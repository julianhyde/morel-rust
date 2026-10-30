// Licensed to Julian Hyde under one or more contributor license
// agreements.  See the NOTICE file distributed with this work
// for additional information regarding copyright ownership.
// Julian Hyde licenses this file to you under the Apache
// License, Version 2.0 (the "License"); you may not use this
// file except in compliance with the License.  You may obtain a
// copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied.  See the License for the specific
// language governing permissions and limitations under the
// License.

//! Synthesises generator expressions from `where` conjuncts.
//! Phase 1 of predicate inversion.
//!
//! Mirrors morel-java's `compile.Generators::maybeGenerator`
//! with the leaf strategies — point, elem, range. Later phases
//! add string-prefix, function inlining, exists, case, and
//! constructor patterns.

use crate::compile::core::{
    Binding, Expr, Match, Pat, PatField, Step, StepEnv, StepKind, fresh_name,
};
use crate::compile::expander::{
    DatatypeMap, FnEnv, and_all, build_iterate_ast, contains_self_call, expr_eq,
};
use crate::compile::free_finder::free_names_in;
use crate::compile::generator::{Cache, Cardinality, Generator};
use crate::compile::library::{BuiltInFunction, lookup_struct_field};
use crate::compile::postfix::peel_type;
use crate::compile::rel_lowerer;
use crate::compile::replacer::substitute;
use crate::compile::span::Span;
use crate::compile::type_env::Id;
use crate::compile::types::{
    Label, PrimitiveType, Type, instantiate, record_fields,
};
use crate::eval::char::Char;
use crate::eval::val::Val;
use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;
use strum::IntoEnumIterator;

/// Tries to derive a generator for `pat` from the conjuncts in
/// `constraints`. Returns `true` if a generator was added to the
/// cache.
///
/// `ordered` is `true` when the surrounding `from` is producing a
/// list (vs a bag). It influences which `tabulate` built-in we use
/// for ranges (`List.tabulate` vs `Bag.tabulate`).
pub fn maybe_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> bool {
    let empty: BTreeSet<String> = BTreeSet::new();
    maybe_generator_with_scope(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
        &empty,
        &empty,
        &empty,
    )
}

#[allow(clippy::too_many_arguments)]
pub fn maybe_generator_with_scope(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
    unbounded_siblings: &BTreeSet<String>,
    ungrounded: &BTreeSet<String>,
) -> bool {
    // The structural tests below ask what kind of type this is, and an
    // alias is whatever it abbreviates. The pattern's own type is kept
    // for the values that are built, so that a scan over a named type
    // gives back that name.
    let peeled = peel_type(pat_type);

    // Phase A: classify each conjunct.
    let mut elem_match: Option<&Expr> = None;
    let mut elem_collection: Option<&Expr> = None;
    let mut elem_subject: Option<&Expr> = None;

    let mut point_match: Option<&Expr> = None;
    let mut point_value: Option<&Expr> = None;

    let mut has_bounds = false;

    let mut prefix_match: Option<&Expr> = None;
    let mut prefix_string: Option<&Expr> = None;

    for c in constraints {
        if elem_match.is_none()
            && let Some((lhs, rhs)) =
                call2_args(c, &[BuiltInFunction::ListElem])
            && (references(lhs, pat_name)
                || binds_ungrounded_names(lhs, pat_name, ungrounded)
                || (tests_rebound()
                    && tuple_mentions(lhs, pat_name)
                    && !free_names_in(lhs)
                        .iter()
                        .any(|n| n != pat_name && ungrounded.contains(n))))
        {
            elem_match = Some(c);
            elem_collection = Some(rhs);
            elem_subject = Some(lhs);
        }
        if point_match.is_none()
            && let Some((lhs, rhs)) = call2_args(
                c,
                &[
                    BuiltInFunction::IntEq,
                    BuiltInFunction::RealEq,
                    BuiltInFunction::StringEq,
                    BuiltInFunction::CharEq,
                    BuiltInFunction::BoolEq,
                    BuiltInFunction::GEq,
                ],
            )
        {
            // The other side of the equality is the single value the
            // pattern takes, so it must not be the pattern itself: `x
            // = x` says nothing, and generating "the value of x" from
            // an x that nothing has bound yet yields garbage.
            if references(lhs, pat_name) && !references(rhs, pat_name) {
                point_match = Some(c);
                point_value = Some(rhs);
            } else if references(rhs, pat_name) && !references(lhs, pat_name) {
                // Reverse direction: `value = pat`. Reject if the
                // value references another unbounded sibling — the
                // sibling will pick up this constraint via the
                // forward direction (`sibling = value`), and using
                // both directions would create a cycle that
                // topo_order can't resolve.
                // A sibling that has a generator already is not
                // part of a cycle: the value can be read once the
                // sibling's scan has produced it, which is what a
                // dependent join is for.
                let lhs_free = free_names_in(lhs);
                let cycles = lhs_free.iter().any(|n| {
                    n != pat_name
                        && unbounded_siblings.contains(n)
                        && cache.best(n).is_none()
                });
                if !cycles {
                    point_match = Some(c);
                    point_value = Some(lhs);
                }
            }
        }
        if !has_bounds && is_bound_constraint(c, pat_name) {
            has_bounds = true;
        }
        if prefix_match.is_none()
            && matches!(peeled, Type::Primitive(PrimitiveType::String))
            && let Some(s) = is_string_prefix_call(c, pat_name)
        {
            prefix_match = Some(c);
            prefix_string = Some(s);
        }
    }

    // Phase B: synthesise leaf generators in priority order.
    if let (Some(c), Some(coll), Some(subject)) =
        (elem_match, elem_collection, elem_subject)
    {
        // `(y, x) elem coll` says where the pair goes, and so binds
        // both names at once. One generator per name would pair
        // every `y` with every `x`, which is not what it said, so
        // the generator binds the tuple and is registered for each
        // name in it.
        if binds_ungrounded_names(subject, pat_name, ungrounded)
            && let Some(tuple) = tuple_pat(subject)
        {
            return create_tuple_elem_generator(
                cache, &tuple, pat_name, coll, c,
            );
        }
        // A component that is neither a name nor a literal -- `(#1 r, y)
        // elem edges` -- is scanned under a fresh name that a condition
        // equates to it, as morel-go's `patForExp` does; only a caller
        // that tests what a pattern rebinds can read it so.
        if tests_rebound() && tuple_mentions(subject, pat_name) {
            let mut conds = Vec::new();
            if let Some(tuple) = pat_for_exp_conds(subject, &mut conds)
                && only_ungrounded(&pat_names(&tuple), pat_name, ungrounded)
                && create_tuple_elem_generator(cache, &tuple, pat_name, coll, c)
            {
                if !conds.is_empty()
                    && let Some(mut g) = cache.best(pat_name).cloned()
                {
                    g.extra_filter = Some(and_all(conds));
                    cache.add(pat_name.to_string(), g);
                }
                return true;
            }
        }
        return create_collection_generator(cache, pat, pat_name, coll, c);
    }
    if maybe_record_elem_projection(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        outer_scope,
    ) {
        return true;
    }
    if let (Some(c), Some(value)) = (point_match, point_value) {
        return create_point_generator(cache, pat, pat_name, value, c);
    }
    if has_bounds && matches!(peeled, Type::Primitive(PrimitiveType::Int)) {
        return create_range_generator(
            ungrounded,
            cache,
            pat,
            pat_name,
            ordered,
            constraints,
            unbounded_siblings,
        );
    }
    if matches!(peeled, Type::Tuple(_))
        && create_tuple_range_generator(
            cache,
            pat,
            pat_name,
            pat_type,
            ordered,
            constraints,
        )
    {
        return true;
    }
    if maybe_field_generator(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
    ) {
        return true;
    }
    if let (Some(c), Some(s)) = (prefix_match, prefix_string) {
        return create_string_prefix_generator(
            cache, pat, pat_name, ordered, s, c,
        );
    }
    if maybe_exists(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
        outer_scope,
        unbounded_siblings,
        ungrounded,
    ) {
        return true;
    }
    if tests_rebound() && maybe_rec_fn(cache, pat_name, constraints, fn_env) {
        return true;
    }
    if maybe_function(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
        outer_scope,
        unbounded_siblings,
        ungrounded,
    ) {
        return true;
    }
    if maybe_case(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
        outer_scope,
        unbounded_siblings,
        ungrounded,
    ) {
        return true;
    }
    if maybe_union(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
        outer_scope,
        unbounded_siblings,
        ungrounded,
    ) {
        return true;
    }
    if maybe_case_constructor(
        cache,
        pat,
        pat_name,
        pat_type,
        ordered,
        constraints,
        fn_env,
        datatypes,
    ) {
        return true;
    }
    // Fallback: enumerate all values of the pattern's type, when
    // that type is finite (bool, option of finite, tuple of
    // finite, user datatype with all-nullary constructors).
    // Surrounding `where` conjuncts filter as needed (e.g.
    // `not b` keeps only `false`, `Option.getOpt i` keeps only
    // the tuples whose option/default product is true).
    if let Some(extent) = finite_extent(pat_type, datatypes) {
        return create_finite_extent_generator(cache, pat, pat_name, extent);
    }
    false
}

// ---------------------------------------------------------------------------
// Leaf strategies
// ---------------------------------------------------------------------------

/// Returns whether an expression is a tuple of variables and
/// literals whose variables are distinct, one of which is `name`
/// and every one of which is still looking for a generator.
///
/// A name something else has already bound is not this
/// generator's to bind: binding it here would say where a value
/// the query has already placed must go.
fn binds_ungrounded_names(
    exp: &Expr,
    name: &str,
    ungrounded: &BTreeSet<String>,
) -> bool {
    let Some(pat) = tuple_pat(exp) else {
        return false;
    };
    let names = pat_names(&pat);
    names.iter().any(|n| n == name)
        && (tests_rebound() || names.iter().all(|n| ungrounded.contains(n)))
}

/// Whether `name` is the one name among `names` that is still to be
/// grounded; the others are bound already, and a caller that tests what
/// a pattern rebinds keeps the rows that agree with them.
fn only_ungrounded(
    names: &[String],
    name: &str,
    ungrounded: &BTreeSet<String>,
) -> bool {
    names.iter().all(|n| n == name || !ungrounded.contains(n))
}

thread_local! {
    /// Whether the caller tests a name that a generator's pattern binds
    /// and something outside it has bound already, as the tree grounder
    /// does: then `(a, y) elem pairs` grounds `y` under the pattern
    /// `(a, y)`, as morel-go's `collectionGenerator` does, and the caller
    /// keeps the rows whose `a` is the `a` in scope. The step list scans
    /// a generator's pattern as it stands, which would rebind `a`.
    static TESTS_REBOUND: Cell<bool> = const { Cell::new(false) };
}

fn tests_rebound() -> bool {
    TESTS_REBOUND.with(Cell::get)
}

/// Runs `f` as a caller that tests what a generator's pattern rebinds;
/// see [`TESTS_REBOUND`].
pub(crate) fn testing_rebound<T>(f: impl FnOnce() -> T) -> T {
    let previous = TESTS_REBOUND.with(|c| c.replace(true));
    let out = f();
    TESTS_REBOUND.with(|c| c.set(previous));
    out
}

/// The pattern that a tuple scans under, or `None` where the
/// expression is not a tuple, or its variables are not distinct.
fn tuple_pat(exp: &Expr) -> Option<Pat> {
    let Expr::Tuple(_, args) = exp else {
        return None;
    };
    if args.len() < 2 {
        return None;
    }
    let pat = pat_for_exp(exp)?;
    let names = pat_names(&pat);
    let distinct: BTreeSet<&String> = names.iter().collect();
    if distinct.len() < names.len() {
        return None;
    }
    Some(pat)
}

/// Converts the element side of a membership conjunct to the
/// pattern its scan binds: a variable to its pattern, a tuple or
/// record to one of converted components, and a literal to a literal
/// pattern, which filters the rows by matching. Anything else is
/// `None`.
fn pat_for_exp(exp: &Expr) -> Option<Pat> {
    match exp {
        // lint: sort until '#}' where '##Expr::'
        Expr::Identifier(t, name) => {
            Some(Pat::Identifier(t.clone(), name.clone()))
        }
        Expr::Literal(t, value)
            if matches!(peel_type(t), Type::Primitive(_)) =>
        {
            Some(Pat::Literal(t.clone(), value.clone()))
        }
        Expr::Tuple(t, args) => {
            let pats: Vec<Pat> =
                args.iter().map(pat_for_exp).collect::<Option<_>>()?;
            // A record is written as a tuple of its fields in slot
            // order, but is matched by a record pattern.
            if let Type::Record(_, labels) = t.as_ref() {
                let fields = labels
                    .keys()
                    .zip(pats)
                    .map(|(label, p)| {
                        PatField::Labeled(label.to_string(), Box::new(p))
                    })
                    .collect();
                return Some(Pat::Record(t.clone(), fields, false));
            }
            Some(Pat::Tuple(t.clone(), pats))
        }
        _ => None,
    }
}

/// Converts the element side of a membership conjunct to a pattern as
/// [pat_for_exp] does, and any other component to a fresh name, adding
/// the condition that equates the name to the component.
fn pat_for_exp_conds(exp: &Expr, conds: &mut Vec<Expr>) -> Option<Pat> {
    match exp {
        Expr::Tuple(t, args) if !matches!(t.as_ref(), Type::Record(..)) => {
            let pats: Vec<Pat> = args
                .iter()
                .map(|a| pat_for_exp_conds(a, conds))
                .collect::<Option<_>>()?;
            Some(Pat::Tuple(t.clone(), pats))
        }
        _ => pat_for_exp(exp).or_else(|| {
            let t = exp.type_();
            let name = fresh_name();
            conds.push(make_eq_for_type(
                &t,
                Expr::Identifier(t.clone(), name.clone()),
                exp.clone(),
            ));
            Some(Pat::Identifier(t, name))
        }),
    }
}

/// The names a pattern binds, in order.
fn pat_names(pat: &Pat) -> Vec<String> {
    let mut names = Vec::new();
    pat.for_each_id_pat(&mut |(_, name): (&Type, &str)| {
        names.push(name.to_string())
    });
    names
}

/// Builds the generator of a tuple of names and literals: the
/// collection the tuple is drawn from, scanned under the tuple,
/// which binds every name in it and whose literals filter the rows.
fn create_tuple_elem_generator(
    cache: &mut Cache,
    tuple: &Pat,
    pat_name: &str,
    collection: &Expr,
    source_constraint: &Expr,
) -> bool {
    let names = pat_names(tuple);
    if !names.iter().any(|n| n == pat_name) {
        return false;
    }
    // The collection has to be of the tuple's own type, or scanning
    // it would bind the names to something else.
    let elem = match collection.type_().as_ref() {
        Type::Bag(e) | Type::List(e) => e.clone(),
        _ => return false,
    };
    if peel_type(&elem) != peel_type(&tuple.type_()) {
        return false;
    }
    let mut free = free_names_in(collection);
    for name in &names {
        free.remove(name);
    }
    let generator = Generator::new(
        tuple.clone(),
        collection.clone(),
        Cardinality::Finite,
        free,
        // A collection may hold the same tuple twice, and in no
        // particular order; `distinct` and `order` follow the scan.
        false,
        true,
        vec![source_constraint.clone()],
    );
    cache.add(pat_name.to_string(), generator);
    true
}

fn create_collection_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    collection: &Expr,
    source_constraint: &Expr,
) -> bool {
    let mut free = free_names_in(collection);
    free.remove(pat_name);
    let generator = Generator::new(
        pat.clone(),
        collection.clone(),
        Cardinality::Finite,
        free,
        // A collection may hold the same value twice, and in no
        // particular order; `distinct` and `order` follow the scan.
        false,
        true, // sealed: the elem-conjunct is fully encoded by the scan
        vec![source_constraint.clone()],
    );
    cache.add(pat_name.to_string(), generator);
    true
}

/// Returns whether an expression names a value a generator can be built
/// for: the pattern itself (`None`), or a selection of one of its
/// fields (`Some(slot)`).
///
/// Narrower than a general occurrence test, which is true of any
/// expression the pattern appears in.
fn pat_or_field_slot(expr: &Expr, pat_name: &str) -> Option<Option<usize>> {
    if references(expr, pat_name) {
        return Some(None);
    }
    if let Expr::Apply(_, f, a, _) = expr
        && let Expr::RecordSelector(_, slot) = f.as_ref()
        && references(a, pat_name)
    {
        return Some(Some(*slot));
    }
    None
}

/// If `c` is `Range.contains range value`, returns the range and the
/// value it constrains.
fn as_range_contains(c: &Expr) -> Option<(&Expr, &Expr)> {
    let Expr::Apply(_, outer_fn, value, _) = c else {
        return None;
    };
    let Expr::Apply(_, contains_fn, range, _) = outer_fn.as_ref() else {
        return None;
    };
    if as_builtin_fn(contains_fn) != Some(BuiltInFunction::RangeContains) {
        return None;
    }
    Some((range, value))
}

/// Grounds a record or tuple variable by grounding each of its fields.
///
/// A record is not itself a value any constraint generates, so
/// `p.i elem [0,1] andalso p.j elem [2,3]` grounds nothing on its own.
/// Each field is generated by the constraint that selects it, though,
/// so a collection is collected per field and they are joined into one
/// generator for the record. Every field must be covered: one left free
/// has values the constraints do not enumerate.
///
/// A tuple is grounded the same way, by its components.
///
/// Mirrors morel-java's `Cache.deriveFieldGenerators`, which reaches
/// the same answer by recording a fresh pattern for each field access
/// as it classifies the constraints.
fn maybe_field_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
) -> bool {
    // An alias is whatever it abbreviates; the pattern's own type is
    // what the record is built at, so a scan over a named type gives
    // back that name.
    let peeled = peel_type(pat_type);
    if !matches!(peeled, Type::Record(..) | Type::Tuple(_)) {
        return false;
    }
    let fields = record_fields(peeled);
    if fields.is_empty() {
        return false;
    }

    // One collection per field, in slot order. A field is covered by an
    // `elem` over a collection, or by a finite range, which is the same
    // thing once enumerated. Two constraints on one field keep the
    // first, and an `elem` takes priority over a range.
    let mut colls: Vec<Option<Expr>> = vec![None; fields.len()];
    for c in constraints {
        if let Some((lhs, rhs)) = call2_args(c, &[BuiltInFunction::ListElem])
            && let Some(Some(slot)) = pat_or_field_slot(lhs, pat_name)
            && slot < colls.len()
            && colls[slot].is_none()
        {
            colls[slot] = Some(rhs.clone());
        }
    }
    for c in constraints {
        // `x elem [a..b]` is rewritten to `Range.contains (a..b) x`.
        let Some((range, value)) = as_range_contains(c) else {
            continue;
        };
        let Some(Some(slot)) = pat_or_field_slot(value, pat_name) else {
            continue;
        };
        // Discreteness is asked of the value being generated: a record
        // is not discrete, but its fields may be.
        if !matches!(
            value.type_().as_ref(),
            Type::Primitive(PrimitiveType::Int)
        ) || slot >= colls.len()
            || colls[slot].is_some()
        {
            continue;
        }
        let bounds = range_bounds(range);
        // Only a finite range enumerates; one open at either end does
        // not, and the field stays uncovered.
        if let [(true, lower), (false, upper)] = bounds.as_slice() {
            colls[slot] = Some(int_range_collection(lower, upper, ordered));
        }
    }
    if colls.iter().any(Option::is_none) {
        return false;
    }

    // Join the fields' collections, and build the record from them.
    let base_t = Rc::new(pat_type.clone());
    let mut steps: Vec<Step> = Vec::new();
    let mut bindings: Vec<Binding> = Vec::new();
    let mut ids: Vec<Expr> = Vec::new();
    for ((label, field_t), coll) in fields.iter().zip(colls) {
        // A name the user cannot have written, so that a field never
        // captures a variable that is in scope.
        let name = format!("${}${}", pat_name, label);
        bindings.push(Binding::new(Id::new(&name, 0), field_t.clone()));
        steps.push(Step::new(
            StepKind::Scan(
                Box::new(Pat::Identifier(field_t.clone(), name.clone())),
                Box::new(coll.expect("every field is covered")),
                None,
            ),
            StepEnv::new(bindings.clone(), false, ordered),
        ));
        ids.push(Expr::Identifier(field_t.clone(), name));
    }
    // Build the value at the pattern's own type. A record is a tuple in
    // Core, so deriving the type from the fields would give `int * int`
    // where the pattern is `{i:int, j:int}`.
    steps.push(Step::new(
        StepKind::Yield(Box::new(Expr::Tuple(base_t.clone(), ids))),
        StepEnv::new(
            vec![Binding::new(Id::new(pat_name, 0), base_t.clone())],
            true,
            ordered,
        ),
    ));
    let coll_t = if ordered {
        Rc::new(Type::List(base_t.clone()))
    } else {
        Rc::new(Type::Bag(base_t.clone()))
    };
    let exp = Expr::From(coll_t, steps);

    let mut free = free_names_in(&exp);
    free.remove(pat_name);
    let generator = Generator::new(
        pat.clone(),
        exp,
        Cardinality::Finite,
        free,
        // A field's collection may hold a value twice, so the join may
        // too; `distinct` follows the scan.
        false,
        // The constraints stay in the `where`: each covers one field,
        // and none is fully discharged by the join.
        true,
        vec![],
    );
    cache.add(pat_name.to_string(), generator);
    true
}

fn create_point_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    value: &Expr,
    source_constraint: &Expr,
) -> bool {
    let elem_t = value.type_();
    let list_t = Rc::new(Type::List(Rc::new((*elem_t).clone())));
    let exp = Expr::List(list_t, vec![value.clone()]);
    let mut free = free_names_in(value);
    free.remove(pat_name);
    let generator = Generator::new(
        pat.clone(),
        exp,
        Cardinality::Single,
        free,
        true,
        true,
        vec![source_constraint.clone()],
    );
    cache.add(pat_name.to_string(), generator);
    true
}

fn create_range_generator(
    ungrounded: &BTreeSet<String>,
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    ordered: bool,
    constraints: &[Expr],
    unbounded_siblings: &BTreeSet<String>,
) -> bool {
    let lower = match lower_bound(pat_name, constraints, ungrounded) {
        Some(l) => l,
        None => return false,
    };
    let upper = match upper_bound(pat_name, constraints, ungrounded) {
        Some(u) => u,
        None => return false,
    };

    // Provenance: every bound constraint involving the pattern, except
    // those that also reference another unbounded sibling (e.g. `x < y`).
    // Such cross-variable constraints are not fully expressed by this
    // pattern's finite range — the constant-valued bounds that ground it
    // come from elsewhere (an input literal or an FBBT-deduced bound) —
    // so they must remain in the `where` as post-generation filters.
    let provenance: Vec<Expr> = constraints
        .iter()
        .filter(|c| {
            is_bound_constraint(c, pat_name)
                && !references_other_sibling(c, pat_name, unbounded_siblings)
        })
        .cloned()
        .collect();

    let exp = int_range_collection(&lower, &upper, ordered);

    let mut free = free_names_in(&lower.bound);
    free.append(&mut free_names_in(&upper.bound));
    free.remove(pat_name);

    let generator = Generator::new(
        pat.clone(),
        exp,
        Cardinality::Finite,
        free,
        true,
        true,
        provenance,
    );
    cache.add(pat_name.to_string(), generator);
    true
}

/// Returns the collection of the integers between two bounds:
/// `List.tabulate (upper - lower + 1, fn k => lower + k)`, or the
/// `Bag` equivalent when the surrounding query is unordered.
fn int_range_collection(lower: &Bound, upper: &Bound, ordered: bool) -> Expr {
    let int_t = Rc::new(Type::Primitive(PrimitiveType::Int));
    // The strictness of the two bounds names the range constructor, so each
    // endpoint is written as it was deduced rather than nudged by one.
    let ctor = match (lower.strict, upper.strict) {
        (false, false) => BuiltInFunction::RangeClosed,
        (false, true) => BuiltInFunction::RangeClosedOpen,
        (true, false) => BuiltInFunction::RangeOpenClosed,
        (true, true) => BuiltInFunction::RangeOpen,
    };
    let range_t = Rc::new(Type::Data("range".to_string(), vec![int_t.clone()]));
    let pair_t = Rc::new(Type::Tuple(vec![int_t.clone(), int_t.clone()]));
    let ctor_app = Expr::Apply(
        range_t.clone(),
        Box::new(Expr::Literal(
            Rc::new(Type::Fn(pair_t.clone(), range_t.clone())),
            Val::Fn(ctor),
        )),
        Box::new(Expr::Tuple(
            pair_t,
            vec![lower.bound.clone(), upper.bound.clone()],
        )),
        Span::new(""),
    );
    let ranges_t = Rc::new(Type::List(range_t));
    let ranges = Expr::List(ranges_t.clone(), vec![ctor_app]);
    let list_t = Rc::new(Type::List(int_t.clone()));
    let flatten = Expr::Apply(
        list_t.clone(),
        Box::new(Expr::Literal(
            Rc::new(Type::Fn(ranges_t, list_t.clone())),
            Val::Fn(BuiltInFunction::RangeFlatten),
        )),
        Box::new(ranges),
        Span::new(""),
    );
    if ordered {
        return flatten;
    }
    // `Range.flatten` gives a list; an unordered scan takes a bag of it.
    let bag_t = Rc::new(Type::Bag(int_t));
    Expr::Apply(
        bag_t.clone(),
        Box::new(Expr::Literal(
            Rc::new(Type::Fn(list_t, bag_t.clone())),
            Val::Fn(BuiltInFunction::BagFromList),
        )),
        Box::new(flatten),
        Span::new(""),
    )
}

/// Recognises a constraint of the form
///   `t >= (l1, …, lk) andalso t <= (u1, …, uk)`
/// (or just `t = (v1, …, vk)`) where every component is a
/// literal and the tuple type is enumerable, and emits a
/// `Bag.fromList`/`List` of the lex-ordered values between
/// `lo` and `hi` inclusive. Required for queries like
///
///   from t where t >= (false, 3) andalso t <= (false, 5)
///
/// where the range generator can't operate on `int` alone.
///
/// Returns `true` if a generator was added.
fn create_tuple_range_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
) -> bool {
    // Separate component types. An alias is whatever it abbreviates.
    let component_types: Vec<Type> = match peel_type(pat_type) {
        Type::Tuple(ts) => ts.iter().map(|t| (**t).clone()).collect(),
        _ => return false,
    };
    // Collect lo and hi tuples from the constraints. Look for
    // `t >= lit_tuple` (or `t > …`), `t <= lit_tuple` (or `t < …`).
    let mut lo: Option<(Vec<Val>, bool)> = None; // (vals, strict)
    let mut hi: Option<(Vec<Val>, bool)> = None;
    let mut bound_constraints: Vec<Expr> = Vec::new();
    for c in constraints {
        let Some((lhs, rhs, op)) = call2_args_op(c, &[BuiltInFunction::GEq])
        else {
            continue;
        };
        // We only handle the polymorphic comparison op `GEq` here
        // (which dispatches by type at runtime). Either side
        // could be the literal.
        let _ = op;
        // The comparison-op literal tells us whether it's >, <,
        // >=, or <=. We don't have that info from `GEq` alone, so
        // skip — comparisons on tuples in our codebase use
        // primitive ops only.
        let _ = (lhs, rhs);
    }
    // Comparison-by-value-on-tuples isn't supported by our
    // codebase via `GEq`; tuples compare via specific `<`, `>`,
    // `<=`, `>=` builtins. Look for those instead.
    for c in constraints {
        let result = call2_args_op(
            c,
            &[
                BuiltInFunction::IntGe,
                BuiltInFunction::IntGt,
                BuiltInFunction::IntLe,
                BuiltInFunction::IntLt,
                BuiltInFunction::IntEq,
                BuiltInFunction::GEq,
                BuiltInFunction::GGe,
                BuiltInFunction::GGt,
                BuiltInFunction::GLe,
                BuiltInFunction::GLt,
            ],
        );
        let Some((lhs, rhs, op)) = result else {
            continue;
        };
        // The pattern side is `Identifier(_, pat_name)`; the
        // other side must be a literal tuple.
        let (lit_side, pat_first) = match (lhs, rhs) {
            (Expr::Identifier(_, n), other) if n == pat_name => (other, true),
            (other, Expr::Identifier(_, n)) if n == pat_name => (other, false),
            _ => continue,
        };
        let Expr::Tuple(_, items) = lit_side else {
            continue;
        };
        let Some(vals) = items
            .iter()
            .map(|e| match e {
                Expr::Literal(_, v) => Some(v.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        // Map the operator to a (lo|hi, strict) classification.
        let (is_lo, strict) = match (op, pat_first) {
            (BuiltInFunction::IntGe | BuiltInFunction::GGe, true) => {
                // pat >= lit ⇒ lit is the lower bound.
                (true, false)
            }
            (BuiltInFunction::IntGt | BuiltInFunction::GGt, true) => {
                (true, true)
            }
            (BuiltInFunction::IntLe | BuiltInFunction::GLe, true) => {
                (false, false)
            }
            (BuiltInFunction::IntLt | BuiltInFunction::GLt, true) => {
                (false, true)
            }
            (BuiltInFunction::IntEq | BuiltInFunction::GEq, _) => {
                // pat = lit ⇒ both bounds are lit.
                lo = Some((vals.clone(), false));
                hi = Some((vals.clone(), false));
                bound_constraints.push(c.clone());
                continue;
            }
            (BuiltInFunction::IntGe | BuiltInFunction::GGe, false) => {
                (false, false)
            }
            (BuiltInFunction::IntGt | BuiltInFunction::GGt, false) => {
                (false, true)
            }
            (BuiltInFunction::IntLe | BuiltInFunction::GLe, false) => {
                (true, false)
            }
            (BuiltInFunction::IntLt | BuiltInFunction::GLt, false) => {
                (true, true)
            }
            _ => continue,
        };
        if is_lo {
            lo = Some((vals, strict));
        } else {
            hi = Some((vals, strict));
        }
        bound_constraints.push(c.clone());
    }
    let Some((lo_vals, lo_strict)) = lo else {
        return false;
    };
    let Some((hi_vals, hi_strict)) = hi else {
        return false;
    };
    if lo_vals.len() != component_types.len()
        || hi_vals.len() != component_types.len()
    {
        return false;
    }
    // Bump strict bounds to inclusive by stepping the int-most
    // component (we only know how to step ints). For now reject
    // strict bounds on non-int trailing component.
    let lo_inclusive = if lo_strict {
        match step_tuple(&lo_vals, &component_types, true) {
            Some(v) => v,
            None => return false,
        }
    } else {
        lo_vals
    };
    let hi_inclusive = if hi_strict {
        match step_tuple(&hi_vals, &component_types, false) {
            Some(v) => v,
            None => return false,
        }
    } else {
        hi_vals
    };

    let Some(values) =
        enumerate_tuple_range(&lo_inclusive, &hi_inclusive, &component_types)
    else {
        return false;
    };

    // Build a list literal of the enumerated tuples.
    let elem_t: Rc<Type> = Rc::new(pat_type.clone());
    let list_t = Rc::new(Type::List(elem_t.clone()));
    let items: Vec<Expr> = values
        .into_iter()
        .map(|tv| {
            Expr::Tuple(
                elem_t.clone(),
                tv.into_iter()
                    .zip(component_types.iter())
                    .map(|(v, t)| Expr::Literal(Rc::new(t.clone()), v))
                    .collect(),
            )
        })
        .collect();
    let exp = Expr::List(list_t, items);
    let _ = ordered;

    let generator = Generator::new(
        pat.clone(),
        exp,
        Cardinality::Finite,
        BTreeSet::new(),
        true,
        true,
        bound_constraints,
    );
    cache.add(pat_name.to_string(), generator);
    true
}

/// Steps a tuple value by ±1 at its trailing int component
/// (for converting strict bounds to inclusive). Returns `None`
/// if the trailing component isn't int.
fn step_tuple(
    vals: &[Val],
    types: &[Type],
    increase: bool,
) -> Option<Vec<Val>> {
    if vals.is_empty() {
        return None;
    }
    let last_t = types.last()?;
    if !matches!(last_t, Type::Primitive(PrimitiveType::Int)) {
        return None;
    }
    let Val::Int(n) = vals.last()? else {
        return None;
    };
    let mut out = vals.to_vec();
    *out.last_mut().unwrap() = Val::Int(if increase { n + 1 } else { n - 1 });
    Some(out)
}

/// Lex-enumerates the tuples `[lo, …, hi]` (inclusive). Returns
/// `None` if any "middle" component would require enumerating
/// values of a non-finite type (e.g. `int` between two bools).
fn enumerate_tuple_range(
    lo: &[Val],
    hi: &[Val],
    types: &[Type],
) -> Option<Vec<Vec<Val>>> {
    if lo.is_empty() {
        return Some(vec![vec![]]);
    }
    if compare_tuple(lo, hi) > 0 {
        return Some(vec![]);
    }
    let lo_v = &lo[0];
    let hi_v = &hi[0];
    let t = &types[0];
    let mut out: Vec<Vec<Val>> = Vec::new();
    for v in iter_values_inclusive(lo_v, hi_v, t)? {
        let lo_eq = compare_val(&v, lo_v) == 0;
        let hi_eq = compare_val(&v, hi_v) == 0;
        let sub_lo: Vec<Val> = if lo_eq {
            lo[1..].to_vec()
        } else {
            type_mins(&types[1..])?
        };
        let sub_hi: Vec<Val> = if hi_eq {
            hi[1..].to_vec()
        } else {
            type_maxes(&types[1..])?
        };
        let subs = enumerate_tuple_range(&sub_lo, &sub_hi, &types[1..])?;
        for sub in subs {
            let mut full = vec![v.clone()];
            full.extend(sub);
            out.push(full);
        }
    }
    Some(out)
}

/// Iterates [lo, hi] inclusive, in lex order. Returns `None` if
/// the type isn't enumerable (e.g. `string`).
fn iter_values_inclusive(lo: &Val, hi: &Val, t: &Type) -> Option<Vec<Val>> {
    match t {
        Type::Primitive(PrimitiveType::Int) => {
            let Val::Int(a) = lo else { return None };
            let Val::Int(b) = hi else { return None };
            Some((*a..=*b).map(Val::Int).collect())
        }
        Type::Primitive(PrimitiveType::Bool) => {
            let Val::Bool(a) = lo else { return None };
            let Val::Bool(b) = hi else { return None };
            // Order: false < true.
            let mut out = Vec::new();
            for v in [false, true] {
                if (!a || v) && (*b || !v) {
                    out.push(Val::Bool(v));
                }
            }
            Some(out)
        }
        _ => None,
    }
}

/// Min values of a tuple of types (the lex-smallest tuple).
/// Returns `None` if any type lacks a known minimum.
fn type_mins(types: &[Type]) -> Option<Vec<Val>> {
    types.iter().map(type_min).collect()
}

fn type_min(t: &Type) -> Option<Val> {
    match t {
        Type::Primitive(PrimitiveType::Bool) => Some(Val::Bool(false)),
        // Ints have no smallest value we want to enumerate;
        // disallow.
        _ => None,
    }
}

/// Max values of a tuple of types.
fn type_maxes(types: &[Type]) -> Option<Vec<Val>> {
    types.iter().map(type_max).collect()
}

fn type_max(t: &Type) -> Option<Val> {
    match t {
        Type::Primitive(PrimitiveType::Bool) => Some(Val::Bool(true)),
        _ => None,
    }
}

/// Lexicographic comparison of two tuples of values.
fn compare_tuple(a: &[Val], b: &[Val]) -> i32 {
    for (x, y) in a.iter().zip(b.iter()) {
        let c = compare_val(x, y);
        if c != 0 {
            return c;
        }
    }
    a.len() as i32 - b.len() as i32
}

fn compare_val(a: &Val, b: &Val) -> i32 {
    match (a, b) {
        (Val::Int(x), Val::Int(y)) => x.cmp(y) as i32,
        (Val::Bool(x), Val::Bool(y)) => x.cmp(y) as i32,
        _ => 0, // unsupported — caller has already filtered
    }
}

/// Generator of last resort: yield every value of the pattern's
/// type, provided the type is finite. The surrounding `where`
/// clause filters down. Used for `from b where not b` (single
/// bool), `from i where Option.getOpt i` (tuple of bool option *
/// bool), etc.
fn create_finite_extent_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    extent: Expr,
) -> bool {
    let generator = Generator::new(
        pat.clone(),
        extent,
        Cardinality::Finite,
        BTreeSet::new(),
        true,
        false, // unsealed: doesn't subsume any specific predicate
        Vec::new(),
    );
    cache.add(pat_name.to_string(), generator);
    true
}

/// Returns a Core list expression containing every value of `t`,
/// or `None` if `t` is infinite (int, real, string, …) or
/// references a feature this builder doesn't yet handle (user
/// datatype, list, fn, …). Built-in types covered: `bool`,
/// `'a option` for finite `'a`, tuples of finite components, and
/// user datatypes whose constructors are all nullary.
pub(crate) fn finite_extent(t: &Type, datatypes: &DatatypeMap) -> Option<Expr> {
    // A datatype named in an annotation arrives as an alias for
    // itself -- `from x: color` gives `Alias("color", Data("color",
    // []))` -- so peel before matching.
    match peel_type(t) {
        // lint: sort until '#}' where '#Type::'
        Type::Data(name, args) => {
            let constructors = datatypes.constructors.get(name)?;
            datatype_extent_list(t, constructors, args, datatypes)
        }
        Type::Primitive(PrimitiveType::Bool) => Some(bool_extent_list()),
        Type::Primitive(PrimitiveType::Char) => Some(char_extent_list()),
        Type::Primitive(PrimitiveType::Unit) => Some(unit_extent_list()),
        Type::Record(false, fields) => {
            let mut extents = Vec::with_capacity(fields.len());
            for ft in fields.values() {
                extents.push(finite_extent(ft, datatypes)?);
            }
            Some(record_extent_cartesian(t, fields.keys().count(), extents))
        }
        Type::Tuple(types) => {
            let mut extents = Vec::with_capacity(types.len());
            for ti in types {
                extents.push(finite_extent(ti, datatypes)?);
            }
            Some(tuple_extent_cartesian(types, extents))
        }
        // #}
        _ => None,
    }
}

/// Produces a list-expression of every value of the given datatype:
/// each nullary constructor, and each value of the argument type of
/// every constructor that takes one. `data_t` is the datatype's
/// `Type` and `constructors` is the constructor list in declaration
/// order. Returns `None` if any constructor's argument type is
/// unknown or is not itself finite.
fn datatype_extent_list(
    data_t: &Type,
    constructors: &[String],
    args: &[Rc<Type>],
    datatypes: &DatatypeMap,
) -> Option<Expr> {
    let data_t_box: Rc<Type> = Rc::new(data_t.clone());
    let list_t = Rc::new(Type::List(data_t_box.clone()));
    let mut elems: Vec<Expr> = Vec::with_capacity(constructors.len());
    for cname in constructors {
        match constructor_arg_type(cname, args, datatypes) {
            // A nullary constructor is a value in itself. It is a
            // global `CoreExpr::Identifier` after resolution — that's
            // how the user-typed `BLUE` reaches Core — carrying the
            // datatype's `Type::Data` directly.
            None => {
                elems.push(Expr::Identifier(data_t_box.clone(), cname.clone()))
            }
            // A constructor that takes an argument contributes one
            // value per value of that argument, so the argument type
            // must be finite too.
            Some(arg_t) => {
                let arg_extent = finite_extent(&arg_t, datatypes)?;
                let Expr::List(_, arg_elems) = arg_extent else {
                    return None;
                };
                let con_t =
                    Rc::new(Type::Fn(Rc::new(arg_t), data_t_box.clone()));
                for v in arg_elems {
                    elems.push(Expr::Apply(
                        data_t_box.clone(),
                        Box::new(Expr::Identifier(
                            con_t.clone(),
                            cname.clone(),
                        )),
                        Box::new(v),
                        Span::new(""),
                    ));
                }
            }
        }
    }
    Some(Expr::List(list_t, elems))
}

/// The type of the argument that constructor `cname` takes, with the
/// datatype's type variables replaced by the type arguments `args` at
/// this use; `None` if it is nullary.
///
/// A user datatype records its constructors' argument types as
/// declared. A built-in one -- `option`, `descending`, `either` --
/// does not, but each of its constructors is a built-in function
/// whose declared type says the same thing: `DESC` is `forall 1 'a ->
/// 'a descending`, so its argument type is `'a`.
fn constructor_arg_type(
    cname: &str,
    args: &[Rc<Type>],
    datatypes: &DatatypeMap,
) -> Option<Type> {
    let declared = if let Some(t) = datatypes.arg_types.get(cname) {
        t.clone()
    } else {
        let f = BuiltInFunction::iter().find(|f| f.name() == cname)?;
        // A nullary built-in constructor, such as `NONE`, has no
        // function type and so takes no argument.
        let f_type = f.get_type();
        let Type::Fn(arg, _) = peel_type(&f_type) else {
            return None;
        };
        (**arg).clone()
    };
    Some(instantiate(&declared, args))
}

/// Produces a list-expression of the one `unit` value.
fn unit_extent_list() -> Expr {
    let unit_t = Rc::new(Type::Primitive(PrimitiveType::Unit));
    let list_t = Rc::new(Type::List(unit_t.clone()));
    Expr::List(list_t, vec![Expr::Literal(unit_t, Val::Unit)])
}

/// Produces a list-expression of every `char`, in code-point order.
fn char_extent_list() -> Expr {
    let char_t = Rc::new(Type::Primitive(PrimitiveType::Char));
    let list_t = Rc::new(Type::List(char_t.clone()));
    let elems: Vec<Expr> = (0..=Char::MAX_ORD as u32)
        .filter_map(char::from_u32)
        .map(|c| Expr::Literal(char_t.clone(), Val::Char(c)))
        .collect();
    Expr::List(list_t, elems)
}

/// Produces a list-expression of every value of a record type: the
/// cartesian product of its fields' extents, in field order (which is
/// the order a record type keeps them in).
fn record_extent_cartesian(
    record_t: &Type,
    field_count: usize,
    extents: Vec<Expr>,
) -> Expr {
    debug_assert_eq!(field_count, extents.len());
    let record_t_box = Rc::new(record_t.clone());
    let list_t = Rc::new(Type::List(record_t_box.clone()));
    let value_lists: Vec<Vec<Expr>> = extents
        .into_iter()
        .map(|e| match e {
            Expr::List(_, vs) => vs,
            _ => Vec::new(),
        })
        .collect();
    // A record value is a tuple of its field values, in field order.
    let elems: Vec<Expr> = cartesian_product(&value_lists)
        .into_iter()
        .map(|values| Expr::Tuple(record_t_box.clone(), values))
        .collect();
    Expr::List(list_t, elems)
}

fn bool_extent_list() -> Expr {
    let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let list_t = Rc::new(Type::List(bool_t.clone()));
    // `false` first, `true` second — matches morel-java's
    // ordering for tuple enumeration over bool components, and
    // also matches `compare` semantics (false < true).
    Expr::List(
        list_t,
        vec![
            Expr::Literal(bool_t.clone(), Val::Bool(false)),
            Expr::Literal(bool_t, Val::Bool(true)),
        ],
    )
}

fn tuple_extent_cartesian(types: &[Rc<Type>], extents: Vec<Expr>) -> Expr {
    let tuple_t = Rc::new(Type::Tuple(types.to_vec()));
    let list_t = Rc::new(Type::List(tuple_t.clone()));

    // Each `extents[i]` is `Expr::List(_, values_i)`. Compute the
    // cartesian product of the value lists, then build a
    // tuple-list whose entries are the product tuples.
    let value_lists: Vec<Vec<Expr>> = extents
        .into_iter()
        .map(|e| match e {
            Expr::List(_, vs) => vs,
            _ => Vec::new(),
        })
        .collect();

    let products = cartesian_product(&value_lists);
    let elems: Vec<Expr> = products
        .into_iter()
        .map(|values| Expr::Tuple(tuple_t.clone(), values))
        .collect();
    Expr::List(list_t, elems)
}

fn cartesian_product(lists: &[Vec<Expr>]) -> Vec<Vec<Expr>> {
    let mut acc: Vec<Vec<Expr>> = vec![Vec::new()];
    for list in lists {
        let mut next = Vec::with_capacity(acc.len() * list.len());
        for prefix in &acc {
            for v in list {
                let mut row = prefix.clone();
                row.push(v.clone());
                next.push(row);
            }
        }
        acc = next;
    }
    acc
}

/// Inverts `String.isPrefix p s` (where `p` is the pattern, `s` is
/// any string expression) into
///   `Bag.tabulate(String.size s + 1, fn i => String.substring(s, 0, i))`
/// (or `List.tabulate` when the surrounding `from` is ordered).
fn create_string_prefix_generator(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    ordered: bool,
    s: &Expr,
    source_constraint: &Expr,
) -> bool {
    let int_t = Rc::new(Type::Primitive(PrimitiveType::Int));
    let str_t = Rc::new(Type::Primitive(PrimitiveType::String));

    // String.size s
    let size_s = call1(BuiltInFunction::StringSize, s.clone(), int_t.clone());
    // String.size s + 1
    let count = binop_int(BuiltInFunction::IntPlus, size_s, int_lit(1));

    // fn i => String.substring (s, 0, i)
    let i_pat = Pat::Identifier(int_t.clone(), "i".to_string());
    let i_id = Expr::Identifier(int_t.clone(), "i".to_string());
    let triple_t = Rc::new(Type::Tuple(vec![
        Rc::new((*str_t).clone()),
        Rc::new((*int_t).clone()),
        Rc::new((*int_t).clone()),
    ]));
    let triple =
        Expr::Tuple(triple_t.clone(), vec![s.clone(), int_lit(0), i_id]);
    let fn_substr_t = Rc::new(Type::Fn(triple_t.clone(), str_t.clone()));
    let fn_substr_lit =
        Expr::Literal(fn_substr_t, Val::Fn(BuiltInFunction::StringSubstring));
    let body = Expr::Apply(
        str_t.clone(),
        Box::new(fn_substr_lit),
        Box::new(triple),
        Span::new(""),
    );
    let fn_t = Rc::new(Type::Fn(int_t.clone(), str_t.clone()));
    let fn_expr = Expr::Fn(
        fn_t,
        vec![Match {
            pat: i_pat,
            expr: body,
        }],
        Span::new(""),
    );

    let tabulate = if ordered {
        BuiltInFunction::ListTabulate
    } else {
        BuiltInFunction::BagTabulate
    };
    let coll_t = if ordered {
        Rc::new(Type::List(str_t.clone()))
    } else {
        Rc::new(Type::Bag(str_t.clone()))
    };
    let exp = call2(tabulate, count, fn_expr, coll_t);

    let mut free = free_names_in(s);
    free.remove(pat_name);

    let generator = Generator::new(
        pat.clone(),
        exp,
        Cardinality::Finite,
        free,
        true,
        true,
        vec![source_constraint.clone()],
    );
    cache.add(pat_name.to_string(), generator);
    true
}

// ---------------------------------------------------------------------------
// Complex strategies
// ---------------------------------------------------------------------------

/// Recognises a constraint of the form
/// `exists s1 in c1 [, s2 in c2, ...] where pred`
/// (which morel-rust resolves to a `From` whose last step is
/// `StepKind::Exists`). When the inner `where` predicate, combined
/// with the outer constraints, yields a generator for `pat` whose
/// free patterns include any inner scan-pat, we wrap the inner
/// scans around the inner generator and yield `pat` with `distinct`.
///
/// Example: `from p where (exists s in ["abcd","ant"] where
/// String.isPrefix p s)` becomes
/// `from s in ["abcd","ant"]
///   join p in Bag.tabulate(String.size s + 1,
///                          fn i => String.substring(s, 0, i))
///   yield p distinct`.
#[allow(clippy::too_many_arguments)]
/// The steps of a query a constraint tests for existence, whether
/// it is written as a call over the query or as a query whose last
/// step tests for it.
fn exists_steps(c: &Expr) -> Option<Vec<Step>> {
    match c {
        Expr::Apply(_, f, a, _)
            if as_builtin_fn(f)
                == Some(BuiltInFunction::RelationalNonEmpty) =>
        {
            match a.as_ref() {
                Expr::From(_, steps) => Some(steps.clone()),
                _ => rel_lowerer::exists_tree_steps(c),
            }
        }
        Expr::From(_, steps)
            if matches!(
                steps.last().map(|s| &s.kind),
                Some(StepKind::Exists)
            ) =>
        {
            Some(steps[..steps.len() - 1].to_vec())
        }
        // A tree's test, with the binder that hands it the row.
        _ => rel_lowerer::exists_tree_steps(c),
    }
}

fn maybe_exists(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
    unbounded_siblings: &BTreeSet<String>,
    ungrounded: &BTreeSet<String>,
) -> bool {
    use crate::compile::core::{Step, StepEnv, StepKind};

    for (idx, c) in constraints.iter().enumerate() {
        let Some(inner_steps) = exists_steps(c) else {
            continue;
        };
        let mut inner_scans: Vec<Step> = Vec::new();
        let mut inner_conjuncts: Vec<Expr> = Vec::new();
        for s in &inner_steps {
            match &s.kind {
                StepKind::Scan(_, _, _) => inner_scans.push(s.clone()),
                StepKind::Where(cond) => {
                    inner_conjuncts.extend(split_conjuncts(cond));
                }
                _ => {} // skip yields, groups, orders, etc. — Phase 3a is
                        // intentionally narrow.
            }
        }

        // Build the augmented constraint set: outer minus this
        // exists, plus inner conjuncts.
        let mut augmented: Vec<Expr> =
            Vec::with_capacity(constraints.len() - 1 + inner_conjuncts.len());
        for (j, oc) in constraints.iter().enumerate() {
            if j != idx {
                augmented.push(oc.clone());
            }
        }
        let body_conjuncts = inner_conjuncts.clone();
        augmented.extend(inner_conjuncts);

        // Try to derive a generator from the augmented set, into
        // a temporary cache so we can inspect the result before
        // adding to the real cache.
        // A variable the body quantifies over an extent is as ungrounded
        // inside it as the one being grounded: `exists y where (x, y)
        // elem pairs` grounds `x` and `y` together.
        let quantified: BTreeSet<String> = inner_steps
            .iter()
            .filter_map(|s| match &s.kind {
                StepKind::Scan(p, source, _)
                    if matches!(source.as_ref(), Expr::Extent(..)) =>
                {
                    Some(p)
                }
                _ => None,
            })
            .flat_map(|p| {
                let mut names = Vec::new();
                p.for_each_id_pat(&mut |(_, n)| names.push(n.to_string()));
                names
            })
            .collect();
        let siblings: BTreeSet<String> =
            unbounded_siblings.union(&quantified).cloned().collect();
        let ungrounded2: BTreeSet<String> =
            ungrounded.union(&quantified).cloned().collect();
        let mut probe = Cache::new();
        if !maybe_generator_with_scope(
            &mut probe,
            pat,
            pat_name,
            pat_type,
            ordered,
            &augmented,
            fn_env,
            datatypes,
            outer_scope,
            &siblings,
            &ungrounded2,
        ) {
            continue;
        }
        let mut inner_gen = match probe.best(pat_name) {
            Some(g) => g.clone(),
            None => continue,
        };
        // A filter the generator brought with it that reads a variable
        // the body quantifies and the generator does not bind is not one
        // it can test; the `exists`, which stays as a filter over what
        // this grounds, tests it instead, as morel-go's
        // `existsGenerator` does.
        if let Some(filter) = &inner_gen.extra_filter {
            let mut binds: Vec<String> = Vec::new();
            inner_gen
                .pat
                .for_each_id_pat(&mut |(_, n)| binds.push(n.to_string()));
            let reads_quantified = free_names_in(filter)
                .iter()
                .any(|n| quantified.contains(n) && !binds.contains(n));
            if reads_quantified {
                inner_gen.extra_filter = None;
                inner_gen.sealed = false;
            }
        }

        // Find inner scans that bind any of the generator's free
        // patterns. If none, the generator stands on its own and
        // we can just promote it.
        let inner_names: BTreeSet<String> = inner_scans
            .iter()
            .filter_map(|s| match &s.kind {
                StepKind::Scan(p, _, _) => match p.as_ref() {
                    Pat::Identifier(_, n) => Some(n.clone()),
                    _ => None,
                },
                _ => None,
            })
            .collect();
        let needed: Vec<&Step> = inner_scans
            .iter()
            .filter(|s| {
                if let StepKind::Scan(p, _, _) = &s.kind
                    && let Pat::Identifier(_, n) = p.as_ref()
                {
                    inner_gen.free_pats.contains(n)
                } else {
                    false
                }
            })
            .collect();

        // A generator whose pattern binds a quantified variable --
        // `(x, y) elem pairs` -- yields it too, and the variable is the
        // body's, not a name to test; so it is projected away, as
        // morel-go's `existsGenerator` does.
        let mut gen_names: Vec<String> = Vec::new();
        inner_gen
            .pat
            .for_each_id_pat(&mut |(_, n)| gen_names.push(n.to_string()));
        let binds_quantified = gen_names.iter().any(|n| quantified.contains(n));
        if needed.is_empty() && !binds_quantified {
            // The generator doesn't depend on the inner scans;
            // just promote it.
            cache.add(pat_name.to_string(), inner_gen);
            return true;
        }

        // Wrap: build `from <needed-scans> join pat in inner_gen.exp
        //        yield pat distinct`.
        let elem_t = pat.type_();
        let coll_t = if ordered {
            Rc::new(Type::List(elem_t.clone()))
        } else {
            Rc::new(Type::Bag(elem_t.clone()))
        };
        let mut new_steps: Vec<Step> = Vec::new();
        for s in &needed {
            new_steps.push((*s).clone());
        }
        // join pat in inner_gen.exp
        let scan_env = StepEnv::new(
            vec![Binding::new(Id::new(pat_name, 0), elem_t.clone())],
            true,
            ordered,
        );
        new_steps.push(Step::new(
            StepKind::Scan(
                Box::new(inner_gen.pat.clone()),
                Box::new(inner_gen.exp.clone()),
                None,
            ),
            scan_env.clone(),
        ));
        // The body's other filters apply too, as morel-go's
        // `existsGenerator` has them: those the generator did not take
        // and that read nothing but what these scans bind and what is
        // bound outside. A scan here that is still unbounded is bounded
        // by them when this query is grounded in turn.
        let mut scope: Vec<(String, Rc<Type>)> = Vec::new();
        for s in &needed {
            if let StepKind::Scan(p, _, _) = &s.kind {
                p.for_each_id_pat(&mut |(t, n)| {
                    scope.push((n.to_string(), Rc::new(t.clone())))
                });
            }
        }
        inner_gen.pat.for_each_id_pat(&mut |(t, n)| {
            scope.push((n.to_string(), Rc::new(t.clone())))
        });
        let filters: Vec<Expr> = body_conjuncts
            .iter()
            .filter(|c| !inner_gen.provenance.iter().any(|p| expr_eq(p, c)))
            .filter(|c| {
                free_names_in(c).iter().all(|n| {
                    scope.iter().any(|(s, _)| s == n)
                        || (!ungrounded.contains(n)
                            && !unbounded_siblings.contains(n)
                            && !quantified.contains(n))
                })
            })
            .cloned()
            .collect();
        if !filters.is_empty() {
            let env = StepEnv::new(
                scope
                    .iter()
                    .map(|(n, t)| Binding::new(Id::new(n, 0), t.clone()))
                    .collect(),
                false,
                ordered,
            );
            new_steps.push(Step::new(
                StepKind::Where(Box::new(and_all(filters))),
                env,
            ));
        }
        // yield pat
        new_steps.push(Step::new(
            StepKind::Yield(Box::new(Expr::Identifier(
                elem_t.clone(),
                pat_name.to_string(),
            ))),
            scan_env.clone(),
        ));
        // distinct
        new_steps.push(Step::new(StepKind::Distinct, scan_env));

        let exp = Expr::From(coll_t, new_steps);

        let mut free = inner_gen.free_pats.clone();
        for n in &inner_names {
            free.remove(n);
        }
        let provenance = vec![c.clone()];
        let unsealed = Generator::new(
            pat.clone(),
            exp,
            Cardinality::Finite,
            free,
            false, // not unique — distinct handles dedup
            false, // unsealed: composite
            provenance,
        );
        cache.add(pat_name.to_string(), unsealed);
        return true;
    }
    false
}

/// Inverts a call of a recursive function, as morel-go's `maybeRecFn`
/// does. A body of the shape `base orelse (exists ... where f (...)
/// andalso step ...)` is a transitive closure: the base's membership
/// seeds a fixed-point iteration that extends rows through the base
/// relation, and the closure is exact, so the call is subsumed.
///
/// morel-go also grounds any other recursive call by its body's
/// non-recursive branches, with the call kept as a filter over them;
/// here a function's body is grounded only where it is put in place of
/// a call, so the filter could not run, and such a call is left to the
/// step list.
fn maybe_rec_fn(
    cache: &mut Cache,
    pat_name: &str,
    constraints: &[Expr],
    fn_env: &FnEnv,
) -> bool {
    for c in constraints {
        let Expr::Apply(_, f, arg, _) = c else {
            continue;
        };
        let Expr::Identifier(_, name) = f.as_ref() else {
            continue;
        };
        let Some((param, body)) = fn_env.get(name) else {
            continue;
        };
        if !contains_self_call(body, name) {
            continue;
        }
        if let Some(g) =
            try_closure(pat_name, c, arg, param, body, name, fn_env)
        {
            cache.add(pat_name.to_string(), g);
            return true;
        }
    }
    false
}

/// Puts a non-recursive function's body in place of a call of it.
fn inline_predicate(c: &Expr, fn_env: &FnEnv) -> Expr {
    let Expr::Apply(_, f, arg, _) = c else {
        return c.clone();
    };
    let Expr::Identifier(_, name) = f.as_ref() else {
        return c.clone();
    };
    let Some((param, body)) = fn_env.get(name) else {
        return c.clone();
    };
    if contains_self_call(body, name) {
        return c.clone();
    }
    match formal_bindings(param, arg) {
        Some(binds) => substitute(body, &binds),
        None => c.clone(),
    }
}

/// The formal parameters of a function: one name, or a tuple of them.
fn formals_of(param: &Pat) -> Option<Vec<(String, Rc<Type>)>> {
    match param {
        Pat::Identifier(t, n) => Some(vec![(n.clone(), t.clone())]),
        Pat::Tuple(_, args) => args
            .iter()
            .map(|a| match a {
                Pat::Identifier(t, n) => Some((n.clone(), t.clone())),
                _ => None,
            })
            .collect(),
        _ => None,
    }
}

/// Maps a function's formals to a call's argument: component by
/// component for a tuple, by selection for anything else.
fn formal_bindings(param: &Pat, arg: &Expr) -> Option<HashMap<String, Expr>> {
    let formals = formals_of(param)?;
    let mut binds = HashMap::new();
    if let [(f, _)] = formals.as_slice() {
        binds.insert(f.clone(), arg.clone());
        return Some(binds);
    }
    match arg {
        Expr::Tuple(_, args) if args.len() == formals.len() => {
            for ((f, _), a) in formals.iter().zip(args) {
                binds.insert(f.clone(), a.clone());
            }
        }
        Expr::Identifier(..) => {
            for (i, (f, _)) in formals.iter().enumerate() {
                binds.insert(f.clone(), rel_lowerer::field_at(arg, i));
            }
        }
        _ => return None,
    }
    Some(binds)
}

/// Inverts a call of a transitive closure, `f (x, y) = base (x, y)
/// orelse (exists z where f (x, z) andalso step (z, y))`, whose base is a
/// membership over the formals: the base's collection seeds
/// `Relational.iterate`, which extends each row through it, as morel-go's
/// `tryClosure` does. The call must apply the function to the variable
/// itself, or to a tuple of variables and literals.
fn try_closure(
    pat_name: &str,
    call: &Expr,
    arg: &Expr,
    param: &Pat,
    body: &Expr,
    name: &str,
    fn_env: &FnEnv,
) -> Option<Generator> {
    // The formals are a pair of names, or one name of a pair type.
    let formals = formals_of(param)?;
    let (names, x_t, y_t): (Vec<String>, Rc<Type>, Rc<Type>) =
        match formals.as_slice() {
            [(x, x_t), (y, y_t)] => {
                (vec![x.clone(), y.clone()], x_t.clone(), y_t.clone())
            }
            [(p, t)] => match peel_type(t) {
                Type::Tuple(ts) if ts.len() == 2 => {
                    (vec![p.clone()], ts[0].clone(), ts[1].clone())
                }
                _ => return None,
            },
            _ => return None,
        };
    let disjuncts = split_orelse(body);
    let [base, recursive] = disjuncts.as_slice() else {
        return None;
    };
    if contains_self_call(base, name) {
        return None;
    }
    // The recursive disjunct is an `exists` whose filters hold the one
    // call and the steps beside it, and the call carries a formal through.
    let Expr::From(_, steps) = recursive else {
        return None;
    };
    if !matches!(steps.last().map(|s| &s.kind), Some(StepKind::Exists)) {
        return None;
    }
    let mut calls = 0;
    let mut others = 0;
    let mut carries = false;
    let mut rec_arg: Option<Expr> = None;
    let mut step_conjuncts: Vec<Expr> = Vec::new();
    for step in steps {
        let StepKind::Where(cond) = &step.kind else {
            continue;
        };
        for cj in split_conjuncts(cond) {
            match &cj {
                Expr::Apply(_, f, a, _) if matches!(f.as_ref(), Expr::Identifier(_, n) if n == name) =>
                {
                    calls += 1;
                    let free = free_names_in(a);
                    carries = names.iter().any(|n| free.contains(n));
                    rec_arg = Some(a.as_ref().clone());
                }
                _ => {
                    others += 1;
                    step_conjuncts.push(cj.clone());
                }
            }
        }
    }
    if calls != 1 || others == 0 {
        return None;
    }
    let element = Rc::new(Type::Tuple(vec![x_t.clone(), y_t.clone()]));
    let iterate = if carries {
        closure_iterate(base, &names, &x_t, &y_t, fn_env)?
    } else {
        bidirectional_iterate(
            base,
            &names,
            &element,
            rec_arg.as_ref()?,
            &step_conjuncts,
            fn_env,
        )?
    };
    closure_generator(pat_name, call, arg, &element, iterate)
}

/// The fixed point of a closure whose recursive call carries a formal
/// through, `f (x, z) andalso step (z, y)`, seeded by its base, which is a
/// membership of the formals: as morel-go's `buildIterate`, each new row
/// is extended through the base relation.
fn closure_iterate(
    base: &Expr,
    names: &[String],
    x_t: &Rc<Type>,
    y_t: &Rc<Type>,
    fn_env: &FnEnv,
) -> Option<Expr> {
    // The base is a membership of the formals in a collection: a tuple of
    // them in order, a record whose fields are them in its own order, or
    // the one formal. A base that calls a function that does not recurse
    // says what the function's body says, as morel-go's `inlinePredicate`
    // reads it.
    let base_conjuncts = split_conjuncts(&inline_predicate(base, fn_env));
    let [membership] = base_conjuncts.as_slice() else {
        return None;
    };
    let (lhs, coll) = call2_args(membership, &[BuiltInFunction::ListElem])?;
    let is_formal =
        |e: &Expr, f: &str| matches!(e, Expr::Identifier(_, n) if n == f);
    let labels = match (lhs, names) {
        (Expr::Tuple(t, items), [x, y])
            if items.len() == 2
                && is_formal(&items[0], x)
                && is_formal(&items[1], y) =>
        {
            match t.as_ref() {
                Type::Record(_, fields) => {
                    Some(fields.keys().map(ToString::to_string).collect())
                }
                _ => None,
            }
        }
        (e, [p]) if is_formal(e, p) => None,
        _ => return None,
    };
    Some(build_iterate_ast(x_t, y_t, y_t, coll.clone(), labels))
}

/// The fixed point of a closure whose recursive call rebinds every formal
/// through the step predicates beside it, as morel-go's
/// `buildBidirectional` builds it: `cousin (x, y) = sib (x, y) orelse
/// (exists xp, yp where par (x, xp) andalso par (y, yp) andalso cousin
/// (xp, yp))`. Each new row binds the recursive call's arguments, and
/// each formal joins back through its step predicate's collection. The
/// seed is the query of the base, which is grounded in its turn.
fn bidirectional_iterate(
    base: &Expr,
    names: &[String],
    element: &Rc<Type>,
    rec_arg: &Expr,
    step_conjuncts: &[Expr],
    fn_env: &FnEnv,
) -> Option<Expr> {
    let Type::Tuple(types) = element.as_ref() else {
        return None;
    };
    if names.len() != types.len() {
        return None;
    }
    let rec_args: Vec<String> = match rec_arg {
        Expr::Tuple(_, items) => items
            .iter()
            .map(|e| match e {
                Expr::Identifier(_, n) => Some(n.clone()),
                _ => None,
            })
            .collect::<Option<_>>()?,
        _ => return None,
    };
    if rec_args.len() != types.len() {
        return None;
    }
    let coll_t = Rc::new(Type::Bag(element.clone()));
    let prev = fresh_name();
    let prev_id = Expr::Identifier(element.clone(), prev.clone());
    let prev_field: HashMap<String, Expr> = rec_args
        .iter()
        .enumerate()
        .map(|(i, n)| (n.clone(), rel_lowerer::field_at(&prev_id, i)))
        .collect();
    let all_name = fresh_name();
    let new_name = fresh_name();
    let mut bound: Vec<(String, Rc<Type>)> =
        vec![(prev.clone(), element.clone())];
    let env = |bound: &[(String, Rc<Type>)]| {
        StepEnv::new(
            bound
                .iter()
                .map(|(n, t)| Binding::new(Id::new(n, 0), t.clone()))
                .collect(),
            bound.len() == 1,
            false,
        )
    };
    let mut steps = vec![Step::new(
        StepKind::Scan(
            Box::new(Pat::Identifier(element.clone(), prev.clone())),
            Box::new(Expr::Identifier(coll_t.clone(), new_name.clone())),
            None,
        ),
        env(&bound),
    )];
    let mut yield_args: Vec<Expr> = Vec::new();
    for (f, t) in names.iter().zip(types) {
        if let Some(e) = prev_field.get(f) {
            yield_args.push(e.clone());
            continue;
        }
        let mut joined = false;
        for c in step_conjuncts {
            let c = inline_predicate(c, fn_env);
            let Some((lhs, coll)) =
                call2_args(&c, &[BuiltInFunction::ListElem])
            else {
                continue;
            };
            let Expr::Tuple(tt, comps) = lhs else {
                continue;
            };
            if !comps.iter().any(|x| references(x, f)) {
                continue;
            }
            let mut pats: Vec<Pat> = Vec::new();
            let mut eqs: Vec<Expr> = Vec::new();
            for comp in comps {
                if references(comp, f) {
                    pats.push(Pat::Identifier(t.clone(), f.clone()));
                    continue;
                }
                let cf = fresh_name();
                let ct = comp.type_();
                pats.push(Pat::Identifier(ct.clone(), cf.clone()));
                eqs.push(make_eq_for_type(
                    &ct,
                    Expr::Identifier(ct.clone(), cf.clone()),
                    substitute(comp, &prev_field),
                ));
                bound.push((cf, ct));
            }
            bound.push((f.clone(), t.clone()));
            let pat = match tt.as_ref() {
                Type::Record(_, labels) => Pat::Record(
                    tt.clone(),
                    labels
                        .keys()
                        .zip(pats)
                        .map(|(l, p)| {
                            PatField::Labeled(l.to_string(), Box::new(p))
                        })
                        .collect(),
                    false,
                ),
                _ => Pat::Tuple(tt.clone(), pats),
            };
            steps.push(Step::new(
                StepKind::Scan(Box::new(pat), Box::new(coll.clone()), None),
                env(&bound),
            ));
            if !eqs.is_empty() {
                steps.push(Step::new(
                    StepKind::Where(Box::new(and_all(eqs))),
                    env(&bound),
                ));
            }
            yield_args.push(Expr::Identifier(t.clone(), f.clone()));
            joined = true;
            break;
        }
        if !joined {
            return None;
        }
    }
    let current = |t: &Rc<Type>| {
        StepEnv::new(
            vec![Binding::new(Id::new("current", 0), t.clone())],
            true,
            false,
        )
    };
    steps.push(Step::new(
        StepKind::Yield(Box::new(Expr::Tuple(element.clone(), yield_args))),
        current(element),
    ));
    let step_from = Expr::From(coll_t.clone(), steps);
    // The seed: the pairs the base holds of, `from x, y where base (x, y)`,
    // which is a query of its own, grounded when the walk reaches it.
    let listed = |e: StepEnv| e.with_ordered(true);
    let mut seed_bound: Vec<(String, Rc<Type>)> = Vec::new();
    let mut seed_steps: Vec<Step> = Vec::new();
    for (f, t) in names.iter().zip(types) {
        seed_bound.push((f.clone(), t.clone()));
        seed_steps.push(Step::new(
            StepKind::Scan(
                Box::new(Pat::Identifier(t.clone(), f.clone())),
                Box::new(Expr::Extent(
                    Rc::new(Type::List(t.clone())),
                    Span::new(""),
                    vec![f.clone()],
                )),
                None,
            ),
            listed(env(&seed_bound)),
        ));
    }
    seed_steps.push(Step::new(
        StepKind::Where(Box::new(base.clone())),
        listed(env(&seed_bound)),
    ));
    seed_steps.push(Step::new(
        StepKind::Yield(Box::new(Expr::Tuple(
            element.clone(),
            names
                .iter()
                .zip(types)
                .map(|(f, t)| Expr::Identifier(t.clone(), f.clone()))
                .collect(),
        ))),
        listed(current(element)),
    ));
    // Its scans are over extents, which are lists.
    let seed = Expr::From(Rc::new(Type::List(element.clone())), seed_steps);
    Some(iterate_apply(
        &coll_t, seed, step_from, &all_name, &new_name,
    ))
}

/// `Relational.iterate seed (fn (all, new) => step)`.
fn iterate_apply(
    coll_t: &Rc<Type>,
    seed: Expr,
    step: Expr,
    all_name: &str,
    new_name: &str,
) -> Expr {
    let pair_t = Rc::new(Type::Tuple(vec![coll_t.clone(), coll_t.clone()]));
    let pair_pat = Pat::Tuple(
        pair_t.clone(),
        vec![
            Pat::Identifier(coll_t.clone(), all_name.to_string()),
            Pat::Identifier(coll_t.clone(), new_name.to_string()),
        ],
    );
    let fn_t = Rc::new(Type::Fn(pair_t, coll_t.clone()));
    let update = Expr::Fn(
        fn_t.clone(),
        vec![Match {
            pat: pair_pat,
            expr: step,
        }],
        Span::new(""),
    );
    let iter_t = Rc::new(Type::Fn(
        coll_t.clone(),
        Rc::new(Type::Fn(fn_t.clone(), coll_t.clone())),
    ));
    let iter =
        Expr::Literal(iter_t, Val::Fn(BuiltInFunction::RelationalIterate));
    let with_seed = Expr::Apply(
        Rc::new(Type::Fn(fn_t, coll_t.clone())),
        Box::new(iter),
        Box::new(seed),
        Span::new(""),
    );
    Expr::Apply(
        coll_t.clone(),
        Box::new(with_seed),
        Box::new(update),
        Span::new(""),
    )
}

/// The generator of a closure's iteration, bound as the call's argument
/// says: the variable itself, or a tuple of variables and literals.
fn closure_generator(
    pat_name: &str,
    call: &Expr,
    arg: &Expr,
    element: &Rc<Type>,
    iterate: Expr,
) -> Option<Generator> {
    let gen_pat = match arg {
        Expr::Identifier(_, n) if n == pat_name => {
            Pat::Identifier(element.clone(), n.clone())
        }
        Expr::Tuple(_, items) => {
            let pats: Vec<Pat> =
                items.iter().map(pat_for_exp).collect::<Option<_>>()?;
            let names = pat_names(&Pat::Tuple(element.clone(), pats.clone()));
            let distinct: BTreeSet<&String> = names.iter().collect();
            if !names.iter().any(|n| n == pat_name) {
                return None;
            }
            if distinct.len() < names.len() {
                return duplicates_wrapper(
                    pat_name, call, items, element, iterate,
                );
            }
            Pat::Tuple(element.clone(), pats)
        }
        _ => return None,
    };
    let mut free = free_names_in(&iterate);
    for n in pat_names(&gen_pat) {
        free.remove(&n);
    }
    Some(Generator::new(
        gen_pat,
        iterate,
        Cardinality::Finite,
        free,
        true,
        true,
        vec![call.clone()],
    ))
}

/// Handles a call like `f (v, v)`, as morel-go's `duplicatesWrapper`
/// does: the closure scans fresh copies, the repeated positions equate,
/// and the variable's copy is yielded.
fn duplicates_wrapper(
    pat_name: &str,
    call: &Expr,
    items: &[Expr],
    element: &Rc<Type>,
    iterate: Expr,
) -> Option<Generator> {
    let Type::Tuple(types) = element.as_ref() else {
        return None;
    };
    if types.len() != items.len() {
        return None;
    }
    let mut copies: Vec<Pat> = Vec::new();
    let mut bound: Vec<Binding> = Vec::new();
    let mut by_var: Vec<(String, Vec<Expr>)> = Vec::new();
    for (item, t) in items.iter().zip(types) {
        let Expr::Identifier(_, n) = item else {
            return None;
        };
        let c = fresh_name();
        copies.push(Pat::Identifier(t.clone(), c.clone()));
        bound.push(Binding::new(Id::new(&c, 0), t.clone()));
        let id = Expr::Identifier(t.clone(), c);
        match by_var.iter_mut().find(|(v, _)| v == n) {
            Some((_, group)) => group.push(id),
            None => by_var.push((n.clone(), vec![id])),
        }
    }
    let mut eqs: Vec<Expr> = Vec::new();
    for (_, group) in &by_var {
        for other in &group[1..] {
            eqs.push(make_eq_for_type(
                &other.type_(),
                group[0].clone(),
                other.clone(),
            ));
        }
    }
    let first = by_var
        .iter()
        .find(|(v, _)| v == pat_name)
        .map(|(_, group)| group[0].clone())?;
    let pat_t = first.type_();
    let free = free_names_in(&iterate);
    let env = || StepEnv::new(bound.clone(), false, false);
    let mut steps = vec![Step::new(
        StepKind::Scan(
            Box::new(Pat::Tuple(element.clone(), copies)),
            Box::new(iterate),
            None,
        ),
        env(),
    )];
    if !eqs.is_empty() {
        steps.push(Step::new(StepKind::Where(Box::new(and_all(eqs))), env()));
    }
    steps.push(Step::new(
        StepKind::Yield(Box::new(first)),
        StepEnv::new(
            vec![Binding::new(Id::new("current", 0), pat_t.clone())],
            true,
            false,
        ),
    ));
    Some(Generator::new(
        Pat::Identifier(pat_t.clone(), pat_name.to_string()),
        Expr::From(Rc::new(Type::Bag(pat_t)), steps),
        Cardinality::Finite,
        free,
        true,
        true,
        vec![call.clone()],
    ))
}

/// Recognises a constraint of the form `f arg` where `f` is a let-
/// bound single-argument function (i.e. `val rec f = fn p => body`).
/// Inlines the body with `p` substituted by `arg`, expands any
/// resulting `andalso` into multiple conjuncts, and recursively
/// runs `maybe_generator` on the augmented constraint set.
///
/// A small "in-progress" stack guards against infinite inlining
/// of recursive functions; recursion stays unsupported in Phase 3
/// (it lands in 3ec81171 / Phase 7).
#[allow(clippy::too_many_arguments)]
fn maybe_function(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
    unbounded_siblings: &BTreeSet<String>,
    ungrounded: &BTreeSet<String>,
) -> bool {
    if fn_env.is_empty() {
        return false;
    }
    for (idx, c) in constraints.iter().enumerate() {
        // Recognise both the inlined form (`Apply(Literal(Fn(_)),
        // arg)`, which doesn't apply here) and the un-inlined
        // identifier form: `Apply(Identifier(name), arg)`.
        let Expr::Apply(_, f, arg, _) = c else {
            continue;
        };
        let Expr::Identifier(_, fn_name) = f.as_ref() else {
            continue;
        };
        let Some((param_pat, body)) = fn_env.get(fn_name) else {
            continue;
        };
        // A recursive function's body holds the call again; the tree
        // grounder inverts it by `maybe_rec_fn`, or not at all.
        if tests_rebound() && contains_self_call(body, fn_name) {
            continue;
        }
        // A call that does not read the name says nothing about it, as
        // morel-java's `maybeFunction`, which grounds the name from the
        // body alone, finds: inlining `isDept d` to ground `e` would
        // find `e`'s generator among the other constraints and hand it
        // `d elem depts` as a filter that reads another leaf.
        if !free_names_in(arg).contains(pat_name) {
            continue;
        }
        // Build the substitution map. `fn x => body` substitutes
        // `x → arg`. `fn (a, b) => body` substitutes `a → arg.0`,
        // `b → arg.1` if `arg` is a literal tuple expression of
        // matching arity; otherwise we'd need a record-selector
        // application (or a let-in to materialise the tuple
        // once), which we don't bother with here.
        let mut subst_map: HashMap<String, Expr> = HashMap::new();
        match param_pat {
            Pat::Identifier(_, param_name) => {
                subst_map.insert(param_name.clone(), (**arg).clone());
            }
            Pat::Tuple(_, sub_pats) => {
                let Expr::Tuple(_, arg_elems) = arg.as_ref() else {
                    continue;
                };
                if sub_pats.len() != arg_elems.len() {
                    continue;
                }
                let mut ok = true;
                for (sp, ae) in sub_pats.iter().zip(arg_elems.iter()) {
                    if let Pat::Identifier(_, n) = sp {
                        subst_map.insert(n.clone(), ae.clone());
                    } else {
                        ok = false;
                        break;
                    }
                }
                if !ok {
                    continue;
                }
            }
            _ => continue,
        };
        let inlined = substitute(body, &subst_map);
        // Decompose `andalso`; merge with the rest of the outer
        // constraints.
        let inner_conjuncts = split_conjuncts(&inlined);
        let mut augmented: Vec<Expr> =
            Vec::with_capacity(constraints.len() - 1 + inner_conjuncts.len());
        for (j, oc) in constraints.iter().enumerate() {
            if j != idx {
                augmented.push(oc.clone());
            }
        }
        augmented.extend(inner_conjuncts);

        // Probe with a fresh cache so we don't pollute on failure.
        let mut probe = Cache::new();
        // Pass an env *without* this fn so we don't recurse on it.
        let mut env2 = fn_env.clone();
        env2.remove(fn_name);
        // The body is read in the query's own scope: a name the
        // query has yet to ground is still ungrounded inside it.
        if !maybe_generator_with_scope(
            &mut probe,
            pat,
            pat_name,
            pat_type,
            ordered,
            &augmented,
            &env2,
            datatypes,
            outer_scope,
            unbounded_siblings,
            ungrounded,
        ) {
            continue;
        }
        let mut inner_gen = match probe.best(pat_name) {
            Some(g) => g.clone(),
            None => continue,
        };

        // Identify inlined conjuncts that the chosen leaf strategy
        // didn't fold into `inner_gen.exp`. They came from the
        // function body and aren't visible in any surrounding
        // `where` step, so without an explicit row filter they'd
        // be silently dropped. Attach the AND of unconsumed inner
        // conjuncts as `extra_filter`; the rebuild emits it as
        // the Scan's per-row condition.
        let inner_conjuncts2 = split_conjuncts(&inlined);
        let unconsumed: Vec<Expr> = inner_conjuncts2
            .into_iter()
            .filter(|ic| !inner_gen.provenance.iter().any(|p| expr_eq(p, ic)))
            .collect();
        // One that reads another name still to be grounded is not one
        // this scan can test, as morel-go's `existsGenerator` finds; the
        // call, which then stays as a filter over what this grounds,
        // tests it instead -- its body grounded where the function was
        // declared.
        let mut gen_names: Vec<String> = Vec::new();
        inner_gen
            .pat
            .for_each_id_pat(&mut |(_, n)| gen_names.push(n.to_string()));
        let (unconsumed, unreadable): (Vec<Expr>, Vec<Expr>) =
            unconsumed.into_iter().partition(|ic| {
                !free_names_in(ic).iter().any(|n| {
                    !gen_names.contains(n) && unbounded_siblings.contains(n)
                })
            });
        if !unreadable.is_empty() {
            inner_gen.sealed = false;
        }
        if !unconsumed.is_empty() {
            let combined = and_all(unconsumed);
            inner_gen.extra_filter =
                Some(match inner_gen.extra_filter.take() {
                    Some(existing) => and_all(vec![existing, combined]),
                    None => combined,
                });
        }

        // Add the original function-call conjunct to provenance so
        // the surrounding `where` can drop it.
        inner_gen.provenance.push(c.clone());
        cache.add(pat_name.to_string(), inner_gen);
        return true;
    }
    false
}

/// Recognises a constraint of the form `case e of …` and, when
/// possible, derives a generator for the unbounded pattern.
///
/// Phase 4 handled the single-arm case (`case e of name => body`).
/// Phase 5 extends to:
///   * multi-arm with literal-pattern → `true` arms (collect the
///     literals into an elem-generator), and
///   * single arm with id-pattern + body referencing the rebound
///     identifier (carried over from Phase 4).
///
/// Mixed-shape multi-arm (literal arms + a variable-arm with a
/// non-trivial condition) needs a union strategy and lands in
/// Phase 6's maybeUnion.
#[allow(clippy::too_many_arguments)]
fn maybe_case(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
    unbounded_siblings: &BTreeSet<String>,
    ungrounded: &BTreeSet<String>,
) -> bool {
    for (idx, c) in constraints.iter().enumerate() {
        let Expr::Case(_, subject, arms, _) = c else {
            continue;
        };

        // 4a: a single-arm case rebinds the subject inside the
        // body: `case e of name => body` binds the whole of it, and
        // `case (e1, e2) of (a, b) => body` binds a component to
        // each name, which is what the pattern says.
        if arms.len() == 1
            && let Some(subst_map) = arm_bindings(&arms[0], subject)
        {
            let inlined = substitute(&arms[0].expr, &subst_map);
            let inner_conjuncts = split_conjuncts(&inlined);
            if try_recurse(
                cache,
                pat,
                pat_name,
                pat_type,
                ordered,
                constraints,
                idx,
                &inner_conjuncts,
                fn_env,
                datatypes,
                c,
                outer_scope,
                unbounded_siblings,
                ungrounded,
            ) {
                return true;
            }
            continue;
        }

        // 5a: build a per-arm constraint and combine with `orelse`.
        // Each arm contributes:
        //   * literal pattern + body=`true`  ⇒  `subject = lit`
        //   * literal pattern + body=`false` ⇒  no contribution
        //   * id pattern + body              ⇒  `body[id := subject]`
        //   * wildcard + body=`false`        ⇒  no contribution (terminal
        //                                          no-match arm)
        // (Constructor patterns and exclusion-constraints from
        // false-arms are deferred to a later phase.)
        let Some(or_expr) = arms_to_orelse(subject, arms) else {
            continue;
        };
        if try_recurse(
            cache,
            pat,
            pat_name,
            pat_type,
            ordered,
            constraints,
            idx,
            &[or_expr],
            fn_env,
            datatypes,
            c,
            outer_scope,
            unbounded_siblings,
            ungrounded,
        ) {
            return true;
        }
    }
    false
}

/// Builds an `orelse`-chained boolean expression from a list of
/// case arms. Returns `None` if any arm is in a shape we don't yet
/// know how to invert (constructor pattern, tuple pattern, etc.).
fn arms_to_orelse(subject: &Expr, arms: &[Match]) -> Option<Expr> {
    let mut branches: Vec<Expr> = Vec::with_capacity(arms.len());
    for arm in arms {
        match (&arm.pat, &arm.expr) {
            (Pat::Literal(t, v), body) => {
                let lit = Expr::Literal(t.clone(), v.clone());
                let eq = make_eq_for_type(t, subject.clone(), lit);
                if let Expr::Literal(_, Val::Bool(true)) = body {
                    branches.push(eq);
                } else if let Expr::Literal(_, Val::Bool(false)) = body {
                    // No contribution (and an exclusion constraint
                    // should be added to subsequent arms — we don't
                    // yet do that).
                } else {
                    return None;
                }
            }
            (Pat::Identifier(_, name), body) => {
                if let Expr::Literal(_, Val::Bool(false)) = body {
                    // Terminal "no-match" arm; contributes nothing.
                    continue;
                }
                let mut subst_map: HashMap<String, Expr> = HashMap::new();
                subst_map.insert(name.clone(), subject.clone());
                let body2 = substitute(body, &subst_map);
                branches.push(body2);
            }
            (Pat::Wildcard(_), body) => {
                if let Expr::Literal(_, Val::Bool(false)) = body {
                    // Terminal no-match arm.
                    continue;
                }
                // A `_ => non-false` body would always match — we'd
                // need to enumerate the subject's type to handle it.
                // Skip for now.
                return None;
            }
            _ => return None,
        }
    }
    if branches.is_empty() {
        return None;
    }
    let mut iter = branches.into_iter();
    let first = iter.next().unwrap();
    Some(iter.fold(first, make_orelse))
}

fn make_eq_for_type(t: &Type, lhs: Expr, rhs: Expr) -> Expr {
    let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let arg_t = Rc::new(Type::Tuple(vec![
        Rc::new((*t).clone()),
        Rc::new((*t).clone()),
    ]));
    let f = match t {
        Type::Primitive(PrimitiveType::Int) => BuiltInFunction::IntEq,
        Type::Primitive(PrimitiveType::Real) => BuiltInFunction::RealEq,
        Type::Primitive(PrimitiveType::String) => BuiltInFunction::StringEq,
        Type::Primitive(PrimitiveType::Char) => BuiltInFunction::CharEq,
        Type::Primitive(PrimitiveType::Bool) => BuiltInFunction::BoolEq,
        _ => BuiltInFunction::GEq,
    };
    let fn_t = Rc::new(Type::Fn(arg_t.clone(), bool_t.clone()));
    let fn_lit = Expr::Literal(fn_t, Val::Fn(f));
    let arg = Expr::Tuple(arg_t, vec![lhs, rhs]);
    Expr::Apply(bool_t, Box::new(fn_lit), Box::new(arg), Span::new(""))
}

fn make_orelse(lhs: Expr, rhs: Expr) -> Expr {
    let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let pair_t = Rc::new(Type::Tuple(vec![
        Rc::new((*bool_t).clone()),
        Rc::new((*bool_t).clone()),
    ]));
    let fn_t = Rc::new(Type::Fn(pair_t.clone(), bool_t.clone()));
    let fn_lit = Expr::Literal(fn_t, Val::Fn(BuiltInFunction::BoolOrElse));
    let arg = Expr::Tuple(pair_t, vec![lhs, rhs]);
    Expr::Apply(bool_t, Box::new(fn_lit), Box::new(arg), Span::new(""))
}

/// Helper: re-runs `maybe_generator` with `replacements` substituted
/// for the constraint at index `idx`, then promotes the generator
/// (if any) into the real `cache` after adding the original
/// constraint to its provenance.
#[allow(clippy::too_many_arguments)]
fn try_recurse(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    skip_idx: usize,
    replacements: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
    original: &Expr,
    outer_scope: &BTreeSet<String>,
    unbounded_siblings: &BTreeSet<String>,
    ungrounded: &BTreeSet<String>,
) -> bool {
    let mut augmented: Vec<Expr> =
        Vec::with_capacity(constraints.len() - 1 + replacements.len());
    for (j, oc) in constraints.iter().enumerate() {
        if j != skip_idx {
            augmented.push(oc.clone());
        }
    }
    augmented.extend(replacements.iter().cloned());
    let mut probe = Cache::new();
    if !maybe_generator_with_scope(
        &mut probe,
        pat,
        pat_name,
        pat_type,
        ordered,
        &augmented,
        fn_env,
        datatypes,
        outer_scope,
        unbounded_siblings,
        ungrounded,
    ) {
        return false;
    }
    let mut inner_gen = match probe.best(pat_name) {
        Some(g) => g.clone(),
        None => return false,
    };
    inner_gen.provenance.push(original.clone());
    cache.add(pat_name.to_string(), inner_gen);
    true
}

/// Where a single-arm `case`'s pattern binds the subject: the whole
/// of it for a name, and a component for each name of a tuple
/// pattern whose subject is a tuple of the same arity.
///
/// `None` where the pattern is one this cannot take apart.
fn arm_bindings(arm: &Match, subject: &Expr) -> Option<HashMap<String, Expr>> {
    let mut map = HashMap::new();
    if let Some(name) = arm_id_pat(arm) {
        map.insert(name, subject.clone());
        return Some(map);
    }
    let Pat::Tuple(_, pats) = &arm.pat else {
        return None;
    };
    let Expr::Tuple(_, args) = subject else {
        return None;
    };
    if pats.len() != args.len() {
        return None;
    }
    for (p, a) in pats.iter().zip(args.iter()) {
        match p {
            Pat::Identifier(_, name) => {
                map.insert(name.clone(), a.clone());
            }
            Pat::Wildcard(_) => {}
            _ => return None,
        }
    }
    Some(map)
}

/// If a single-arm match is `name => body`, returns `name`.
fn arm_id_pat(m: &Match) -> Option<String> {
    if let Pat::Identifier(_, n) = &m.pat {
        Some(n.clone())
    } else {
        None
    }
}

/// Recognises a constraint of the form
///   `branch_1 orelse branch_2 [orelse branch_3 ...]`
/// (decomposed via the BoolOrElse builtin), derives a generator
/// for each branch by recursing `maybe_generator` with that
/// branch as the only constraint, and concatenates the resulting
/// expressions with `Bag.concat`/`List.concat`.
///
/// The combined generator is unsealed: it doesn't subsume any
/// individual branch as a where-conjunct (the surrounding `where`
/// will keep the original `orelse` for correctness).
/// Recognises a constraint `{f1=v1, …, fk=pat_name, …} elem coll`
/// where one tuple/record component is `pat_name` and the
/// others are literals or outer-scope identifiers (free
/// variables not bound by any from-step in this query). Builds
/// a generator that scans `coll`, filters on the literal /
/// outer-bound components, and projects the `pat_name`
/// component. Used for queries like
///
///   exists price where {bar="cask", beer=b, price=price}
///                       elem barBeers
///
/// where `b` is a function parameter (outer-scope) and
/// `price` is the unbounded variable.
fn maybe_record_elem_projection(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    _pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    outer_scope: &BTreeSet<String>,
) -> bool {
    for c in constraints {
        let Some((lhs, rhs)) = call2_args(c, &[BuiltInFunction::ListElem])
        else {
            continue;
        };
        // lhs must be a tuple/record with exactly one
        // component that's `Identifier(pat_name)` and all
        // other components either literals or non-pat-name
        // identifiers (assumed outer-scope).
        let Expr::Tuple(tuple_t, ids) = lhs else {
            continue;
        };
        // Field labels in alphabetical order from the type.
        let labels: Vec<String> = match tuple_t.as_ref() {
            Type::Record(_, fields) => fields
                .keys()
                .filter_map(|l| match l {
                    Label::String(n) => Some(n.clone()),
                    _ => None,
                })
                .collect(),
            Type::Tuple(_) => {
                // Position-indexed labels "1", "2", …
                (1..=ids.len()).map(|i| i.to_string()).collect()
            }
            _ => continue,
        };
        if labels.len() != ids.len() {
            continue;
        }
        let mut pat_field: Option<String> = None;
        let mut filters: Vec<(String, Expr)> = Vec::new();
        let mut ok = true;
        for (label, id) in labels.iter().zip(ids.iter()) {
            match id {
                Expr::Identifier(_, n) if n == pat_name => {
                    if pat_field.is_some() {
                        // Multiple components claim pat_name —
                        // skip; let decompose handle it.
                        ok = false;
                        break;
                    }
                    pat_field = Some(label.clone());
                }
                Expr::Identifier(_, n) => {
                    // Only treat as filter if the name is known
                    // to be in outer scope (function parameter,
                    // let-bound val, …). Names not in
                    // outer_scope are likely from-step extents
                    // that `decompose_tuple_elems` should handle.
                    if !outer_scope.contains(n) {
                        ok = false;
                        break;
                    }
                    filters.push((label.clone(), id.clone()));
                }
                Expr::Literal(_, _) => {
                    filters.push((label.clone(), id.clone()));
                }
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }
        let Some(pat_field) = pat_field else {
            continue;
        };

        // Build: from r in coll where r.f1 = v1 andalso …
        //        yield #pat_field r
        use crate::compile::core::{Step, StepEnv, StepKind};
        use crate::compile::type_env::Id;

        let row_t = match tuple_t.as_ref() {
            Type::Record(prog, fields) => {
                Rc::new(Type::Record(*prog, fields.clone()))
            }
            _ => continue,
        };
        let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
        let row_var = "__rep$".to_string();
        let scan_env = StepEnv::new(
            vec![Binding::new(Id::new(&row_var, 0), row_t.clone())],
            true,
            ordered,
        );
        let mut steps: Vec<Step> = Vec::new();
        steps.push(Step::new(
            StepKind::Scan(
                Box::new(Pat::Identifier(row_t.clone(), row_var.clone())),
                Box::new(rhs.clone()),
                None,
            ),
            scan_env.clone(),
        ));
        // Build filter conditions: r.f = v.
        if !filters.is_empty() {
            let filter_exprs: Vec<Expr> = filters
                .iter()
                .map(|(label, value_expr)| {
                    let field_t: Option<Rc<Type>> = match tuple_t.as_ref() {
                        Type::Record(_, fields) => {
                            fields.get(&Label::String(label.clone())).cloned()
                        }
                        _ => None,
                    };
                    let Some(field_t) = field_t else {
                        return Expr::Literal(bool_t.clone(), Val::Bool(false));
                    };
                    let slot = match tuple_t.as_ref() {
                        Type::Record(_, fields) => fields
                            .keys()
                            .position(
                                |l| matches!(l, Label::String(n) if n == label),
                            )
                            .unwrap(),
                        _ => 0,
                    };
                    let sel_fn_t =
                        Rc::new(Type::Fn(row_t.clone(), field_t.clone()));
                    let sel = Expr::RecordSelector(sel_fn_t.clone(), slot);
                    let r_id = Expr::Identifier(row_t.clone(), row_var.clone());
                    let lhs_field = Expr::Apply(
                        field_t.clone(),
                        Box::new(sel),
                        Box::new(r_id),
                        Span::new(""),
                    );
                    make_eq_for_type(&field_t, lhs_field, value_expr.clone())
                })
                .collect();
            let cond = and_all(filter_exprs);
            steps.push(Step::new(
                StepKind::Where(Box::new(cond)),
                scan_env.clone(),
            ));
        }
        // Build the projection: `#pat_field r` (a record selector).
        let pat_field_t: Rc<Type> = match tuple_t.as_ref() {
            Type::Record(_, fields) => {
                match fields.get(&Label::String(pat_field.clone())).cloned() {
                    Some(t) => t,
                    None => continue,
                }
            }
            _ => continue,
        };
        let pat_field_slot = match tuple_t.as_ref() {
            Type::Record(_, fields) => fields
                .keys()
                .position(|l| matches!(l, Label::String(n) if n == &pat_field))
                .unwrap(),
            _ => 0,
        };
        let sel_fn_t = Rc::new(Type::Fn(row_t.clone(), pat_field_t.clone()));
        let sel = Expr::RecordSelector(sel_fn_t, pat_field_slot);
        let r_id = Expr::Identifier(row_t.clone(), row_var.clone());
        let yield_expr = Expr::Apply(
            pat_field_t.clone(),
            Box::new(sel),
            Box::new(r_id),
            Span::new(""),
        );
        let yield_env = StepEnv::new(
            vec![Binding::new(Id::new(pat_name, 0), pat_field_t.clone())],
            true,
            ordered,
        );
        steps.push(Step::new(StepKind::Yield(Box::new(yield_expr)), yield_env));
        let coll_t = if ordered {
            Rc::new(Type::List(pat_field_t.clone()))
        } else {
            Rc::new(Type::Bag(pat_field_t.clone()))
        };
        let exp = Expr::From(coll_t, steps);

        let mut free = free_names_in(&exp);
        free.remove(pat_name);
        let generator = Generator::new(
            pat.clone(),
            exp,
            Cardinality::Finite,
            free,
            true,
            true,
            vec![c.clone()],
        );
        cache.add(pat_name.to_string(), generator);
        return true;
    }
    false
}

/// Recognises a `case` constraint whose subject is the pattern
/// we're trying to ground, and whose arms include constructor
/// patterns (e.g. `INL n => n >= 5 andalso n <= 8`). For each
/// constructor arm we derive a generator for the sub-pattern
/// from the arm's body, then wrap the generator's exp with
/// the constructor (`Bag.map (fn x => INL x) <inner>`). All
/// arms' results are union'd via `Bag.concat` (or
/// `List.concat` for ordered scope).
///
/// Wildcard / nullary-constructor / `_ => false` arms
/// contribute nothing; an arm with a non-bool body and a non-
/// invertible sub-constraint causes us to skip the whole case.
fn maybe_case_constructor(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    _pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> bool {
    for c in constraints {
        let Expr::Case(_, subject, arms, _) = c else {
            continue;
        };
        let Expr::Identifier(_, sn) = subject.as_ref() else {
            continue;
        };
        if sn != pat_name {
            continue;
        }
        // At least one constructor arm with a non-`false` body.
        let has_constructor_arm = arms.iter().any(|a| {
            matches!(a.pat, Pat::Constructor(_, _, _))
                && !matches!(a.expr, Expr::Literal(_, Val::Bool(false)))
        });
        if !has_constructor_arm {
            continue;
        }

        let mut branch_exps: Vec<Expr> = Vec::new();
        let all_free: BTreeSet<String> = BTreeSet::new();
        let mut ok = true;
        for arm in arms {
            // Skip false-body arms.
            if matches!(arm.expr, Expr::Literal(_, Val::Bool(false))) {
                continue;
            }
            match &arm.pat {
                Pat::Constructor(_ctor_t, ctor_name, Some(sub_pat)) => {
                    let Some(ctor_fn) = constructor_to_builtin(ctor_name)
                    else {
                        ok = false;
                        break;
                    };
                    let elem_t = pat.type_();
                    let sub_t = sub_pat.type_();
                    let Some((sub_pat_name, sub_exp)) =
                        derive_payload_generator(
                            sub_pat, &arm.expr, ordered, fn_env, datatypes,
                        )
                    else {
                        ok = false;
                        break;
                    };
                    let wrapped = build_map_constructor(
                        ctor_fn,
                        sub_t,
                        elem_t,
                        sub_pat_name,
                        sub_exp,
                        ordered,
                    );
                    branch_exps.push(wrapped);
                }
                // Constant constructor `Pat::Constructor(_, ctor, None)`
                // with non-false body: support `body == true` only —
                // the constructor's single value is a member.
                Pat::Constructor(_, _, None) => {
                    // Not yet supported.
                    ok = false;
                    break;
                }
                Pat::Wildcard(_) => {
                    // Already filtered false bodies above; a non-false
                    // wildcard body would always match — needs
                    // enumeration of subject's type.
                    ok = false;
                    break;
                }
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok || branch_exps.is_empty() {
            continue;
        }

        // Build `Bag.concat [b1, b2, ...]` (or List.concat).
        let elem_t = pat.type_();
        let coll_t = if ordered {
            Rc::new(Type::List(elem_t.clone()))
        } else {
            Rc::new(Type::Bag(elem_t.clone()))
        };
        let combined = if branch_exps.len() == 1 {
            branch_exps.into_iter().next().unwrap()
        } else {
            let list_of_coll_t =
                Rc::new(Type::List(Rc::new((*coll_t).clone())));
            let arg_list = Expr::List(list_of_coll_t.clone(), branch_exps);
            let concat_fn = if ordered {
                BuiltInFunction::ListConcat
            } else {
                BuiltInFunction::BagConcat
            };
            let fn_t = Rc::new(Type::Fn(list_of_coll_t, coll_t.clone()));
            let fn_lit = Expr::Literal(fn_t, Val::Fn(concat_fn));
            Expr::Apply(
                coll_t,
                Box::new(fn_lit),
                Box::new(arg_list),
                Span::new(""),
            )
        };

        let generator = Generator::new(
            pat.clone(),
            combined,
            Cardinality::Finite,
            all_free,
            false,
            false,
            vec![c.clone()],
        );
        cache.add(pat_name.to_string(), generator);
        return true;
    }
    false
}

/// Builds a generator for the payload of a constructor arm:
/// returns `(bind_name, exp)` where `exp` is a list/bag of
/// payload values and `bind_name` is the name to use in the
/// `Bag.map (fn bind_name => CTOR bind_name)` wrapping.
///
/// For a Pat::Identifier sub-pattern the bind_name is the
/// identifier itself and `exp` comes from `maybe_generator`
/// on the body.
///
/// For a Pat::Tuple sub-pattern (e.g. `INR (b, i)`) we build
/// a synthetic `from b, i where <body> yield (b, i)` query,
/// expand it with predicate inversion, and use a fresh
/// bind_name for the wrapping fn (the map argument will be
/// the whole tuple).
fn derive_payload_generator(
    sub_pat: &Pat,
    body: &Expr,
    ordered: bool,
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> Option<(String, Expr)> {
    match sub_pat {
        Pat::Identifier(t, n) => {
            let inner_constraints = split_conjuncts(body);
            let mut probe = Cache::new();
            if !maybe_generator(
                &mut probe,
                sub_pat,
                n,
                t,
                ordered,
                &inner_constraints,
                fn_env,
                datatypes,
            ) {
                return None;
            }
            let g = probe.best(n)?;
            Some((n.clone(), g.exp.clone()))
        }
        // Literal sub-pat (e.g. `INL 0`) — only contributes when
        // the body is `true`; one element list.
        Pat::Literal(lit_t, v) => {
            if !matches!(body, Expr::Literal(_, Val::Bool(true))) {
                return None;
            }
            let elem = Expr::Literal(lit_t.clone(), v.clone());
            let coll_t = if ordered {
                Rc::new(Type::List(lit_t.clone()))
            } else {
                Rc::new(Type::Bag(lit_t.clone()))
            };
            // `[lit]` as a List value; bags are formed at the
            // outer concat layer if needed.
            let list_t = Rc::new(Type::List(lit_t.clone()));
            let list_lit = Expr::List(list_t.clone(), vec![elem]);
            // For bag scope, wrap with `Bag.fromList`-equivalent —
            // but our concat happily mixes lists into bags via
            // the type system. Keep as List for simplicity; the
            // outer bag-concat will treat it as elements.
            let _ = coll_t;
            Some(("__lit".to_string(), list_lit))
        }
        Pat::Tuple(tuple_t, sub_pats) => {
            // Build `from <each leaf> where body yield (leaves)`
            // whose generators the walk derives when it reaches it.
            use crate::compile::core::{Step, StepEnv, StepKind};
            use crate::compile::type_env::Id;

            let mut steps: Vec<Step> = Vec::new();
            let mut leaves: Vec<(String, Rc<Type>)> = Vec::new();
            for sp in sub_pats {
                let (n, t) = match sp {
                    Pat::Identifier(t, n) => (n.clone(), t.clone()),
                    _ => return None,
                };
                leaves.push((n.clone(), t.clone()));
                let scan_env = StepEnv::new(
                    leaves
                        .iter()
                        .map(|(n, t)| Binding::new(Id::new(n, 0), t.clone()))
                        .collect(),
                    leaves.len() == 1,
                    ordered,
                );
                steps.push(Step::new(
                    StepKind::Scan(
                        Box::new(Pat::Identifier(t.clone(), n.clone())),
                        Box::new(Expr::Extent(
                            t.clone(),
                            Span::new(""),
                            vec![n],
                        )),
                        None,
                    ),
                    scan_env,
                ));
            }
            let last_env = steps.last().unwrap().env.clone();
            steps.push(Step::new(
                StepKind::Where(Box::new(body.clone())),
                last_env.clone(),
            ));
            // Yield the tuple in original sub-pattern order.
            let yield_items: Vec<Expr> = sub_pats
                .iter()
                .map(|sp| match sp {
                    Pat::Identifier(t, n) => {
                        Expr::Identifier(t.clone(), n.clone())
                    }
                    _ => unreachable!(),
                })
                .collect();
            let yield_expr = Expr::Tuple(tuple_t.clone(), yield_items);
            // After the yield the from result is `tuple_t bag`.
            let yield_env = StepEnv::new(
                vec![Binding::new(Id::new("__pl", 0), tuple_t.clone())],
                true,
                ordered,
            );
            steps.push(Step::new(
                StepKind::Yield(Box::new(yield_expr)),
                yield_env,
            ));
            let coll_t = if ordered {
                Rc::new(Type::List(tuple_t.clone()))
            } else {
                Rc::new(Type::Bag(tuple_t.clone()))
            };
            // The leaves' extents are grounded when the walk reaches
            // this query, as morel-go's `conArmGenerator` leaves them.
            let from = Expr::From(coll_t, steps);
            Some(("__pl".to_string(), from))
        }
        _ => None,
    }
}

/// Maps a constructor name to its `BuiltInFunction` value.
/// Returns `None` for user-defined or unsupported constructors.
fn constructor_to_builtin(name: &str) -> Option<BuiltInFunction> {
    match name {
        "INL" => Some(BuiltInFunction::EitherInl),
        "INR" => Some(BuiltInFunction::EitherInr),
        "SOME" => Some(BuiltInFunction::OptionSome),
        _ => None,
    }
}

/// Builds `Bag.map (fn x => CTOR x) inner` (or List.map for
/// ordered scope), wrapping every payload in `inner` with the
/// given constructor.
#[allow(clippy::needless_pass_by_value)]
fn build_map_constructor(
    ctor_fn: BuiltInFunction,
    payload_t: Rc<Type>,
    elem_t: Rc<Type>,
    sub_pat_name: String,
    inner: Expr,
    ordered: bool,
) -> Expr {
    let coll_t = if ordered {
        Rc::new(Type::List(elem_t.clone()))
    } else {
        Rc::new(Type::Bag(elem_t.clone()))
    };
    let inner_coll_t = if ordered {
        Rc::new(Type::List(payload_t.clone()))
    } else {
        Rc::new(Type::Bag(payload_t.clone()))
    };
    // `fn x => CTOR x`
    let ctor_fn_t = Rc::new(Type::Fn(payload_t.clone(), elem_t.clone()));
    let ctor_lit = Expr::Literal(ctor_fn_t.clone(), Val::Fn(ctor_fn));
    let body = Expr::Apply(
        elem_t.clone(),
        Box::new(ctor_lit),
        Box::new(Expr::Identifier(payload_t.clone(), sub_pat_name.clone())),
        Span::new(""),
    );
    let fn_pat = Pat::Identifier(payload_t.clone(), sub_pat_name);
    let map_arg_fn_t = Rc::new(Type::Fn(payload_t.clone(), elem_t.clone()));
    let map_arg = Expr::Fn(
        map_arg_fn_t.clone(),
        vec![Match {
            pat: fn_pat,
            expr: body,
        }],
        Span::new(""),
    );
    // `Bag.map`-curried: Apply(Apply(map_fn, fn_arg), inner)
    let map_builtin = if ordered {
        BuiltInFunction::ListMap
    } else {
        BuiltInFunction::BagMap
    };
    let map_t = Rc::new(Type::Fn(
        map_arg_fn_t,
        Rc::new(Type::Fn(inner_coll_t.clone(), coll_t.clone())),
    ));
    let map_lit = Expr::Literal(map_t, Val::Fn(map_builtin));
    let map_partial_t = Rc::new(Type::Fn(inner_coll_t, coll_t.clone()));
    let map_partial = Expr::Apply(
        map_partial_t,
        Box::new(map_lit),
        Box::new(map_arg),
        Span::new(""),
    );
    Expr::Apply(
        coll_t,
        Box::new(map_partial),
        Box::new(inner),
        Span::new(""),
    )
}

#[allow(clippy::too_many_arguments)]
fn maybe_union(
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    pat_type: &Type,
    ordered: bool,
    constraints: &[Expr],
    fn_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
    unbounded_siblings: &BTreeSet<String>,
    ungrounded: &BTreeSet<String>,
) -> bool {
    for c in constraints {
        let branches = split_orelse(c);
        if branches.len() < 2 {
            continue;
        }
        let mut sub_gens: Vec<Generator> = Vec::with_capacity(branches.len());
        let mut all_ok = true;
        for branch in &branches {
            // Split each branch into its top-level `andalso`
            // conjuncts so leaf strategies see e.g. `i > 0` and
            // `i < 10` as separate constraints.
            let branch_conjuncts = split_conjuncts(branch);
            let mut probe = Cache::new();
            if !maybe_generator_with_scope(
                &mut probe,
                pat,
                pat_name,
                pat_type,
                ordered,
                &branch_conjuncts,
                fn_env,
                datatypes,
                outer_scope,
                unbounded_siblings,
                ungrounded,
            ) {
                all_ok = false;
                break;
            }
            if let Some(g) = probe.best(pat_name) {
                sub_gens.push(g.clone());
            } else {
                all_ok = false;
                break;
            }
        }
        if !all_ok {
            continue;
        }

        // Every branch a range or a point: the ranges merge into
        // one, which enumerates the disjunction exactly and so
        // subsumes it. Ranges that provably do not overlap
        // concatenate; ones that may overlap go through a discrete
        // set, whose set semantics deduplicate. Either way the
        // generator is sealed and unique, and the disjunction stops
        // being a filter.
        if let Some(ctors) = merged_range_ctors(&sub_gens) {
            let elem_t = pat.type_();
            let exp = if ranges_disjoint(&ctors) {
                range_scan_exp(&elem_t, ctors, ordered)
            } else {
                range_set_scan_exp(&elem_t, ctors, ordered)
            };
            let mut free: BTreeSet<String> = BTreeSet::new();
            for g in &sub_gens {
                free.extend(g.free_pats.iter().cloned());
            }
            cache.add(
                pat_name.to_string(),
                Generator::new(
                    pat.clone(),
                    exp,
                    Cardinality::Finite,
                    free,
                    true,
                    true,
                    vec![c.clone()],
                ),
            );
            return true;
        }

        // Build `Bag.concat [g1.exp, g2.exp, ...]` (or
        // `List.concat …`).
        let elem_t = pat.type_();
        let coll_t = if ordered {
            Rc::new(Type::List(elem_t.clone()))
        } else {
            Rc::new(Type::Bag(elem_t.clone()))
        };
        let list_of_coll_t = Rc::new(Type::List(Rc::new((*coll_t).clone())));
        let exps: Vec<Expr> = sub_gens.iter().map(|g| g.exp.clone()).collect();
        let arg_list = Expr::List(list_of_coll_t.clone(), exps);
        let concat_fn = if ordered {
            BuiltInFunction::ListConcat
        } else {
            BuiltInFunction::BagConcat
        };
        let fn_t = Rc::new(Type::Fn(list_of_coll_t, coll_t.clone()));
        let fn_lit = Expr::Literal(fn_t, Val::Fn(concat_fn));
        let exp = Expr::Apply(
            coll_t,
            Box::new(fn_lit),
            Box::new(arg_list),
            Span::new(""),
        );

        let mut free: BTreeSet<String> = BTreeSet::new();
        for g in &sub_gens {
            for n in &g.free_pats {
                free.insert(n.clone());
            }
        }

        let generator = Generator::new(
            pat.clone(),
            exp,
            Cardinality::Finite,
            free,
            false, // not unique — branches may overlap
            false, // unsealed: composite
            vec![c.clone()],
        );
        cache.add(pat_name.to_string(), generator);
        return true;
    }
    false
}

/// The range constructors behind a disjunction's branch
/// generators, or `None` where a branch is neither a range nor a
/// point.
fn merged_range_ctors(gens: &[Generator]) -> Option<Vec<Expr>> {
    let mut ctors = Vec::new();
    for g in gens {
        ctors.extend(range_ctors(&g.exp)?);
    }
    Some(ctors)
}

/// The range constructors a generator's collection is made of: the
/// items of a `Range.flatten`, or the one value of a point, which
/// is the range `POINT v`.
fn range_ctors(exp: &Expr) -> Option<Vec<Expr>> {
    // An unordered scan takes a bag of the list the range gives.
    if let Expr::Apply(_, f, arg, _) = exp
        && as_builtin_fn(f) == Some(BuiltInFunction::BagFromList)
    {
        return range_ctors(arg);
    }
    match exp {
        Expr::Apply(_, f, arg, _)
            if as_builtin_fn(f) == Some(BuiltInFunction::RangeFlatten) =>
        {
            match arg.as_ref() {
                Expr::List(_, items) => Some(items.clone()),
                _ => None,
            }
        }
        Expr::List(_, items) if items.len() == 1 => {
            Some(vec![point_ctor(&items[0])])
        }
        _ => None,
    }
}

/// Builds `POINT v`, the range of one value.
fn point_ctor(v: &Expr) -> Expr {
    let elem_t = v.type_();
    let range_t = range_type(&elem_t);
    Expr::Apply(
        range_t.clone(),
        Box::new(Expr::Literal(
            Rc::new(Type::Fn(elem_t, range_t)),
            Val::Fn(BuiltInFunction::RangePoint),
        )),
        Box::new(v.clone()),
        Span::new(""),
    )
}

fn range_type(elem_t: &Rc<Type>) -> Rc<Type> {
    Rc::new(Type::Data("range".to_string(), vec![elem_t.clone()]))
}

/// Builds `Range.flatten [ctors]`, the values of ranges that do
/// not overlap, in the order they are written.
fn range_scan_exp(elem_t: &Rc<Type>, ctors: Vec<Expr>, ordered: bool) -> Expr {
    let ranges_t = Rc::new(Type::List(range_type(elem_t)));
    let list_t = Rc::new(Type::List(elem_t.clone()));
    let flatten = Expr::Apply(
        list_t.clone(),
        Box::new(Expr::Literal(
            Rc::new(Type::Fn(ranges_t.clone(), list_t.clone())),
            Val::Fn(BuiltInFunction::RangeFlatten),
        )),
        Box::new(Expr::List(ranges_t, ctors)),
        Span::new(""),
    );
    if ordered {
        return flatten;
    }
    as_bag(flatten, elem_t)
}

/// Builds `Range.toList (Range.discreteSetOf [ctors])`, the values
/// of ranges that may overlap, which the set deduplicates.
fn range_set_scan_exp(
    elem_t: &Rc<Type>,
    ctors: Vec<Expr>,
    ordered: bool,
) -> Expr {
    let ranges_t = Rc::new(Type::List(range_type(elem_t)));
    let set_t =
        Rc::new(Type::Data("discrete_set".to_string(), vec![elem_t.clone()]));
    let set = Expr::Apply(
        set_t.clone(),
        Box::new(Expr::Literal(
            Rc::new(Type::Fn(ranges_t.clone(), set_t.clone())),
            Val::Fn(BuiltInFunction::RangeDsOf),
        )),
        Box::new(Expr::List(ranges_t, ctors)),
        Span::new(""),
    );
    let (out_t, f) = if ordered {
        (Type::List(elem_t.clone()), BuiltInFunction::RangeToList)
    } else {
        (Type::Bag(elem_t.clone()), BuiltInFunction::RangeToBag)
    };
    let out_t = Rc::new(out_t);
    Expr::Apply(
        out_t.clone(),
        Box::new(Expr::Literal(
            Rc::new(Type::Fn(set_t, out_t.clone())),
            Val::Fn(f),
        )),
        Box::new(set),
        Span::new(""),
    )
}

/// Wraps a list as a bag, which is what an unordered scan takes.
fn as_bag(list: Expr, elem_t: &Rc<Type>) -> Expr {
    let list_t = list.type_();
    let bag_t = Rc::new(Type::Bag(elem_t.clone()));
    Expr::Apply(
        bag_t.clone(),
        Box::new(Expr::Literal(
            Rc::new(Type::Fn(list_t, bag_t.clone())),
            Val::Fn(BuiltInFunction::BagFromList),
        )),
        Box::new(list),
        Span::new(""),
    )
}

/// One range constructor's endpoints, for the disjointness test.
struct Endpoints {
    lo: i128,
    hi: i128,
    lo_open: bool,
    hi_open: bool,
}

/// Returns whether the ranges provably do not overlap: every
/// endpoint an integer literal and, in order of lower endpoint,
/// each range strictly below the next. Touching closed endpoints
/// count as overlapping.
fn ranges_disjoint(ctors: &[Expr]) -> bool {
    let mut eps = Vec::with_capacity(ctors.len());
    for c in ctors {
        match ctor_endpoints(c) {
            Some(ep) => eps.push(ep),
            None => return false,
        }
    }
    eps.sort_by(|a, b| a.lo.cmp(&b.lo).then(b.lo_open.cmp(&a.lo_open)));
    for w in eps.windows(2) {
        let (a, b) = (&w[0], &w[1]);
        if a.hi > b.lo {
            return false;
        }
        if a.hi == b.lo && !a.hi_open && !b.lo_open {
            return false;
        }
    }
    true
}

/// A constructor's literal endpoints.
fn ctor_endpoints(c: &Expr) -> Option<Endpoints> {
    let Expr::Apply(_, f, arg, _) = c else {
        return None;
    };
    let ctor = as_builtin_fn(f)?;
    if ctor == BuiltInFunction::RangePoint {
        let v = int_literal(arg)?;
        return Some(Endpoints {
            lo: v,
            hi: v,
            lo_open: false,
            hi_open: false,
        });
    }
    let Expr::Tuple(_, args) = arg.as_ref() else {
        return None;
    };
    let [lo, hi] = args.as_slice() else {
        return None;
    };
    let (lo_open, hi_open) = match ctor {
        BuiltInFunction::RangeClosed => (false, false),
        BuiltInFunction::RangeClosedOpen => (false, true),
        BuiltInFunction::RangeOpen => (true, true),
        BuiltInFunction::RangeOpenClosed => (true, false),
        _ => return None,
    };
    Some(Endpoints {
        lo: int_literal(lo)?,
        hi: int_literal(hi)?,
        lo_open,
        hi_open,
    })
}

fn int_literal(e: &Expr) -> Option<i128> {
    match e {
        Expr::Literal(_, Val::Int(n)) => Some(*n as i128),
        _ => None,
    }
}

/// Flattens `a orelse b orelse c …` into `[a, b, c, …]`.
/// Returns a single-element list if `expr` isn't an orelse.
pub(crate) fn split_orelse(expr: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    push_orelse(expr, &mut out);
    out
}

fn push_orelse(expr: &Expr, out: &mut Vec<Expr>) {
    if let Some((lhs, rhs)) = call2_args(expr, &[BuiltInFunction::BoolOrElse]) {
        push_orelse(lhs, out);
        push_orelse(rhs, out);
    } else {
        out.push(expr.clone());
    }
}

// ---------------------------------------------------------------------------
// Bound extraction
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Bound {
    bound: Expr,
    /// `true` for strict (`>`, `<`); `false` for inclusive (`>=`, `<=`).
    strict: bool,
}

fn is_bound_constraint(constraint: &Expr, pat_name: &str) -> bool {
    try_isolate_bound(constraint, pat_name).is_some()
        || !range_contains_bounds(constraint, pat_name).is_empty()
}

/// If `c` is `Range.contains range value` (curried, i.e.
/// `Apply(Apply(Range.contains, range), value)`) where `value` is exactly the
/// pattern `pat_name`, returns the range constructor application (e.g.
/// `CLOSED (a, b)` or `AT_LEAST a`); otherwise `None`. `pat elem [a..b]`
/// desugars to this form.
fn range_contains_range<'a>(c: &'a Expr, pat_name: &str) -> Option<&'a Expr> {
    let Expr::Apply(_, outer_fn, value, _) = c else {
        return None;
    };
    if !references(value, pat_name) {
        return None;
    }
    let Expr::Apply(_, contains_fn, range, _) = outer_fn.as_ref() else {
        return None;
    };
    if as_builtin_fn(contains_fn) != Some(BuiltInFunction::RangeContains) {
        return None;
    }
    Some(range)
}

/// The lower/upper bounds implied by a `Range.contains range pat` constraint.
/// A two-sided range (e.g. `CLOSED (a, b)`) yields both bounds; a one-sided
/// range (e.g. `AT_LEAST a`) yields one; `ALL` and a point yield none. Each
/// entry is `(is_lower, bound)`.
fn range_contains_bounds(c: &Expr, pat_name: &str) -> Vec<(bool, Bound)> {
    match range_contains_range(c, pat_name) {
        Some(range) => range_bounds(range),
        None => Vec::new(),
    }
}

/// The lower/upper bounds a range constructor implies. Each entry is
/// `(is_lower, bound)`; see [`range_contains_bounds`].
fn range_bounds(range: &Expr) -> Vec<(bool, Bound)> {
    use BuiltInFunction as B;
    let Expr::Apply(_, ctor_fn, ctor_arg, _) = range else {
        return Vec::new();
    };
    let Some(ctor) = as_builtin_fn(ctor_fn) else {
        return Vec::new();
    };
    match ctor {
        B::RangeClosed
        | B::RangeClosedOpen
        | B::RangeOpen
        | B::RangeOpenClosed => {
            let Expr::Tuple(_, args) = ctor_arg.as_ref() else {
                return Vec::new();
            };
            if args.len() != 2 {
                return Vec::new();
            }
            let lo_strict = matches!(ctor, B::RangeOpen | B::RangeOpenClosed);
            let hi_strict = matches!(ctor, B::RangeOpen | B::RangeClosedOpen);
            vec![
                (
                    true,
                    Bound {
                        bound: args[0].clone(),
                        strict: lo_strict,
                    },
                ),
                (
                    false,
                    Bound {
                        bound: args[1].clone(),
                        strict: hi_strict,
                    },
                ),
            ]
        }
        B::RangeAtLeast | B::RangeGreaterThan => vec![(
            true,
            Bound {
                bound: (**ctor_arg).clone(),
                strict: ctor == B::RangeGreaterThan,
            },
        )],
        B::RangeAtMost | B::RangeLessThan => vec![(
            false,
            Bound {
                bound: (**ctor_arg).clone(),
                strict: ctor == B::RangeLessThan,
            },
        )],
        _ => Vec::new(),
    }
}

/// Returns whether `constraint` references an unbounded sibling pattern
/// other than `pat_name` (e.g. `x < y` when `y` is also unbounded). Such
/// a constraint cannot be subsumed by `pat_name`'s finite range; it must
/// remain as a filter.
fn references_other_sibling(
    constraint: &Expr,
    pat_name: &str,
    unbounded_siblings: &BTreeSet<String>,
) -> bool {
    free_names_in(constraint)
        .iter()
        .any(|n| n != pat_name && unbounded_siblings.contains(n))
}

/// How much we like the shape of a bound. The variants are in order of
/// preference; see [`choose_bound`].
#[derive(Copy, Clone, PartialEq)]
enum Preference {
    /// Mentions only variables that are bound already.
    Grounded,
    /// Mentions no variables.
    Constant,
    /// Anything.
    Any,
}

/// Returns whether a bound expression is acceptable at a preference.
fn acceptable(
    bound: &Expr,
    ungrounded: &BTreeSet<String>,
    preference: Preference,
) -> bool {
    let free = free_names_in(bound);
    match preference {
        Preference::Grounded => {
            !free.is_empty() && free.iter().all(|n| !ungrounded.contains(n))
        }
        Preference::Constant => free.is_empty(),
        Preference::Any => true,
    }
}

/// Chooses a bound, in order of preference.
///
/// First, a bound that mentions only variables that are bound already,
/// as `x` is in `from x in [3, 5, 7], y where y < x`. Such a bound
/// generates `y` afresh for each `x`, which is tighter than any constant
/// bound, and it cannot make a cycle, because `x` does not wait on `y`.
///
/// Failing that, a constant bound. It is independent of every other
/// variable, and so is always safe.
///
/// Failing that, a bound of any shape, which may mention a variable that
/// is itself waiting for a generator. Such a bound may make a cycle that
/// generator scheduling cannot break, but it is better than no bound at
/// all.
fn choose_bound(
    pat_name: &str,
    constraints: &[Expr],
    ungrounded: &BTreeSet<String>,
    finder: fn(&str, &[Expr], &BTreeSet<String>, Preference) -> Option<Bound>,
) -> Option<Bound> {
    for preference in
        [Preference::Grounded, Preference::Constant, Preference::Any]
    {
        if let Some(b) = finder(pat_name, constraints, ungrounded, preference) {
            return Some(b);
        }
    }
    None
}

/// Returns `(bound, strict)` for the pattern's lower bound. Strict means
/// `>` (exclusive).
fn lower_bound(
    pat_name: &str,
    constraints: &[Expr],
    ungrounded: &BTreeSet<String>,
) -> Option<Bound> {
    choose_bound(pat_name, constraints, ungrounded, lower_bound1)
}

/// Helper for [`lower_bound`]: returns the first bound acceptable at
/// `preference`.
fn lower_bound1(
    pat_name: &str,
    constraints: &[Expr],
    ungrounded: &BTreeSet<String>,
    preference: Preference,
) -> Option<Bound> {
    for c in constraints {
        if let Some((op, rhs)) = try_isolate_bound(c, pat_name)
            && (op == BuiltInFunction::IntGt || op == BuiltInFunction::IntGe)
            && acceptable(&rhs, ungrounded, preference)
        {
            return Some(Bound {
                bound: rhs,
                strict: op == BuiltInFunction::IntGt,
            });
        }
        // `pat elem [a..b]` (a finite or lower-bounded range) implies a lower
        // bound on `pat`.
        if let Some((_, bound)) = range_contains_bounds(c, pat_name)
            .into_iter()
            .find(|(is_lower, b)| {
                *is_lower && acceptable(&b.bound, ungrounded, preference)
            })
        {
            return Some(bound);
        }
    }
    None
}

/// Returns `(bound, strict)` for the pattern's upper bound. Strict
/// means `<` (exclusive). Analogous to [`lower_bound`].
fn upper_bound(
    pat_name: &str,
    constraints: &[Expr],
    ungrounded: &BTreeSet<String>,
) -> Option<Bound> {
    choose_bound(pat_name, constraints, ungrounded, upper_bound1)
}

/// Helper for [`upper_bound`]: returns the first bound acceptable at
/// `preference`.
fn upper_bound1(
    pat_name: &str,
    constraints: &[Expr],
    ungrounded: &BTreeSet<String>,
    preference: Preference,
) -> Option<Bound> {
    for c in constraints {
        if let Some((op, rhs)) = try_isolate_bound(c, pat_name)
            && (op == BuiltInFunction::IntLt || op == BuiltInFunction::IntLe)
            && acceptable(&rhs, ungrounded, preference)
        {
            return Some(Bound {
                bound: rhs,
                strict: op == BuiltInFunction::IntLt,
            });
        }
        // `pat elem [a..b]` (a finite or upper-bounded range) implies an upper
        // bound on `pat`.
        if let Some((_, bound)) = range_contains_bounds(c, pat_name)
            .into_iter()
            .find(|(is_lower, b)| {
                !*is_lower && acceptable(&b.bound, ungrounded, preference)
            })
        {
            return Some(bound);
        }
    }
    None
}

/// Names a comparison by its `int` instance.
///
/// A comparison in a polymorphic function's body keeps the generic
/// operator -- `fun le (x, y) = x <= y` is an `'a * 'a -> bool` -- and a
/// call that instantiates it at `int` inlines that body unchanged. The
/// bound it states is the same one either way, and the caller has already
/// established that the pattern is an `int`.
fn int_comparison(f: BuiltInFunction) -> Option<BuiltInFunction> {
    Some(match f {
        BuiltInFunction::GGe | BuiltInFunction::IntGe => BuiltInFunction::IntGe,
        BuiltInFunction::GGt | BuiltInFunction::IntGt => BuiltInFunction::IntGt,
        BuiltInFunction::GLe | BuiltInFunction::IntLe => BuiltInFunction::IntLe,
        BuiltInFunction::GLt | BuiltInFunction::IntLt => BuiltInFunction::IntLt,
        _ => return None,
    })
}

/// Normalises a comparison constraint into the form `pat op expr`,
/// where `op` is one of the `Int{Lt,Le,Gt,Ge}` built-ins and
/// `expr` doesn't reference `pat_name`. Returns `None` if the
/// constraint isn't a comparison or `pat_name` doesn't appear in a
/// shape we can isolate.
///
/// Supported shapes (with `k` not referencing `pat_name`):
///   * `pat`              isolated already
///   * `pat + k` or `k + pat`  (subtract `k` from the other side)
///   * `pat - k`               (add `k` to the other side)
fn try_isolate_bound(
    c: &Expr,
    pat_name: &str,
) -> Option<(BuiltInFunction, Expr)> {
    let ops = [
        BuiltInFunction::GGe,
        BuiltInFunction::GGt,
        BuiltInFunction::GLe,
        BuiltInFunction::GLt,
        BuiltInFunction::IntGe,
        BuiltInFunction::IntGt,
        BuiltInFunction::IntLe,
        BuiltInFunction::IntLt,
    ];
    let (lhs, rhs, op) = call2_args_op(c, &ops)?;
    let op = int_comparison(op)?;
    // Try lhs-side: `(pat ± k) op rhs` ⇒ `pat op (rhs ∓ k)`.
    if let Some(adj) = isolate_pat_offset(lhs, pat_name)
        && !free_names_in(rhs).contains(pat_name)
    {
        let new_rhs = apply_offset(rhs.clone(), adj);
        return Some((op, new_rhs));
    }
    // Try rhs-side: `lhs op (pat ± k)` ⇒ flip op, then move offset:
    // `lhs op (pat ± k)` ⇔ `(pat ± k) flip(op) lhs` ⇒
    //   `pat flip(op) (lhs ∓ k)`.
    if let Some(adj) = isolate_pat_offset(rhs, pat_name)
        && !free_names_in(lhs).contains(pat_name)
    {
        let flipped = match op {
            BuiltInFunction::IntLt => BuiltInFunction::IntGt,
            BuiltInFunction::IntLe => BuiltInFunction::IntGe,
            BuiltInFunction::IntGt => BuiltInFunction::IntLt,
            BuiltInFunction::IntGe => BuiltInFunction::IntLe,
            _ => return None,
        };
        let new_rhs = apply_offset(lhs.clone(), adj);
        return Some((flipped, new_rhs));
    }
    None
}

/// If `side` has the form `pat`, `pat + k`, `k + pat`, or `pat - k`
/// (with `k` not referencing `pat_name`), returns the offset `delta`
/// that, when added to *the other side* of the comparison, isolates
/// `pat`. `pat` alone gives `Some(IntLit(0))`. Returns `None` when
/// pat is missing or appears in a shape we can't invert (e.g. `k -
/// pat`, multiplication).
fn isolate_pat_offset(side: &Expr, pat_name: &str) -> Option<Expr> {
    if let Expr::Identifier(_, n) = side
        && n == pat_name
    {
        return Some(int_lit(0));
    }
    let (a, b, op) = call2_args_op(
        side,
        &[BuiltInFunction::IntPlus, BuiltInFunction::IntMinus],
    )?;
    let a_is_pat = matches!(a, Expr::Identifier(_, n) if n == pat_name);
    let b_is_pat = matches!(b, Expr::Identifier(_, n) if n == pat_name);
    match op {
        BuiltInFunction::IntPlus => {
            // pat + k: subtract k from the other side ⇒ delta = -k.
            if a_is_pat && !free_names_in(b).contains(pat_name) {
                return Some(negate_int(b.clone()));
            }
            // k + pat: same.
            if b_is_pat && !free_names_in(a).contains(pat_name) {
                return Some(negate_int(a.clone()));
            }
            None
        }
        BuiltInFunction::IntMinus => {
            // pat - k: add k to the other side ⇒ delta = +k.
            if a_is_pat && !free_names_in(b).contains(pat_name) {
                return Some(b.clone());
            }
            // k - pat: would require flipping the comparison; skip.
            None
        }
        _ => None,
    }
}

/// `expr + delta`, simplified when `delta` is the literal `0` and
/// written as a subtraction when it is a negation: adding `0 - k`
/// is subtracting `k`, and that is how it reads.
fn apply_offset(expr: Expr, delta: Expr) -> Expr {
    if matches!(&delta, Expr::Literal(_, Val::Int(0))) {
        return expr;
    }
    if let Some((a, b, BuiltInFunction::IntMinus)) =
        call2_args_op(&delta, &[BuiltInFunction::IntMinus])
        && matches!(a, Expr::Literal(_, Val::Int(0)))
    {
        return binop_int(BuiltInFunction::IntMinus, expr, b.clone());
    }
    binop_int(BuiltInFunction::IntPlus, expr, delta)
}

fn negate_int(expr: Expr) -> Expr {
    binop_int(BuiltInFunction::IntMinus, int_lit(0), expr)
}

// ---------------------------------------------------------------------------
// Core-expression helpers
// ---------------------------------------------------------------------------

/// Matches `Apply(_, Literal(Fn(f)), Tuple(_, [a, b]))` where `f` is
/// one of the built-ins in `ops`. Returns `(a, b)` on a match.
fn call2_args<'a>(
    expr: &'a Expr,
    ops: &[BuiltInFunction],
) -> Option<(&'a Expr, &'a Expr)> {
    call2_args_op(expr, ops).map(|(a, b, _)| (a, b))
}

fn call2_args_op<'a>(
    expr: &'a Expr,
    ops: &[BuiltInFunction],
) -> Option<(&'a Expr, &'a Expr, BuiltInFunction)> {
    if let Expr::Apply(_, f, arg, _) = expr
        && let Expr::Literal(_, Val::Fn(builtin)) = f.as_ref()
        && ops.contains(builtin)
        && let Expr::Tuple(_, args) = arg.as_ref()
        && args.len() == 2
    {
        return Some((&args[0], &args[1], *builtin));
    }
    None
}

/// True if `expr` is a direct reference to the pattern named `name`,
/// or contains it transitively. For now only the direct case is
/// handled — Phase 1 doesn't need offset detection.
fn references(expr: &Expr, name: &str) -> bool {
    matches!(expr, Expr::Identifier(_, n) if n == name)
}

/// Whether a tuple has the name as a component, at any depth.
fn tuple_mentions(expr: &Expr, name: &str) -> bool {
    match expr {
        Expr::Tuple(_, args) => args
            .iter()
            .any(|a| references(a, name) || tuple_mentions(a, name)),
        _ => false,
    }
}

/// If `expr` is `String.isPrefix p s` (curried, i.e.
/// `Apply(Apply(StringIsPrefix, p), s)`) where `p` references the
/// named pattern, returns `s`.
///
/// `String.isPrefix` may surface in either of two shapes depending
/// on whether the inliner has already lowered structure-field
/// access to a `Literal(Fn(...))`:
///
///   1. `Apply(Apply(Literal(Fn(StringIsPrefix)), p), s)`
///   2. `Apply(Apply(Apply(RecordSelector(_, slot),
///                         Identifier("String")), p), s)`
///
/// At the point the Expander runs (immediately after resolution,
/// before `inliner::inline_decl`), shape 2 is the common form;
/// shape 1 will appear once we move the Expander after inlining.
fn is_string_prefix_call<'a>(
    expr: &'a Expr,
    pat_name: &str,
) -> Option<&'a Expr> {
    let Expr::Apply(_, outer_fn, s, _) = expr else {
        return None;
    };
    let Expr::Apply(_, mid_fn, p, _) = outer_fn.as_ref() else {
        return None;
    };
    if !references(p, pat_name) {
        return None;
    }
    if as_builtin_fn(mid_fn) == Some(BuiltInFunction::StringIsPrefix) {
        return Some(s);
    }
    None
}

/// Resolves an expression to a built-in function, if it is one. Handles
/// both an inlined literal and a record-selector application against a
/// builtin structure (e.g. `Apply(RecordSelector(_, slot),
/// Identifier("String"))`).
fn as_builtin_fn(expr: &Expr) -> Option<BuiltInFunction> {
    match expr {
        Expr::Literal(_, Val::Fn(f)) => Some(*f),
        Expr::Apply(_, f, a, _) => {
            if let Expr::RecordSelector(t, slot) = f.as_ref()
                && let Expr::Identifier(_, struct_name) = a.as_ref()
                && let Type::Fn(record_t, _) = t.as_ref()
                && let Some(field_name) = record_t.field_name(*slot)
            {
                return lookup_struct_field(struct_name, field_name);
            }
            None
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Infinite-range scan rewriting (RangePushdown)
// ---------------------------------------------------------------------------

/// Returns whether a collection is an infinite single-constructor range
/// list, such as `[1..]`.
pub fn is_infinite_range(src: &Expr) -> bool {
    match_infinite_range_scan(src).is_some()
}

/// If `src` is `Range.flatten [<single infinite constructor>]`, returns
/// `(lower, strict, arg)`: whether the implied bound is a lower bound,
/// whether it is strict, and the range endpoint expression. Finite
/// constructors (POINT, CLOSED, …) and multi-item lists return `None`.
fn match_infinite_range_scan(src: &Expr) -> Option<(bool, bool, Expr)> {
    let Expr::Apply(_, f, arg, _) = src else {
        return None;
    };
    if as_builtin_fn(f) != Some(BuiltInFunction::RangeFlatten) {
        return None;
    }
    let Expr::List(_, items) = arg.as_ref() else {
        return None;
    };
    if items.len() != 1 {
        return None;
    }
    let Expr::Apply(_, ctor_fn, ctor_arg, _) = &items[0] else {
        return None;
    };
    let Expr::Literal(_, Val::Fn(ctor)) = ctor_fn.as_ref() else {
        return None;
    };
    match ctor {
        BuiltInFunction::RangeAtLeast => {
            Some((true, false, (**ctor_arg).clone()))
        }
        BuiltInFunction::RangeGreaterThan => {
            Some((true, true, (**ctor_arg).clone()))
        }
        BuiltInFunction::RangeAtMost => {
            Some((false, false, (**ctor_arg).clone()))
        }
        BuiltInFunction::RangeLessThan => {
            Some((false, true, (**ctor_arg).clone()))
        }
        _ => None,
    }
}

/// Builds `name <op> bound` where `<op>` is the lower/upper, strict/
/// non-strict comparison for the element type. Supports int and char.
fn compare_for_type(
    elem_t: &Rc<Type>,
    lower: bool,
    strict: bool,
    name: &str,
    bound: Expr,
) -> Option<Expr> {
    let op = match elem_t.as_ref() {
        Type::Primitive(PrimitiveType::Int) => match (lower, strict) {
            (true, false) => BuiltInFunction::IntGe,
            (true, true) => BuiltInFunction::IntGt,
            (false, false) => BuiltInFunction::IntLe,
            (false, true) => BuiltInFunction::IntLt,
        },
        Type::Primitive(PrimitiveType::Char) => match (lower, strict) {
            (true, false) => BuiltInFunction::CharGe,
            (true, true) => BuiltInFunction::CharGt,
            (false, false) => BuiltInFunction::CharLe,
            (false, true) => BuiltInFunction::CharLt,
        },
        _ => return None,
    };
    let id = Expr::Identifier(elem_t.clone(), name.to_string());
    let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let pair_t = Rc::new(Type::Tuple(vec![elem_t.clone(), elem_t.clone()]));
    let fn_t = Rc::new(Type::Fn(pair_t.clone(), bool_t.clone()));
    let fn_expr = Expr::Literal(fn_t, Val::Fn(op));
    let arg = Expr::Tuple(pair_t, vec![id, bound]);
    Some(Expr::Apply(
        bool_t,
        Box::new(fn_expr),
        Box::new(arg),
        Span::new(""),
    ))
}

/// The comparison a one-sided range-list scan implies for its variable,
/// as morel-go's `impliedRangeBound` writes it: `x >= 1` for `x` in
/// `[1..]`.
pub(crate) fn implied_range_bound(
    src: &Expr,
    elem_t: &Rc<Type>,
    name: &str,
) -> Option<Expr> {
    let (lower, strict, end) = match_infinite_range_scan(src)?;
    compare_for_type(elem_t, lower, strict, name, end)
}

/// Folds the tightest literal bound on `name` among `conjuncts` into a
/// one-sided range, as morel-go's `pushBound` does: `[1..]` under
/// `x < 5` is `[1..^5]`. Returns the finite range and the index of the
/// conjunct it consumed; `None` if no conjunct bounds the open side, or
/// if the tightest one would make the range obviously empty.
pub(crate) fn tighten_range(
    src: &Expr,
    elem_t: &Rc<Type>,
    name: &str,
    conjuncts: &[Expr],
) -> Option<(Expr, usize)> {
    let (scan_lower, scan_strict, scan_end) = match_infinite_range_scan(src)?;
    // The scan bounds one side; the bound to find is on the other.
    let want_upper = scan_lower;
    let mut best: Option<(bool, Expr, usize)> = None;
    for (i, c) in conjuncts.iter().enumerate() {
        let Some((lower, strict, end)) = extract_literal_bound(c, name) else {
            continue;
        };
        if lower == want_upper {
            continue;
        }
        if let Some((best_strict, best_end, _)) = &best {
            let cmp = compare_literals(&end, best_end);
            let tighter = if want_upper {
                cmp.is_lt() || (cmp.is_eq() && strict && !best_strict)
            } else {
                cmp.is_gt() || (cmp.is_eq() && strict && !best_strict)
            };
            if !tighter {
                continue;
            }
        }
        best = Some((strict, end, i));
    }
    let (strict, end, i) = best?;
    if is_scalar_literal(&scan_end) {
        let cmp = compare_literals(&end, &scan_end);
        if (want_upper && cmp.is_lt()) || (!want_upper && cmp.is_gt()) {
            return None;
        }
    }
    let ((lo, lo_incl), (hi, hi_incl)) = if scan_lower {
        ((scan_end, !scan_strict), (end, !strict))
    } else {
        ((end, !strict), (scan_end, !scan_strict))
    };
    let ctor = match (lo_incl, hi_incl) {
        (true, true) => BuiltInFunction::RangeClosed,
        (true, false) => BuiltInFunction::RangeClosedOpen,
        (false, true) => BuiltInFunction::RangeOpenClosed,
        (false, false) => BuiltInFunction::RangeOpen,
    };
    Some((build_finite_range_scan(src, elem_t, ctor, lo, hi), i))
}

/// Orders two int or char literals; others compare equal.
fn compare_literals(a: &Expr, b: &Expr) -> Ordering {
    match (a, b) {
        (Expr::Literal(_, Val::Int(x)), Expr::Literal(_, Val::Int(y))) => {
            x.cmp(y)
        }
        (Expr::Literal(_, Val::Char(x)), Expr::Literal(_, Val::Char(y))) => {
            x.cmp(y)
        }
        _ => Ordering::Equal,
    }
}

/// If `conjunct` is a comparison `name <op> lit` (or `lit <op> name`)
/// against an int/char literal, returns `(lower, strict, literal_expr)`:
/// whether it bounds `name` from below, whether the bound is strict, and
/// the literal endpoint.
fn extract_literal_bound(
    conjunct: &Expr,
    pat_name: &str,
) -> Option<(bool, bool, Expr)> {
    let ops = [
        BuiltInFunction::IntLt,
        BuiltInFunction::IntLe,
        BuiltInFunction::IntGt,
        BuiltInFunction::IntGe,
        BuiltInFunction::CharLt,
        BuiltInFunction::CharLe,
        BuiltInFunction::CharGt,
        BuiltInFunction::CharGe,
    ];
    let (a, b, op) = call2_args_op(conjunct, &ops)?;
    let a_is_pat = matches!(a, Expr::Identifier(_, n) if n == pat_name);
    let b_is_pat = matches!(b, Expr::Identifier(_, n) if n == pat_name);
    if a_is_pat && is_scalar_literal(b) {
        let (lower, strict) = bound_direction(op);
        return Some((lower, strict, b.clone()));
    }
    if b_is_pat && is_scalar_literal(a) {
        let (lower, strict) = bound_direction(flip_cmp(op));
        return Some((lower, strict, a.clone()));
    }
    None
}

/// Returns `(lower, strict)` for a `pat <op> c` comparison: `lower` true
/// if it bounds the pattern from below (`>`, `>=`).
fn bound_direction(op: BuiltInFunction) -> (bool, bool) {
    match op {
        BuiltInFunction::IntLt | BuiltInFunction::CharLt => (false, true),
        BuiltInFunction::IntLe | BuiltInFunction::CharLe => (false, false),
        BuiltInFunction::IntGt | BuiltInFunction::CharGt => (true, true),
        BuiltInFunction::IntGe | BuiltInFunction::CharGe => (true, false),
        _ => unreachable!(),
    }
}

/// The comparison with its operands swapped (`a < b` ⇔ `b > a`).
fn flip_cmp(op: BuiltInFunction) -> BuiltInFunction {
    match op {
        BuiltInFunction::IntLt => BuiltInFunction::IntGt,
        BuiltInFunction::IntLe => BuiltInFunction::IntGe,
        BuiltInFunction::IntGt => BuiltInFunction::IntLt,
        BuiltInFunction::IntGe => BuiltInFunction::IntLe,
        BuiltInFunction::CharLt => BuiltInFunction::CharGt,
        BuiltInFunction::CharLe => BuiltInFunction::CharGe,
        BuiltInFunction::CharGt => BuiltInFunction::CharLt,
        BuiltInFunction::CharGe => BuiltInFunction::CharLe,
        other => other,
    }
}

fn is_scalar_literal(e: &Expr) -> bool {
    matches!(e, Expr::Literal(_, Val::Int(_) | Val::Char(_)))
}

/// Rebuilds an infinite range scan's source as a finite two-sided range,
/// reusing the original `Range.flatten` wrapper and replacing the single
/// list constructor with `ctor (lo, hi)`.
fn build_finite_range_scan(
    src: &Expr,
    elem_t: &Rc<Type>,
    ctor: BuiltInFunction,
    lo: Expr,
    hi: Expr,
) -> Expr {
    let Expr::Apply(result_t, flatten_fn, list, span) = src else {
        unreachable!("match_infinite_range_scan guarantees Apply")
    };
    let Expr::List(list_t, items) = list.as_ref() else {
        unreachable!("match_infinite_range_scan guarantees a list")
    };
    let range_t = items[0].type_();
    let pair_t = Rc::new(Type::Tuple(vec![elem_t.clone(), elem_t.clone()]));
    let fn_t = Rc::new(Type::Fn(pair_t.clone(), range_t.clone()));
    let ctor_app = Expr::Apply(
        range_t,
        Box::new(Expr::Literal(fn_t, Val::Fn(ctor))),
        Box::new(Expr::Tuple(pair_t, vec![lo, hi])),
        span.clone(),
    );
    let new_list = Expr::List(list_t.clone(), vec![ctor_app]);
    Expr::Apply(
        result_t.clone(),
        flatten_fn.clone(),
        Box::new(new_list),
        span.clone(),
    )
}

/// Splits an `andalso`-rooted expression into its conjuncts. Anything
/// else is returned as a single-element vector.
pub fn split_conjuncts(expr: &Expr) -> Vec<Expr> {
    let mut out = Vec::new();
    push_conjuncts(expr, &mut out);
    out
}

fn push_conjuncts(expr: &Expr, out: &mut Vec<Expr>) {
    if let Some((lhs, rhs)) = call2_args(expr, &[BuiltInFunction::BoolAndAlso])
    {
        push_conjuncts(lhs, out);
        push_conjuncts(rhs, out);
    } else {
        out.push(expr.clone());
    }
}

// ---------------------------------------------------------------------------
// Mini Core builders — local to this module, intentionally narrow.
// ---------------------------------------------------------------------------

fn int_lit(n: i32) -> Expr {
    Expr::Literal(Rc::new(Type::Primitive(PrimitiveType::Int)), Val::Int(n))
}

fn binop_int(f: BuiltInFunction, a: Expr, b: Expr) -> Expr {
    let int_t = Rc::new(Type::Primitive(PrimitiveType::Int));
    let pair_t = Rc::new(Type::Tuple(vec![
        Rc::new((*int_t).clone()),
        Rc::new((*int_t).clone()),
    ]));
    let fn_t = Rc::new(Type::Fn(pair_t.clone(), int_t.clone()));
    let fn_expr = Expr::Literal(fn_t.clone(), Val::Fn(f));
    let arg = Expr::Tuple(pair_t, vec![a, b]);
    Expr::Apply(int_t, Box::new(fn_expr), Box::new(arg), Span::new(""))
}

fn call1(f: BuiltInFunction, a: Expr, result_t: Rc<Type>) -> Expr {
    let arg_t = a.type_();
    let fn_t = Rc::new(Type::Fn(arg_t, result_t.clone()));
    let fn_expr = Expr::Literal(fn_t, Val::Fn(f));
    Expr::Apply(result_t, Box::new(fn_expr), Box::new(a), Span::new(""))
}

fn call2(f: BuiltInFunction, a: Expr, b: Expr, result_t: Rc<Type>) -> Expr {
    let arg_t = Rc::new(Type::Tuple(vec![
        Rc::new((*a.type_()).clone()),
        Rc::new((*b.type_()).clone()),
    ]));
    let fn_t = Rc::new(Type::Fn(arg_t.clone(), result_t.clone()));
    let fn_expr = Expr::Literal(fn_t, Val::Fn(f));
    let arg = Expr::Tuple(arg_t, vec![a, b]);
    Expr::Apply(result_t, Box::new(fn_expr), Box::new(arg), Span::new(""))
}

#[allow(dead_code)]
fn unused_warn() -> BTreeSet<String> {
    // Suppress an "unused import" warning until the BTreeSet usage
    // shows up in a follow-up phase. (free_names_in already returns
    // a BTreeSet, so we use it indirectly.)
    BTreeSet::new()
}
