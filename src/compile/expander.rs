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

//! Two-phase predicate-inversion pipeline. Phase 1 of
//! hydromatic/morel#217.
//!
//! `expand_from(from_expr)` analyses `where`-conjuncts to derive a
//! generator for each unbounded pattern (i.e. each Scan over an
//! `Expr::Extent`), then rewrites the `from` so the unbounded
//! source becomes a real collection-scan and the conjuncts that
//! the generator subsumes are dropped from the surrounding `where`.
//!
//! Mirrors morel-java's `compile.Expander`, less the bits that
//! Phase 1 doesn't need (no outer-scope filtering, no recursive
//! function inlining, no case/exists/string-prefix).

use crate::compile::core::{
    Binding, Decl, Expr, Match, Pat, Step, StepEnv, StepKind, ValBind,
};
use crate::compile::generator::Cache;
use crate::compile::generators::{maybe_generator, split_conjuncts};
use crate::compile::library::BuiltInFunction;
use crate::compile::span::Span;
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::val::Val;
use std::collections::{HashMap, HashSet};

/// Map of let-bound function name → (parameter pattern, body
/// expression). Populated as `expand_decl` walks down through
/// nested `Let` expressions so that `maybe_function` can inline a
/// known function's body when it sees a constraint of the form
/// `f arg`.
pub type FnEnv = HashMap<String, (Pat, Expr)>;

/// Map of user-defined datatype name → its constructor names in
/// declaration order. Lets `finite_extent` enumerate values of
/// `Type::Data(name, _)` for constraint-free unbounded patterns
/// (e.g. `from c, d where c <> d` over a `Color`).
pub type DatatypeMap = HashMap<String, Vec<String>>;

/// Convenience wrapper for callers that don't have a function
/// environment available (e.g. the resolver, which calls this
/// before `expand_decl` runs the full tree-walk pass).
pub fn expand_from(expr: Expr, datatypes: &DatatypeMap) -> Expr {
    let env = FnEnv::new();
    expand_from_with(expr, &env, datatypes)
}

/// If `expr` is a `From`, `Exists`, or `Forall` containing one or
/// more Scans over Extents, rewrite it by deriving generators from
/// `where` clauses and using them as the scan sources. Otherwise
/// returns `expr` unchanged.
pub fn expand_from_with(
    expr: Expr,
    env: &FnEnv,
    datatypes: &DatatypeMap,
) -> Expr {
    match expr {
        Expr::From(t, steps) => {
            if !has_extent_scan(&steps) {
                return Expr::From(t, steps);
            }
            Expr::From(t, expand_steps(steps, env, datatypes))
        }
        Expr::Exists(t, steps) => {
            if !has_extent_scan(&steps) {
                return Expr::Exists(t, steps);
            }
            Expr::Exists(t, expand_steps(steps, env, datatypes))
        }
        Expr::Forall(t, steps) => {
            if !has_extent_scan(&steps) {
                return Expr::Forall(t, steps);
            }
            Expr::Forall(t, expand_steps(steps, env, datatypes))
        }
        _ => expr,
    }
}

/// Tree-walking pass that re-runs `expand_from_with` on every
/// `From`/`Exists`/`Forall` it encounters, with a `FnEnv` populated
/// from enclosing `let val rec ... = fn p => body` bindings. This
/// is the entry point used after the resolver finishes, so that
/// `maybe_function` can inline let-bound predicates that the
/// per-query passes inside `resolve_query` couldn't see.
pub fn expand_decl(decl: Decl, datatypes: &DatatypeMap) -> Decl {
    let env = FnEnv::new();
    walk_decl(decl, &env, datatypes)
}

fn walk_decl(decl: Decl, env: &FnEnv, datatypes: &DatatypeMap) -> Decl {
    match decl {
        Decl::NonRecVal(b) => {
            let mut b2 = (*b).clone();
            b2.expr = walk_expr(b2.expr, env, datatypes);
            Decl::NonRecVal(Box::new(b2))
        }
        Decl::RecVal(binds) => {
            let mut new_binds = Vec::with_capacity(binds.len());
            for mut b in binds {
                b.expr = walk_expr(b.expr, env, datatypes);
                new_binds.push(b);
            }
            Decl::RecVal(new_binds)
        }
        other => other,
    }
}

fn walk_expr(expr: Expr, env: &FnEnv, datatypes: &DatatypeMap) -> Expr {
    match expr {
        Expr::Let(t, decls, body) => {
            // Extend the environment with single-arg `fn` bindings
            // before recursing into the body.
            let mut env2 = env.clone();
            for d in &decls {
                collect_fn_bindings(d, &mut env2);
            }
            let new_decls: Vec<Decl> = decls
                .into_iter()
                .map(|d| walk_decl(d, &env2, datatypes))
                .collect();
            let new_body = Box::new(walk_expr(*body, &env2, datatypes));
            Expr::Let(t, new_decls, new_body)
        }
        Expr::From(_, _) | Expr::Exists(_, _) | Expr::Forall(_, _) => {
            // Recurse into nested expressions first (so inner
            // sub-queries also benefit from the env), then run the
            // expander on the resulting top-level expression.
            let inner = walk_query_steps(expr, env, datatypes);
            expand_from_with(inner, env, datatypes)
        }
        Expr::Apply(t, f, a, span) => Expr::Apply(
            t,
            Box::new(walk_expr(*f, env, datatypes)),
            Box::new(walk_expr(*a, env, datatypes)),
            span,
        ),
        Expr::Case(t, subject, arms, span) => Expr::Case(
            t,
            Box::new(walk_expr(*subject, env, datatypes)),
            arms.into_iter()
                .map(|m| Match {
                    pat: m.pat,
                    expr: walk_expr(m.expr, env, datatypes),
                })
                .collect(),
            span,
        ),
        Expr::Fn(t, arms, span) => Expr::Fn(
            t,
            arms.into_iter()
                .map(|m| Match {
                    pat: m.pat,
                    expr: walk_expr(m.expr, env, datatypes),
                })
                .collect(),
            span,
        ),
        Expr::Tuple(t, items) => Expr::Tuple(
            t,
            items
                .into_iter()
                .map(|e| walk_expr(e, env, datatypes))
                .collect(),
        ),
        Expr::List(t, items) => Expr::List(
            t,
            items
                .into_iter()
                .map(|e| walk_expr(e, env, datatypes))
                .collect(),
        ),
        Expr::Aggregate(t, e1, e2) => Expr::Aggregate(
            t,
            Box::new(walk_expr(*e1, env, datatypes)),
            Box::new(walk_expr(*e2, env, datatypes)),
        ),
        other => other,
    }
}

/// Walk inside a `From`/`Exists`/`Forall`'s steps so that
/// expressions embedded in `Where`, `Yield`, and other step kinds
/// get the same treatment. The query's outer wrapper is recreated.
fn walk_query_steps(expr: Expr, env: &FnEnv, datatypes: &DatatypeMap) -> Expr {
    let (kind, t, steps) = match expr {
        Expr::From(t, s) => ('f', t, s),
        Expr::Exists(t, s) => ('e', t, s),
        Expr::Forall(t, s) => ('a', t, s),
        other => return other,
    };
    let new_steps: Vec<Step> = steps
        .into_iter()
        .map(|s| {
            let new_kind = match s.kind {
                StepKind::Scan(p, source, cond) => StepKind::Scan(
                    p,
                    Box::new(walk_expr(*source, env, datatypes)),
                    cond.map(|c| Box::new(walk_expr(*c, env, datatypes))),
                ),
                StepKind::Where(c) => {
                    StepKind::Where(Box::new(walk_expr(*c, env, datatypes)))
                }
                StepKind::Yield(e) => {
                    StepKind::Yield(Box::new(walk_expr(*e, env, datatypes)))
                }
                StepKind::Order(e) => {
                    StepKind::Order(Box::new(walk_expr(*e, env, datatypes)))
                }
                StepKind::Compute(e) => {
                    StepKind::Compute(Box::new(walk_expr(*e, env, datatypes)))
                }
                StepKind::Group(k, a) => StepKind::Group(
                    Box::new(walk_expr(*k, env, datatypes)),
                    a.map(|e| Box::new(walk_expr(*e, env, datatypes))),
                ),
                other => other,
            };
            Step::new(new_kind, s.env)
        })
        .collect();
    match kind {
        'f' => Expr::From(t, new_steps),
        'e' => Expr::Exists(t, new_steps),
        _ => Expr::Forall(t, new_steps),
    }
}

/// Inspects a `Decl` and, for every value-binding whose RHS is a
/// single-arm `fn p => body`, records the binding in `env`. We
/// cap at one parameter for now — multi-clause functions and
/// curried definitions can be added in a later phase.
fn collect_fn_bindings(decl: &Decl, env: &mut FnEnv) {
    use std::slice::from_ref;
    let binds: &[ValBind] = match decl {
        Decl::NonRecVal(b) => from_ref(b.as_ref()),
        Decl::RecVal(binds) => binds.as_slice(),
        _ => return,
    };
    for b in binds {
        if let Pat::Identifier(_, name) = &b.pat
            && let Expr::Fn(_, arms, _) = &b.expr
            && arms.len() == 1
        {
            let Match { pat, expr } = &arms[0];
            env.insert(name.clone(), (pat.clone(), expr.clone()));
        }
    }
}

fn has_extent_scan(steps: &[Step]) -> bool {
    steps.iter().any(|s| {
        matches!(&s.kind,
            StepKind::Scan(_, source, _)
                if matches!(source.as_ref(), Expr::Extent(_)))
    })
}

/// Pre-pass: rewrite each `where (x, y, …) elem coll` whose left-
/// hand tuple is exactly the names of some unbounded patterns in
/// this from. The matched ScanExtents are merged into a single
/// `Scan(Tuple([x, y, …]), coll)` step (mirroring the user-typed
/// `from (x, y, …) in coll`), and the original `elem` conjunct
/// is dropped from the surrounding `Where`.
///
/// The merged scan is placed at the position of the *last* of the
/// matched ScanExtents, so later steps that reference any of the
/// destructured names see them as bound.
/// Inlines simple function calls in Where conjuncts when the
/// function has a tuple-pattern parameter. This lets
/// `decompose_tuple_elems` see e.g. `(n, d) elem coll` even
/// when the user wrote `f (n, d)` for a let-bound
/// `fun f (n, d) = (n, d) elem coll`.
fn inline_tuple_fn_calls_in_where(
    steps: Vec<Step>,
    fn_env: &FnEnv,
) -> Vec<Step> {
    use crate::compile::generators::split_conjuncts;
    use crate::compile::replacer::substitute;
    if fn_env.is_empty() {
        return steps;
    }
    let try_inline = |c: &Expr| -> Expr {
        let Expr::Apply(_, f, arg, _) = c else {
            return c.clone();
        };
        let Expr::Identifier(_, fn_name) = f.as_ref() else {
            return c.clone();
        };
        let Some((param_pat, body)) = fn_env.get(fn_name) else {
            return c.clone();
        };
        let Pat::Tuple(_, sub_pats) = param_pat else {
            return c.clone();
        };
        let Expr::Tuple(_, arg_elems) = arg.as_ref() else {
            return c.clone();
        };
        if sub_pats.len() != arg_elems.len() {
            return c.clone();
        }
        let mut subst_map: HashMap<String, Expr> = HashMap::new();
        for (sp, ae) in sub_pats.iter().zip(arg_elems.iter()) {
            if let Pat::Identifier(_, n) = sp {
                subst_map.insert(n.clone(), ae.clone());
            } else {
                return c.clone();
            }
        }
        substitute(body, &subst_map)
    };
    steps
        .into_iter()
        .map(|s| match s.kind {
            StepKind::Where(cond) => {
                let conjuncts: Vec<Expr> = split_conjuncts(&cond)
                    .into_iter()
                    .map(|c| try_inline(&c))
                    .collect();
                let new_cond = if conjuncts.is_empty() {
                    *cond
                } else {
                    let mut iter = conjuncts.into_iter();
                    let first = iter.next().unwrap();
                    iter.fold(first, |a, b| and_all(vec![a, b]))
                };
                Step::new(StepKind::Where(Box::new(new_cond)), s.env)
            }
            other => Step::new(other, s.env),
        })
        .collect()
}

/// Beta-reduces single-arm `case (e1, …, en) of (a1, …, an) =>
/// body` to `body[ai := ei]` in Where conjuncts. Lets
/// `decompose_tuple_elems` see e.g. `(y, x) elem coll` even when
/// the user wrote `case (y, x) of (a, b) => (a, b) elem coll`.
fn inline_tuple_case_in_where(steps: Vec<Step>) -> Vec<Step> {
    use crate::compile::generators::split_conjuncts;
    use crate::compile::replacer::substitute;
    let try_inline = |c: &Expr| -> Expr {
        let Expr::Case(_, subject, arms, _) = c else {
            return c.clone();
        };
        if arms.len() != 1 {
            return c.clone();
        }
        let arm = &arms[0];
        let Pat::Tuple(_, sub_pats) = &arm.pat else {
            return c.clone();
        };
        let Expr::Tuple(_, arg_elems) = subject.as_ref() else {
            return c.clone();
        };
        if sub_pats.len() != arg_elems.len() {
            return c.clone();
        }
        let mut subst_map: HashMap<String, Expr> = HashMap::new();
        for (sp, ae) in sub_pats.iter().zip(arg_elems.iter()) {
            if let Pat::Identifier(_, n) = sp {
                subst_map.insert(n.clone(), ae.clone());
            } else {
                return c.clone();
            }
        }
        substitute(&arm.expr, &subst_map)
    };
    steps
        .into_iter()
        .map(|s| match s.kind {
            StepKind::Where(cond) => {
                let conjuncts: Vec<Expr> = split_conjuncts(&cond)
                    .into_iter()
                    .map(|c| try_inline(&c))
                    .collect();
                let new_cond = if conjuncts.is_empty() {
                    *cond
                } else {
                    let mut iter = conjuncts.into_iter();
                    let first = iter.next().unwrap();
                    iter.fold(first, |a, b| and_all(vec![a, b]))
                };
                Step::new(StepKind::Where(Box::new(new_cond)), s.env)
            }
            other => Step::new(other, s.env),
        })
        .collect()
}

/// Drops `ScanExtent` steps whose pattern name doesn't appear in
/// any of the from's other steps (whose result is `bool` —
/// `exists` / `forall` — so unconstrained, unread bindings have
/// no effect on the answer). Only the leaf-pattern case (a
/// single `Pat::Identifier`) is pruned; compound patterns might
/// have non-identifier sub-patterns we don't analyse here.
fn prune_unused_scan_extents(steps: Vec<Step>) -> Vec<Step> {
    use crate::compile::free_finder::free_names_in;
    // Collect names referenced by every non-(self-)scan step.
    let mut referenced: HashSet<String> = HashSet::new();
    for (i, s) in steps.iter().enumerate() {
        match &s.kind {
            StepKind::Scan(p, source, cond) => {
                // A scan's source/condition can reference earlier
                // patterns; we count those references. The pattern
                // bound by *this* scan is excluded below — we want
                // self-references not to count.
                let bound_here: HashSet<String> = {
                    let mut bs: Vec<Binding> = Vec::new();
                    Binding::collect_bindings(p, &mut bs);
                    bs.into_iter().map(|b| b.id.name).collect()
                };
                let _ = i;
                for n in free_names_in(source).into_iter() {
                    if !bound_here.contains(&n) {
                        referenced.insert(n);
                    }
                }
                if let Some(c) = cond {
                    for n in free_names_in(c).into_iter() {
                        if !bound_here.contains(&n) {
                            referenced.insert(n);
                        }
                    }
                }
            }
            StepKind::Where(c) => {
                for n in free_names_in(c) {
                    referenced.insert(n);
                }
            }
            StepKind::Yield(e) | StepKind::Order(e) | StepKind::Compute(e) => {
                for n in free_names_in(e) {
                    referenced.insert(n);
                }
            }
            StepKind::Group(k, a) => {
                for n in free_names_in(k) {
                    referenced.insert(n);
                }
                if let Some(agg) = a {
                    for n in free_names_in(agg) {
                        referenced.insert(n);
                    }
                }
            }
            _ => {}
        }
    }

    // Drop any `ScanExtent(name)` whose `name` is unreferenced.
    steps
        .into_iter()
        .filter(|s| match &s.kind {
            StepKind::Scan(p, source, _)
                if matches!(source.as_ref(), Expr::Extent(_)) =>
            {
                if let Pat::Identifier(_, n) = p.as_ref() {
                    referenced.contains(n)
                } else {
                    true
                }
            }
            _ => true,
        })
        .collect()
}

fn decompose_tuple_elems(steps: Vec<Step>) -> Vec<Step> {
    use HashSet;

    // Gather all ScanExtent positions and the names they bind.
    let mut extent_index: HashMap<String, usize> = HashMap::new();
    // Names bound by *any* prior scan in this from (regular or
    // unbounded), with their step position. Tuple-LHS components
    // that are bound here can be matched via a fresh-named
    // scan-binding plus an equality filter, even though they
    // don't have their own ScanExtent.
    let mut already_bound: HashMap<String, usize> = HashMap::new();
    for (i, step) in steps.iter().enumerate() {
        if let StepKind::Scan(p, source, _) = &step.kind {
            if matches!(source.as_ref(), Expr::Extent(_))
                && let Pat::Identifier(_, n) = p.as_ref()
            {
                extent_index.insert(n.clone(), i);
            } else {
                let mut bs: Vec<Binding> = Vec::new();
                Binding::collect_bindings(p, &mut bs);
                for b in bs {
                    already_bound.insert(b.id.name, i);
                }
            }
        }
    }
    if extent_index.is_empty() {
        return steps;
    }
    // Counter for synthesising fresh names for already-bound
    // tuple components.
    let mut fresh_counter: usize = 0;

    // For each where-step, decompose its conjuncts and identify
    // which ones are tuple-elem candidates we can merge.
    //
    // (positions_to_drop, replacement_at_position, conjunct_index_to_drop)
    let mut drop_positions: HashSet<usize> = HashSet::new();
    let mut replacement_at: HashMap<usize, Step> = HashMap::new();
    // Steps to insert immediately *after* a given position (used
    // when the merged Scan's last reference is an already-bound
    // name, so the existing Scan must be kept).
    let mut insert_after: HashMap<usize, Step> = HashMap::new();
    // Per Where step: which conjunct indices to drop.
    let mut where_drops: HashMap<usize, HashSet<usize>> = HashMap::new();

    for (wi, step) in steps.iter().enumerate() {
        let StepKind::Where(cond) = &step.kind else {
            continue;
        };
        let conjuncts = split_conjuncts(cond);
        for (ci, c) in conjuncts.iter().enumerate() {
            // Look for `Apply(ListElem, Tuple(_, [tuple_lhs, coll]))`
            // where `tuple_lhs` is a Tuple of Identifiers, all of
            // which are ScanExtent-bound and not yet claimed.
            let Expr::Apply(_, f, arg, _) = c else {
                continue;
            };
            let Expr::Literal(_, Val::Fn(BuiltInFunction::ListElem)) =
                f.as_ref()
            else {
                continue;
            };
            let Expr::Tuple(_, args) = arg.as_ref() else {
                continue;
            };
            if args.len() != 2 {
                continue;
            }
            let Expr::Tuple(_tuple_t, ids) = &args[0] else {
                continue;
            };
            let coll = &args[1];

            // Each component must be either:
            //   * an Identifier naming a not-yet-claimed ScanExtent
            //     (becomes a Pat::Identifier in the merged scan), or
            //   * a Literal (becomes a Pat::Literal — narrows the
            //     scan to records whose field equals that constant).
            // Anything else (a free expression, a non-extent
            // identifier, etc.) makes us skip this conjunct and let
            // the per-pattern generator pipeline handle it.
            let mut named_pats: Vec<Pat> = Vec::with_capacity(ids.len());
            // Positions of ScanExtents we'll drop and replace; the
            // merged Scan sits at the *last* of these.
            let mut extent_positions: Vec<usize> =
                Vec::with_capacity(ids.len());
            // Positions that constrain *where* the merged Scan can
            // be inserted: extent positions (above) plus positions
            // of already-bound names referenced as tuple components.
            // The merged Scan is placed at max(reference_positions)
            // so all referenced bindings are in scope.
            let mut reference_positions: Vec<usize> =
                Vec::with_capacity(ids.len());
            let mut bound_names: Vec<String> = Vec::new();
            // Equality filters to apply after the merged Scan,
            // matching synthesised binding-names for already-
            // bound tuple components against the original
            // identifiers.
            let mut post_filters: Vec<(String, Box<Type>, Expr)> = Vec::new();
            let mut ok = true;
            for id in ids {
                match id {
                    Expr::Identifier(t, n) => {
                        if let Some(pos) = extent_index.get(n) {
                            if drop_positions.contains(pos)
                                || replacement_at.contains_key(pos)
                                || bound_names.contains(n)
                            {
                                ok = false;
                                break;
                            }
                            named_pats
                                .push(Pat::Identifier(t.clone(), n.clone()));
                            extent_positions.push(*pos);
                            reference_positions.push(*pos);
                            bound_names.push(n.clone());
                        } else if let Some(pos) = already_bound.get(n) {
                            // Already-bound name: scan position
                            // gets a fresh binding-name we'll
                            // compare against the original.
                            let fresh = format!("__decomp${}", fresh_counter);
                            fresh_counter += 1;
                            named_pats.push(Pat::Identifier(
                                t.clone(),
                                fresh.clone(),
                            ));
                            post_filters.push((fresh, t.clone(), id.clone()));
                            reference_positions.push(*pos);
                        } else {
                            ok = false;
                            break;
                        }
                    }
                    Expr::Literal(t, v) => {
                        named_pats.push(Pat::Literal(t.clone(), v.clone()));
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            // Need at least one identifier to merge — otherwise this
            // is a constant `elem` that doesn't bind anything.
            if !ok || extent_positions.is_empty() {
                continue;
            }

            // Build the merged Scan. Element type = first named
            // pat's tuple type (i.e. the tuple type from the LHS).
            let tuple_t = match &args[0] {
                Expr::Tuple(t, _) => t.clone(),
                _ => continue,
            };
            let tuple_pat = Pat::Tuple(tuple_t.clone(), named_pats);
            // Build a Scan condition that compares each fresh-
            // bound component to its original (already-bound)
            // identifier. The condition lives on the Scan, so it
            // runs once per element, filtering early.
            let cond = if post_filters.is_empty() {
                None
            } else {
                let bool_t = Box::new(Type::Primitive(PrimitiveType::Bool));
                let mut conjuncts: Vec<Expr> = Vec::new();
                for (fresh, t, orig) in &post_filters {
                    let pair_t = Box::new(Type::Tuple(vec![
                        (**t).clone(),
                        (**t).clone(),
                    ]));
                    let fn_t =
                        Box::new(Type::Fn(pair_t.clone(), bool_t.clone()));
                    let eq_op = match t.as_ref() {
                        Type::Primitive(PrimitiveType::Int) => {
                            BuiltInFunction::IntEq
                        }
                        Type::Primitive(PrimitiveType::Real) => {
                            BuiltInFunction::RealEq
                        }
                        Type::Primitive(PrimitiveType::String) => {
                            BuiltInFunction::StringEq
                        }
                        Type::Primitive(PrimitiveType::Char) => {
                            BuiltInFunction::CharEq
                        }
                        Type::Primitive(PrimitiveType::Bool) => {
                            BuiltInFunction::BoolEq
                        }
                        _ => BuiltInFunction::GEq,
                    };
                    let fn_lit = Expr::Literal(fn_t, Val::Fn(eq_op));
                    let arg = Expr::Tuple(
                        pair_t,
                        vec![
                            Expr::Identifier(t.clone(), fresh.clone()),
                            orig.clone(),
                        ],
                    );
                    conjuncts.push(Expr::Apply(
                        bool_t.clone(),
                        Box::new(fn_lit),
                        Box::new(arg),
                        Span::new(""),
                    ));
                }
                Some(Box::new(and_all(conjuncts)))
            };
            let scan = Step::new(
                StepKind::Scan(
                    Box::new(tuple_pat),
                    Box::new(coll.clone()),
                    cond,
                ),
                step.env.clone(),
            );

            // Place the scan at the position of the *last*
            // referenced binding (extent or already-bound) so
            // every dependency is in scope.
            let last_pos = *reference_positions.iter().max().unwrap();
            let last_is_extent = extent_positions.contains(&last_pos);
            for p in &extent_positions {
                if *p != last_pos {
                    drop_positions.insert(*p);
                }
            }
            if last_is_extent {
                if replacement_at.contains_key(&last_pos) {
                    // Two merges want the same slot; bail.
                    continue;
                }
                replacement_at.insert(last_pos, scan);
            } else {
                if insert_after.contains_key(&last_pos) {
                    continue;
                }
                insert_after.insert(last_pos, scan);
            }

            // Mark the conjunct for removal from this Where.
            where_drops.entry(wi).or_default().insert(ci);
        }
    }

    if drop_positions.is_empty()
        && replacement_at.is_empty()
        && insert_after.is_empty()
    {
        return steps;
    }

    // Rebuild the step list applying the replacements.
    let mut out: Vec<Step> = Vec::with_capacity(steps.len());
    for (i, step) in steps.into_iter().enumerate() {
        if drop_positions.contains(&i) {
            continue;
        }
        if let Some(repl) = replacement_at.remove(&i) {
            out.push(repl);
            if let Some(after) = insert_after.remove(&i) {
                out.push(after);
            }
            continue;
        }
        // For Where steps, drop matched conjuncts.
        if let Some(drops) = where_drops.get(&i)
            && let StepKind::Where(cond) = &step.kind
        {
            let conjuncts = split_conjuncts(cond);
            let kept: Vec<Expr> = conjuncts
                .into_iter()
                .enumerate()
                .filter(|(ci, _)| !drops.contains(ci))
                .map(|(_, c)| c)
                .collect();
            if kept.is_empty() {
                // Whole where becomes vacuous; drop it.
                if let Some(after) = insert_after.remove(&i) {
                    out.push(after);
                }
                continue;
            }
            let new_cond = and_all(kept);
            out.push(Step::new(StepKind::Where(Box::new(new_cond)), step.env));
            if let Some(after) = insert_after.remove(&i) {
                out.push(after);
            }
            continue;
        }
        out.push(step);
        if let Some(after) = insert_after.remove(&i) {
            out.push(after);
        }
    }
    out
}

fn expand_steps(
    steps: Vec<Step>,
    env: &FnEnv,
    datatypes: &DatatypeMap,
) -> Vec<Step> {
    // Phase 0 (pre-pass): merge tuple-pattern `elem` conjuncts
    // with the corresponding ScanExtents. A `where (x, y) elem
    // coll` constraint, combined with `ScanExtent(x)` and
    // `ScanExtent(y)`, becomes a single `Scan(Tuple([x, y]), coll)`
    // — equivalent to writing `from (x, y) in coll`. Without this
    // step the per-pattern generators couldn't preserve the
    // tuple's correlation between `x` and `y`.
    // Phase 0a: inline let-bound function calls in `where`
    // conjuncts whose body would, after substitution, be a
    // tuple-elem constraint (e.g. `fun f (n, d) = (n, d) elem
    // coll`). The per-pattern function-inlining strategy in
    // `maybe_function` only lets us derive a generator for one
    // pattern at a time; for tuple-elem we want
    // `decompose_tuple_elems` to merge ScanExtents for *all*
    // tuple components into one Scan, so the inlining has to
    // happen at the from-level pre-pass.
    let steps = inline_tuple_fn_calls_in_where(steps, env);
    let steps = inline_tuple_case_in_where(steps);
    let steps = decompose_tuple_elems(steps);

    // Phase 0b: prune fully-unused ScanExtents from `exists` /
    // `forall` queries. `exists w, x, y where (x, 2) elem coll`
    // depends only on x; w and y don't gate the answer, so
    // morel-java drops them. We only do this for exists/forall
    // (last step is StepKind::Exists) — for a regular `from` the
    // iteration count of an unconstrained var would matter.
    let steps =
        if matches!(steps.last().map(|s| &s.kind), Some(StepKind::Exists)) {
            prune_unused_scan_extents(steps)
        } else {
            steps
        };

    // Phase A: derive generators by scanning where-clauses.
    let mut cache = Cache::new();
    derive_generators(&steps, &mut cache, env, datatypes);

    // Phase B: collect every Scan-over-Extent's (pat, env) pair in
    // the order they appear in `steps`, then topologically sort by
    // generator dependencies. A scan whose generator references
    // another unbounded pattern must come after that pattern's
    // scan. Without this, e.g.
    //   `from dno, name, v where v elem scott.depts
    //                       where dno = v.deptno`
    // would emit `Scan(dno, [v.deptno])` before `v` is bound.
    let extent_scans: Vec<(Pat, StepEnv)> = steps
        .iter()
        .filter_map(|s| match &s.kind {
            StepKind::Scan(p, source, _)
                if matches!(source.as_ref(), Expr::Extent(_)) =>
            {
                Some(((**p).clone(), s.env.clone()))
            }
            _ => None,
        })
        .collect();
    let ordered_scans = topo_order(&extent_scans, &cache);

    // Phase C: rebuild the steps. Replace each Scan-over-Extent
    // with its generator's expression, but defer emission until
    // the generator's free patterns are bound by earlier scans
    // (regular `from x in coll` or already-emitted unbounded
    // scans). Decompose every Where into conjuncts and drop
    // those whose text appears in a sealed generator's
    // provenance. Other steps pass through.
    // Names introduced by *this* from's scans (regular and
    // unbounded). Used to decide whether a generator's free-pat
    // dependency must be emitted before it; names from outer
    // scopes (let-bound vals, function parameters, …) are always
    // in scope and don't gate scan ordering.
    let from_names: HashSet<String> = {
        let mut s = HashSet::new();
        for st in &steps {
            if let StepKind::Scan(p, _, _) = &st.kind {
                let mut bs: Vec<Binding> = Vec::new();
                Binding::collect_bindings(p, &mut bs);
                for b in bs {
                    s.insert(b.id.name);
                }
            }
        }
        s
    };

    let provenance: Vec<Expr> =
        cache.sealed_provenance().into_iter().cloned().collect();
    let mut out = Vec::with_capacity(steps.len());
    let mut scan_idx = 0;
    let mut bound_names: HashSet<String> = HashSet::new();
    // Bindings ordered as scans are emitted; used to rebuild the
    // step env when we reorder ScanExtents past regular Scans.
    let mut bound_bindings: Vec<Binding> = Vec::new();
    // ScanExtents waiting on their free-pat dependencies. Each
    // entry is (next_pat, next_env, original_cond).
    let mut deferred: Vec<(Pat, StepEnv, Option<Box<Expr>>)> = Vec::new();

    let try_flush = |bound_names: &mut HashSet<String>,
                     bound_bindings: &mut Vec<Binding>,
                     deferred: &mut Vec<(Pat, StepEnv, Option<Box<Expr>>)>,
                     out: &mut Vec<Step>| {
        let mut progress = true;
        while progress {
            progress = false;
            let mut still: Vec<(Pat, StepEnv, Option<Box<Expr>>)> = Vec::new();
            for (next_pat, orig_env, cond) in deferred.drain(..) {
                let Pat::Identifier(_, n) = &next_pat else {
                    still.push((next_pat, orig_env, cond));
                    continue;
                };
                let name = n.clone();
                let ready = match cache.best(&name) {
                    Some(g) => g.free_pats.iter().all(|fp| {
                        // Outer-scope names are always in scope;
                        // only require from-step names to be
                        // bound by an earlier emitted scan.
                        !from_names.contains(fp.as_str())
                            || bound_names.contains(fp.as_str())
                    }),
                    None => true,
                };
                if !ready {
                    still.push((next_pat, orig_env, cond));
                    continue;
                }
                // Add the new pattern's bindings.
                let mut bs: Vec<Binding> = Vec::new();
                Binding::collect_bindings(&next_pat, &mut bs);
                for b in bs {
                    if !bound_names.contains(&b.id.name) {
                        bound_names.insert(b.id.name.clone());
                        bound_bindings.push(b);
                    }
                }
                let new_atom = bound_bindings.len() == 1;
                let new_env = StepEnv::new(
                    bound_bindings.clone(),
                    new_atom,
                    orig_env.ordered,
                );
                if let Some(generator) = cache.best(&name) {
                    let merged_cond = match (
                        cond.map(|c| *c),
                        generator.extra_filter.clone(),
                    ) {
                        (None, None) => None,
                        (Some(c), None) | (None, Some(c)) => Some(Box::new(c)),
                        (Some(c), Some(f)) => {
                            Some(Box::new(and_all(vec![c, f])))
                        }
                    };
                    let unique = generator.unique;
                    out.push(Step::new(
                        StepKind::Scan(
                            Box::new(next_pat),
                            Box::new(generator.exp.clone()),
                            merged_cond,
                        ),
                        new_env.clone(),
                    ));
                    // A non-unique generator (e.g. point-orelse-
                    // range) may produce the same value via more
                    // than one branch. Strip duplicates so the
                    // result has set semantics.
                    if !unique {
                        out.push(Step::new(StepKind::Distinct, new_env));
                    }
                } else {
                    let extent = Expr::Extent(next_pat.type_());
                    out.push(Step::new(
                        StepKind::Scan(
                            Box::new(next_pat),
                            Box::new(extent),
                            cond,
                        ),
                        new_env,
                    ));
                }
                progress = true;
            }
            *deferred = still;
        }
    };

    for step in steps {
        match step.kind {
            StepKind::Scan(pat, source, cond)
                if matches!(source.as_ref(), Expr::Extent(_)) =>
            {
                if !matches!(pat.as_ref(), Pat::Identifier(_, _))
                    || scan_idx >= ordered_scans.len()
                {
                    out.push(Step::new(
                        StepKind::Scan(pat, source, cond),
                        step.env,
                    ));
                    continue;
                }
                let (next_pat, next_env) = ordered_scans[scan_idx].clone();
                scan_idx += 1;
                deferred.push((next_pat, next_env, cond));
                try_flush(
                    &mut bound_names,
                    &mut bound_bindings,
                    &mut deferred,
                    &mut out,
                );
            }
            StepKind::Scan(pat, source, cond) => {
                // Regular Scan: emit, then try to flush deferred.
                let mut bs: Vec<Binding> = Vec::new();
                Binding::collect_bindings(&pat, &mut bs);
                for b in bs {
                    if !bound_names.contains(&b.id.name) {
                        bound_names.insert(b.id.name.clone());
                        bound_bindings.push(b);
                    }
                }
                let new_atom = bound_bindings.len() == 1;
                let new_env = StepEnv::new(
                    bound_bindings.clone(),
                    new_atom,
                    step.env.ordered,
                );
                out.push(Step::new(StepKind::Scan(pat, source, cond), new_env));
                try_flush(
                    &mut bound_names,
                    &mut bound_bindings,
                    &mut deferred,
                    &mut out,
                );
            }
            StepKind::Where(condition) => {
                try_flush(
                    &mut bound_names,
                    &mut bound_bindings,
                    &mut deferred,
                    &mut out,
                );
                let conjuncts = split_conjuncts(&condition);
                let kept: Vec<Expr> = conjuncts
                    .into_iter()
                    .filter(|c| !provenance_contains(&provenance, c))
                    .collect();
                if kept.is_empty() {
                    continue;
                }
                let new_cond = and_all(kept);
                out.push(Step::new(
                    StepKind::Where(Box::new(new_cond)),
                    step.env,
                ));
            }
            other => {
                try_flush(
                    &mut bound_names,
                    &mut bound_bindings,
                    &mut deferred,
                    &mut out,
                );
                out.push(Step::new(other, step.env));
            }
        }
    }
    // Emit any still-deferred scans best-effort; they'll surface
    // as "pattern X is not grounded" at compile time.
    for (next_pat, next_env, cond) in deferred {
        let extent = Expr::Extent(next_pat.type_());
        out.push(Step::new(
            StepKind::Scan(Box::new(next_pat), Box::new(extent), cond),
            next_env,
        ));
    }
    out
}

/// Topologically sorts the unbounded scans by generator
/// dependency: a scan whose generator references pattern `q` is
/// emitted *after* `q`'s own scan. Cycles fall back to the original
/// order for the cycle members.
fn topo_order(
    extent_scans: &[(Pat, StepEnv)],
    cache: &Cache,
) -> Vec<(Pat, StepEnv)> {
    use HashSet;
    let names: Vec<String> = extent_scans
        .iter()
        .filter_map(|(p, _)| match p {
            Pat::Identifier(_, n) => Some(n.clone()),
            _ => None,
        })
        .collect();
    let unbounded: HashSet<&str> = names.iter().map(String::as_str).collect();
    let mut emitted: HashSet<String> = HashSet::new();
    let mut order: Vec<(Pat, StepEnv)> = Vec::with_capacity(extent_scans.len());
    let mut remaining: Vec<(Pat, StepEnv)> = extent_scans.to_vec();
    let mut last_size = remaining.len() + 1;
    while !remaining.is_empty() && remaining.len() < last_size {
        last_size = remaining.len();
        let mut still: Vec<(Pat, StepEnv)> = Vec::new();
        for (p, e) in remaining.drain(..) {
            let Pat::Identifier(_, ref n) = p else {
                order.push((p, e));
                continue;
            };
            let n = n.clone();
            // The scan is ready if every free pattern of its
            // generator is either NOT an unbounded scan in this
            // from (i.e. outer-scope or a bounded scan) or has
            // already been emitted.
            let ready = match cache.best(&n) {
                Some(g) => g.free_pats.iter().all(|fp| {
                    !unbounded.contains(fp.as_str())
                        || emitted.contains(fp.as_str())
                }),
                None => true,
            };
            if ready {
                emitted.insert(n);
                order.push((p, e));
            } else {
                still.push((p, e));
            }
        }
        remaining = still;
    }
    // Anything left is part of a cycle (or has missing deps);
    // append it in original order so we at least preserve the
    // surface arrangement.
    for entry in remaining {
        order.push(entry);
    }
    order
}

fn derive_generators(
    steps: &[Step],
    cache: &mut Cache,
    env: &FnEnv,
    datatypes: &DatatypeMap,
) {
    // Collect all Where conjuncts visible in this from. The morel-java
    // Expander does this in step order, but for Phase 1 (leaf-only,
    // no dependencies between generators) the order doesn't matter.
    let mut all_constraints: Vec<Expr> = Vec::new();
    for step in steps {
        if let StepKind::Where(cond) = &step.kind {
            all_constraints.extend(split_conjuncts(cond));
        }
    }

    // For every Scan-over-Extent, attempt to synthesise a generator.
    // Use a copy of the constraints so each pattern sees the full set.
    for step in steps {
        if let StepKind::Scan(pat, source, _) = &step.kind
            && matches!(source.as_ref(), Expr::Extent(_))
            && let Pat::Identifier(t, name) = pat.as_ref()
        {
            // The current `from` is a bag if any Scan source is a
            // bag, otherwise a list. For Phase 1 we're conservative:
            // unbounded extents default to bag, matching the type
            // resolver's `deduce_scan_extent_step_type`.
            let ordered = matches!(source.as_ref(), Expr::Extent(t)
                if matches!(t.as_ref(), Type::List(_)));
            maybe_generator(
                cache,
                pat,
                name,
                t,
                ordered,
                &all_constraints,
                env,
                datatypes,
            );
        }
    }
}

fn provenance_contains(provenance: &[Expr], conjunct: &Expr) -> bool {
    provenance.iter().any(|p| expr_eq(p, conjunct))
}

/// Structural equality between two Core expressions, ignoring spans.
/// Adequate for matching `where` conjuncts against generator
/// provenance — no alpha-renaming is needed because both sides come
/// from the same surface query.
pub(crate) fn expr_eq(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Literal(t1, v1), Expr::Literal(t2, v2)) => t1 == t2 && v1 == v2,
        (Expr::Identifier(t1, n1), Expr::Identifier(t2, n2)) => {
            t1 == t2 && n1 == n2
        }
        (Expr::RecordSelector(t1, s1), Expr::RecordSelector(t2, s2)) => {
            t1 == t2 && s1 == s2
        }
        (Expr::Apply(_, f1, a1, _), Expr::Apply(_, f2, a2, _)) => {
            expr_eq(f1, f2) && expr_eq(a1, a2)
        }
        (Expr::Tuple(_, xs), Expr::Tuple(_, ys))
        | (Expr::List(_, xs), Expr::List(_, ys)) => {
            xs.len() == ys.len()
                && xs.iter().zip(ys.iter()).all(|(x, y)| expr_eq(x, y))
        }
        (Expr::Extent(t1), Expr::Extent(t2)) => t1 == t2,
        _ => false,
    }
}

pub(crate) fn and_all(conjuncts: Vec<Expr>) -> Expr {
    let mut iter = conjuncts.into_iter();
    let first = iter.next().expect("at least one conjunct");
    iter.fold(first, |lhs, rhs| {
        let bool_t = Box::new(Type::Primitive(PrimitiveType::Bool));
        let pair_t =
            Box::new(Type::Tuple(vec![(*bool_t).clone(), (*bool_t).clone()]));
        let fn_t = Box::new(Type::Fn(pair_t.clone(), bool_t.clone()));
        let fn_expr =
            Expr::Literal(fn_t, Val::Fn(BuiltInFunction::BoolAndAlso));
        let arg = Expr::Tuple(pair_t, vec![lhs, rhs]);
        Expr::Apply(bool_t, Box::new(fn_expr), Box::new(arg), Span::new(""))
    })
}
