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

//! Rules that rewrite a declaration's relational trees once they have
//! been built. It is the part of morel-java's `RelRules` that morel-rust
//! has: `FILTER_INTO_JOIN`.

use crate::compile::core::{
    Decl, Expr, JoinKind, JoinRows, Rel, Row, element_type, fresh_name,
    fresh_row_name, id_name, is_safe,
};
use crate::compile::expander::and_all;
use crate::compile::free_finder::free_names_in;
use crate::compile::library::BuiltInFunction;
use crate::compile::rel_lowerer::{
    component_count, field_at, map_children, map_steps, substitute_name,
};
use crate::compile::types::Type;
use crate::eval::val::Val;
use std::collections::BTreeSet;
use std::ptr;
use std::rc::Rc;

/// Returns a declaration with the rules applied to every tree in it.
pub fn apply_decl(decl: &Decl) -> Decl {
    match decl {
        Decl::NonRecVal(b) => {
            let mut bind = b.as_ref().clone();
            bind.expr = apply(&b.expr);
            Decl::NonRecVal(Box::new(bind))
        }
        Decl::RecVal(binds) => Decl::RecVal(
            binds
                .iter()
                .map(|b| {
                    let mut bind = b.clone();
                    bind.expr = apply(&b.expr);
                    bind
                })
                .collect(),
        ),
        other => other.clone(),
    }
}

/// Returns an expression with the rules applied to every tree in it,
/// bottom-up, so that a node's inputs are rewritten before the node.
fn apply(e: &Expr) -> Expr {
    match e {
        Expr::Rel(..) => {
            let e2 = apply_below(e);
            // A rule applies again to a filter it puts over a join, so
            // that a conjunct reaches the lowest join that reads both of
            // its sides.
            match filter_exists_into_join(&e2).or_else(|| filter_into_join(&e2))
            {
                Some(e3) => apply(&e3),
                None => e2,
            }
        }
        Expr::From(t, steps) => Expr::From(t.clone(), map_steps(steps, &apply)),
        _ => map_children(e, &apply),
    }
}

/// Applies the rules to a node's children, but not to the node.
///
/// A join's element is the components of its inputs, and an input that
/// is itself a join gives one component for each of its own; any other
/// node gives one. So the rewrite of an input may not turn a join into
/// a node of another kind, nor the reverse: the join's type, and what
/// reads its element, would no longer agree with its inputs. Where it
/// would, the input keeps its kind, and only what is below it is
/// rewritten.
fn apply_below(e: &Expr) -> Expr {
    let Expr::Rel(t, rel) = e else {
        return apply(e);
    };
    // The inputs whose kind the join's element depends on: both of an
    // inner or outer join's; none of a semi-join's or anti-join's, whose
    // element is its left input's, whatever kind of node that is.
    let shaped: Vec<&Expr> = match rel.as_ref() {
        Rel::Join(kind, ..) if !kind.filters_left() => rel.inputs(),
        _ => Vec::new(),
    };
    let is_shaped = |x: &Expr| shaped.iter().any(|i| ptr::eq(*i, x));
    Expr::Rel(
        t.clone(),
        Box::new(rel.map_children(&|x| {
            let x2 = apply(x);
            if is_shaped(x) && component_count(&x2) != component_count(x) {
                apply_below(x)
            } else {
                x2
            }
        })),
    )
}

/// Moves the conjuncts of a `filter` over a `join` into the join, as far
/// down as each can go: into the left input, if it reads only the left
/// element; into the right input, if it reads only the right element and
/// the right input does not read the left element; into the join's
/// condition, if it reads both. It is morel-java's `FILTER_INTO_JOIN`.
///
/// So `from x in xs, y in ys where x.b = y.c andalso y.d > 0`, whose join
/// is a cross product, becomes a join on `x.b = y.c` of `xs` with `ys`
/// filtered by `y.d > 0`, and the join can be a hash join.
///
/// Over a `left join`, only a conjunct that reads only the left element
/// moves, into the left input; over a `right join`, only one that reads
/// only the right element, into the right input. Every element of that
/// input is in the output, so filtering it before the join removes the
/// same rows. A conjunct that reads the side padded with `NONE` stays,
/// and nothing moves over a `full join`.
///
/// Filtering an input of an inner join, or its pairs, before the join
/// rather than after gives the same rows in the same order. A conjunct
/// moves only if it can neither raise nor have an effect (see
/// [`is_safe`]). Neither a filter nor a join that reads its position is
/// changed, because moving a conjunct changes what is counted.
fn filter_into_join(e: &Expr) -> Option<Expr> {
    let Expr::Rel(filter_t, rel) = e else {
        return None;
    };
    let Rel::Filter(row, input, condition) = rel.as_ref() else {
        return None;
    };
    let Expr::Rel(join_t, join) = input.as_ref() else {
        return None;
    };
    let Rel::Join(kind, rows, join_condition, left, right) = join.as_ref()
    else {
        return None;
    };
    if row.ordinal.is_some()
        || rows.ordinal.is_some()
        || *kind == JoinKind::Full
    {
        return None;
    }
    if kind.filters_left() {
        // A semi-join's or anti-join's element is its left element, so
        // a safe conjunct can filter the left input instead.
        let (to_left, remaining): (Vec<Expr>, Vec<Expr>) =
            conjuncts(condition).into_iter().partition(is_safe);
        if to_left.is_empty() {
            return None;
        }
        let left2 = apply(&filter_over(left, &row.name, to_left));
        if component_count(&left2) != component_count(left) {
            return None;
        }
        let join2 = Expr::Rel(
            join_t.clone(),
            Box::new(Rel::Join(
                *kind,
                rows.clone(),
                join_condition.clone(),
                Box::new(left2),
                right.clone(),
            )),
        );
        if remaining.is_empty() {
            return Some(join2);
        }
        return Some(Expr::Rel(
            filter_t.clone(),
            Box::new(Rel::Filter(
                row.clone(),
                Box::new(join2),
                Box::new(and_all(remaining)),
            )),
        ));
    }
    // The element, over the join's own ids. The components of a side
    // that an outer join pads with NONE are options, which the ids are
    // not, so they are placeholders; a conjunct that reads one stays.
    let left_id = Expr::Identifier(element_of(left), rows.left.clone());
    let right_id = Expr::Identifier(element_of(right), rows.right.clone());
    let left_components = components(left, &left_id);
    let right_components = components(right, &right_id);
    let element_t = element_of(input);
    let types: Vec<Rc<Type>> = match element_t.as_ref() {
        Type::Tuple(types) => types.clone(),
        _ => return None,
    };
    let mut padded: BTreeSet<String> = BTreeSet::new();
    let mut parts = Vec::new();
    for (i, t) in types.iter().enumerate() {
        let is_left = i < left_components.len();
        let pad = if is_left {
            *kind == JoinKind::Right
        } else {
            *kind == JoinKind::Left
        };
        if pad {
            let name = format!("$pad{}", fresh_name());
            padded.insert(name.clone());
            parts.push(Expr::Identifier(t.clone(), name));
        } else if is_left {
            parts.push(left_components[i].clone());
        } else {
            parts.push(right_components[i - left_components.len()].clone());
        }
    }
    let element = Expr::Tuple(element_t.clone(), parts);
    let dependent = free_names_in(right).contains(&rows.left);
    let mut to_left = Vec::new();
    let mut to_right = Vec::new();
    let mut to_condition = Vec::new();
    let mut remaining = Vec::new();
    for conjunct in conjuncts(condition) {
        if !is_safe(&conjunct) {
            remaining.push(conjunct);
            continue;
        }
        let e = substitute_name(&conjunct, &row.name, &element);
        let names = free_names_in(&e);
        let reads_left = names.contains(&rows.left);
        let reads_right = names.contains(&rows.right);
        if padded.iter().any(|pad| names.contains(pad)) {
            // It reads a side that is padded with NONE.
            remaining.push(conjunct);
        } else if *kind != JoinKind::Inner {
            // Over an outer join, a conjunct may filter the side whose
            // every element is in the output, but may not join the
            // condition: a pair that fails it would be padded with NONE,
            // not removed.
            if reads_left && !reads_right {
                to_left.push((conjunct, e));
            } else if reads_right && !reads_left {
                to_right.push((conjunct, e));
            } else {
                remaining.push(conjunct);
            }
        } else if reads_left && reads_right {
            to_condition.push(e);
        } else if reads_left {
            to_left.push((conjunct, e));
        } else if reads_right && !dependent {
            to_right.push((conjunct, e));
        } else if reads_right {
            to_condition.push(e);
        } else {
            remaining.push(conjunct);
        }
    }
    if to_left.is_empty() && to_right.is_empty() && to_condition.is_empty() {
        return None;
    }
    // A conjunct moved into an input that is a join is moved on into
    // it. If it cannot be, the input would become a filter, of one
    // component where the join had several, so it stays where it was.
    let mut moved_any = !to_condition.is_empty();
    let mut moved_into = |side: &Expr, id: &str, moved: Vec<(Expr, Expr)>| {
        if moved.is_empty() {
            return side.clone();
        }
        let (originals, conditions): (Vec<Expr>, Vec<Expr>) =
            moved.into_iter().unzip();
        let side2 = apply(&filter_over(side, id, conditions));
        if component_count(&side2) == component_count(side) {
            moved_any = true;
            side2
        } else {
            remaining.extend(originals);
            side.clone()
        }
    };
    let left2 = moved_into(left, &rows.left, to_left);
    let right2 = moved_into(right, &rows.right, to_right);
    if !moved_any {
        return None;
    }
    let mut conditions = Vec::new();
    if !matches!(join_condition.as_ref(), Expr::Literal(_, Val::Bool(true))) {
        conditions.push((**join_condition).clone());
    }
    conditions.extend(to_condition);
    let join2 = Expr::Rel(
        join_t.clone(),
        Box::new(Rel::Join(
            *kind,
            rows.clone(),
            Box::new(if conditions.is_empty() {
                (**join_condition).clone()
            } else {
                and_all(conditions)
            }),
            Box::new(left2),
            Box::new(right2),
        )),
    );
    if remaining.is_empty() {
        return Some(join2);
    }
    Some(Expr::Rel(
        filter_t.clone(),
        Box::new(Rel::Filter(
            row.clone(),
            Box::new(join2),
            Box::new(and_all(remaining)),
        )),
    ))
}

/// Converts a conjunct `exists q` of a `filter` into a semi-join of the
/// filter's input with `q`, and `not (exists q)` into an anti-join, when
/// `q` reads the row only in equalities: `from c in customers where
/// (exists s in sales where s.cust = c.id)` becomes a semi-join of
/// `customers` with `sales` on `s.cust = c.id`, which evaluates `sales`
/// once rather than once per customer, and can be a hash join. It is
/// morel-java's `FILTER_EXISTS_INTO_JOIN`.
///
/// The equalities may be in any filter of `q` that is under only filters
/// and inner joins; each comes out of its filter and into the join's
/// condition, re-expressed over `q`'s element. If `q` reads the row
/// anywhere else, the conjunct stays. The other conjuncts go into a
/// filter below the join, so that they can move into the joins below it;
/// a filter that reads its position is not changed.
fn filter_exists_into_join(e: &Expr) -> Option<Expr> {
    let Expr::Rel(filter_t, rel) = e else {
        return None;
    };
    let Rel::Filter(row, input, condition) = rel.as_ref() else {
        return None;
    };
    if row.ordinal.is_some() {
        return None;
    }
    let conjuncts = conjuncts(condition);
    for (i, conjunct) in conjuncts.iter().enumerate() {
        // The names by which the query may read the row: the filter's
        // row, and the name the resolver gave it in a `let`, if any.
        let mut row_names = BTreeSet::from([row.name.clone()]);
        let mut e = conjunct;
        if let Expr::Let(_, decls, body) = e
            && let [Decl::NonRecVal(bind)] = decls.as_slice()
            && matches!(&bind.expr, Expr::Identifier(_, n) if *n == row.name)
            && let Some(v) = bind.pat.name()
        {
            row_names.insert(v);
            e = body;
        }
        let mut anti = false;
        if let Some(arg) = call_arg(e, BuiltInFunction::BoolNot) {
            anti = true;
            e = arg;
        }
        let q = if let Some(arg) = call_arg(e, BuiltInFunction::RelationalEmpty)
        {
            anti = !anti;
            arg
        } else if let Some(arg) =
            call_arg(e, BuiltInFunction::RelationalNonEmpty)
        {
            arg
        } else {
            continue;
        };
        // Whether the query has a row does not depend on what its
        // elements are, or their order; so a projection or a sort on top
        // of it, such as the record of a query with several scans, can
        // go, provided that evaluating it could neither raise nor have
        // an effect.
        let mut q = q;
        while let Expr::Rel(_, r) = q
            && let Rel::Project(qrow, qinput, qe) | Rel::Sort(qrow, qinput, qe) =
                r.as_ref()
            && is_safe(qe)
            && qrow.ordinal.is_none()
        {
            q = qinput;
        }
        let Some(d) = decorrelate(q, &row_names, &BTreeSet::new()) else {
            continue;
        };
        if d.conditions.is_empty() {
            continue;
        }
        // The conjuncts before the `exists` are evaluated before it, so
        // they may go below the join; so may a conjunct after it that can
        // neither raise nor have an effect. A conjunct after it that
        // might raise stays above, so that it still sees only the rows
        // that pass the `exists`.
        let mut others: Vec<Expr> = conjuncts[..i].to_vec();
        let mut above = Vec::new();
        for c in &conjuncts[i + 1..] {
            if is_safe(c) {
                others.push(c.clone());
            } else {
                above.push(c.clone());
            }
        }
        let left = if others.is_empty() {
            (**input).clone()
        } else {
            Expr::Rel(
                filter_t.clone(),
                Box::new(Rel::Filter(
                    row.clone(),
                    input.clone(),
                    Box::new(and_all(others)),
                )),
            )
        };
        let left_name = fresh_row_name(id_name(&row.name));
        let right_name = fresh_row_name(Some(&d.name));
        let left_id = Expr::Identifier(element_of(&left), left_name.clone());
        let right_id = Expr::Identifier(element_of(&d.rel), right_name.clone());
        let conditions: Vec<Expr> = d
            .conditions
            .iter()
            .map(|condition| {
                let mut c = condition(&right_id);
                for row_name in &row_names {
                    c = substitute_name(&c, row_name, &left_id);
                }
                c
            })
            .collect();
        let join = Expr::Rel(
            left.type_(),
            Box::new(Rel::Join(
                if anti { JoinKind::Anti } else { JoinKind::Semi },
                JoinRows {
                    left: left_name,
                    right: right_name,
                    ordinal: None,
                },
                Box::new(and_all(conditions)),
                Box::new(left),
                Box::new(d.rel),
            )),
        );
        if above.is_empty() {
            return Some(join);
        }
        return Some(Expr::Rel(
            filter_t.clone(),
            Box::new(Rel::Filter(
                row.clone(),
                Box::new(join),
                Box::new(and_all(above)),
            )),
        ));
    }
    None
}

/// Returns the argument of a call to a built-in function of one argument.
fn call_arg(e: &Expr, f: BuiltInFunction) -> Option<&Expr> {
    if let Expr::Apply(_, fx, arg, _) = e
        && let Expr::Literal(_, Val::Fn(g)) = fx.as_ref()
        && *g == f
    {
        return Some(arg);
    }
    None
}

/// A condition taken from a query, as a function of an expression for
/// the query's element.
type Condition = Box<dyn Fn(&Expr) -> Expr>;

/// A query from which the equalities that read the outer row have been
/// taken: the query without them, and each equality as a function of an
/// expression for the query's element.
struct Decorrelated {
    rel: Expr,
    conditions: Vec<Condition>,
    /// A name for the query's element, after the id of the node it came
    /// from.
    name: String,
}

/// Returns whether an expression reads any of the names.
fn mentions(e: &Expr, names: &BTreeSet<String>) -> bool {
    free_names_in(e).iter().any(|n| names.contains(n))
}

/// Takes from a query the equalities that read the outer row, under any
/// of `row_names`; returns `None` if the query reads it in any other way.
/// `locals` are the rows that the query binds above this node, which the
/// outer side of an equality must not read.
fn decorrelate(
    node: &Expr,
    row_names: &BTreeSet<String>,
    locals: &BTreeSet<String>,
) -> Option<Decorrelated> {
    if !mentions(node, row_names) {
        return Some(Decorrelated {
            rel: node.clone(),
            conditions: Vec::new(),
            name: name(node),
        });
    }
    let Expr::Rel(t, rel) = node else {
        return None;
    };
    match rel.as_ref() {
        Rel::Filter(frow, finput, fcondition) => {
            if frow.ordinal.is_some() {
                return None;
            }
            let mut locals2 = locals.clone();
            locals2.insert(frow.name.clone());
            let input = decorrelate(finput, row_names, &locals2)?;
            let mut conditions = input.conditions;
            let mut remaining = Vec::new();
            for conjunct in and_parts(fcondition) {
                if !mentions(&conjunct, row_names) {
                    // Once the equalities are taken out, the query is
                    // evaluated once, over all of its elements, rather
                    // than for each outer row; a conjunct that the
                    // equalities used to guard, or that would not have
                    // been evaluated at all, would then be evaluated.
                    // Only a conjunct that can neither raise nor have an
                    // effect may stay.
                    if !is_safe(&conjunct) {
                        return None;
                    }
                    remaining.push(conjunct);
                    continue;
                }
                let is_outer_key =
                    |x: &Expr| mentions(x, row_names) && !mentions(x, &locals2);
                let (a, b) = equality(&conjunct)?;
                if !is_outer_key(a) && !is_outer_key(b) {
                    return None;
                }
                // The equality, given an expression for the element; the
                // filter's element is its input's.
                let name = frow.name.clone();
                conditions.push(Box::new(move |element: &Expr| {
                    substitute_name(&conjunct, &name, element)
                }));
            }
            let rel = if remaining.is_empty() {
                input.rel
            } else {
                Expr::Rel(
                    t.clone(),
                    Box::new(Rel::Filter(
                        frow.clone(),
                        Box::new(input.rel),
                        Box::new(and_all(remaining)),
                    )),
                )
            };
            Some(Decorrelated {
                rel,
                conditions,
                name: id_name(&frow.name).unwrap_or("r").to_string(),
            })
        }
        Rel::Join(kind, rows, jcondition, left, right) => {
            if *kind != JoinKind::Inner
                || rows.ordinal.is_some()
                || mentions(jcondition, row_names)
            {
                return None;
            }
            let l = decorrelate(left, row_names, locals)?;
            let mut locals2 = locals.clone();
            locals2.insert(rows.left.clone());
            let r = decorrelate(right, row_names, &locals2)?;
            // An input may lose a filter, but not change the number of
            // components that it gives the join.
            let left_count = component_count(left);
            let right_count = component_count(right);
            if component_count(&l.rel) != left_count
                || component_count(&r.rel) != right_count
            {
                return None;
            }
            // Once equalities are taken out of an input, the join sees
            // elements that they used to exclude. So its condition must
            // be one that can neither raise nor have an effect, and if
            // equalities came out of the left input, a right input that
            // depends on the left, and so is evaluated for each of those
            // elements too, must be safe as well.
            if !l.conditions.is_empty() || !r.conditions.is_empty() {
                if !is_safe(jcondition) {
                    return None;
                }
                if !l.conditions.is_empty()
                    && free_names_in(right).contains(&rows.left)
                    && !is_safe(right)
                {
                    return None;
                }
            }
            let join2 = Expr::Rel(
                t.clone(),
                Box::new(Rel::Join(
                    *kind,
                    rows.clone(),
                    jcondition.clone(),
                    Box::new(l.rel),
                    Box::new(r.rel),
                )),
            );
            let mut conditions: Vec<Condition> = Vec::new();
            // An input's element, from the join's element: the input's
            // components.
            for c in l.conditions {
                conditions.push(Box::new(move |element: &Expr| {
                    c(&slice(element, 0, left_count))
                }));
            }
            // A condition from the right input may also read the left
            // input's element (the right input of a dependent join may),
            // by the join's left row; that, too, becomes a component of
            // the join's element.
            for c in r.conditions {
                let left_row = rows.left.clone();
                conditions.push(Box::new(move |element: &Expr| {
                    substitute_name(
                        &c(&slice(
                            element,
                            left_count,
                            left_count + right_count,
                        )),
                        &left_row,
                        &slice(element, 0, left_count),
                    )
                }));
            }
            Some(Decorrelated {
                rel: join2,
                conditions,
                name: l.name,
            })
        }
        _ => None,
    }
}

/// Returns the operands of an equality, `a = b`.
fn equality(e: &Expr) -> Option<(&Expr, &Expr)> {
    if let Expr::Apply(_, f, arg, _) = e
        && let Expr::Literal(_, Val::Fn(builtin)) = f.as_ref()
        && builtin.infix_op().is_some_and(|(op, _, _)| op == "=")
        && let Expr::Tuple(_, args) = arg.as_ref()
        && let [a, b] = args.as_slice()
    {
        return Some((a, b));
    }
    None
}

/// Returns the expression for the element of an input of a join, given
/// an expression for the join's element: its components `start` to
/// `end`, as a tuple if there are several.
fn slice(element: &Expr, start: usize, end: usize) -> Expr {
    let parts: Vec<Expr> = (start..end).map(|i| field_at(element, i)).collect();
    if parts.len() == 1 {
        return parts.into_iter().next().expect("one part");
    }
    let types = parts.iter().map(Expr::type_).collect();
    Expr::Tuple(Rc::new(Type::Tuple(types)), parts)
}

/// Returns a name for the element of a query, after the id of its node,
/// if it has one.
fn name(node: &Expr) -> String {
    if let Expr::Rel(_, rel) = node {
        match rel.as_ref() {
            Rel::Filter(row, ..)
            | Rel::Project(row, ..)
            | Rel::Sort(row, ..)
            | Rel::Group(row, ..) => {
                return id_name(&row.name).unwrap_or("r").to_string();
            }
            Rel::Join(_, _, _, left, _) => return name(left),
            _ => {}
        }
    }
    "e".to_string()
}

/// Returns the type of the elements of a node.
fn element_of(e: &Expr) -> Rc<Type> {
    let t = e.type_();
    element_type(&t).unwrap_or(t)
}

/// The components of a node's element, read out of an expression for it:
/// a join's are its inputs', and any other node's is the element.
fn components(node: &Expr, e: &Expr) -> Vec<Expr> {
    let n = component_count(node);
    if n == 1 {
        return vec![e.clone()];
    }
    (0..n).map(|i| field_at(e, i)).collect()
}

/// Returns a filter over `input` whose condition is the conjunction of
/// `conditions`, which read the input's element as `id`.
fn filter_over(input: &Expr, id: &str, conditions: Vec<Expr>) -> Expr {
    // Named after the id it replaces, so that the plan reads as the query.
    let name = fresh_row_name(id_name(id));
    let new_id = Expr::Identifier(element_of(input), name.clone());
    let condition = substitute_name(&and_all(conditions), id, &new_id);
    Expr::Rel(
        input.type_(),
        Box::new(Rel::Filter(
            Row {
                name,
                ordinal: None,
            },
            Box::new(input.clone()),
            Box::new(condition),
        )),
    )
}

/// Returns the conjuncts of a condition.
///
/// When a conjunct refers to the row from inside a query, as in `where
/// x.a = y.b andalso (exists z in zs where z.c = x.a)`, the resolver
/// names the row, and the condition becomes `let val v = r in ... end`.
/// Such a condition is split too: each conjunct of its body that does
/// not mention `v` is a conjunct on its own, and each that does is
/// wrapped in the `let`.
fn conjuncts(condition: &Expr) -> Vec<Expr> {
    let mut list = Vec::new();
    for e in and_parts(condition) {
        if let Expr::Let(t, decls, body) = &e
            && let [Decl::NonRecVal(bind)] = decls.as_slice()
            && matches!(bind.expr, Expr::Literal(..) | Expr::Identifier(..))
            && let Some(v) = bind.pat.name()
        {
            for c in conjuncts(body) {
                if free_names_in(&c).contains(&v) {
                    list.push(Expr::Let(t.clone(), decls.clone(), Box::new(c)));
                } else {
                    list.push(c);
                }
            }
        } else {
            list.push(e);
        }
    }
    list
}

/// Returns the operands of a chain of `andalso`.
fn and_parts(e: &Expr) -> Vec<Expr> {
    if let Expr::Apply(_, f, arg, _) = e
        && let Expr::Literal(_, Val::Fn(BuiltInFunction::BoolAndAlso)) =
            f.as_ref()
        && let Expr::Tuple(_, args) = arg.as_ref()
        && let [a, b] = args.as_slice()
    {
        let mut v = and_parts(a);
        v.extend(and_parts(b));
        return v;
    }
    vec![e.clone()]
}
