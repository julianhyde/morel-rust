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
    Decl, Expr, JoinKind, Rel, Row, element_type, fresh_name, fresh_row_name,
    id_name, is_safe,
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
            // The rule applies again to a filter it puts over a join, so
            // that a conjunct reaches the lowest join that reads both of
            // its sides.
            match filter_into_join(&e2) {
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
    let is_input = |x: &Expr| rel.inputs().iter().any(|i| ptr::eq(*i, x));
    let joins = matches!(rel.as_ref(), Rel::Join(..));
    Expr::Rel(
        t.clone(),
        Box::new(rel.map_children(&|x| {
            let x2 = apply(x);
            if joins
                && is_input(x)
                && component_count(&x2) != component_count(x)
            {
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
