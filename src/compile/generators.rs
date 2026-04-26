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
//! Phase 1 of predicate inversion (hydromatic/morel#217).
//!
//! Mirrors morel-java's `compile.Generators::maybeGenerator`
//! with the leaf strategies — point, elem, range. Later phases
//! add string-prefix, function inlining, exists, case, and
//! constructor patterns.

use crate::compile::core::{Expr, Pat};
use crate::compile::free_finder::free_names_in;
use crate::compile::generator::{Cache, Cardinality, Generator};
use crate::compile::library::BuiltInFunction;
use crate::compile::span::Span;
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::val::Val;
use std::collections::BTreeSet;

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
) -> bool {
    // Phase A: classify each conjunct.
    let mut elem_match: Option<&Expr> = None;
    let mut elem_collection: Option<&Expr> = None;

    let mut point_match: Option<&Expr> = None;
    let mut point_value: Option<&Expr> = None;

    let mut has_bounds = false;

    for c in constraints {
        if elem_match.is_none()
            && let Some((lhs, rhs)) =
                call2_args(c, &[BuiltInFunction::ListElem])
            && references(lhs, pat_name)
        {
            elem_match = Some(c);
            elem_collection = Some(rhs);
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
            if references(lhs, pat_name) {
                point_match = Some(c);
                point_value = Some(rhs);
            } else if references(rhs, pat_name) {
                point_match = Some(c);
                point_value = Some(lhs);
            }
        }
        if !has_bounds && is_bound_constraint(c, pat_name) {
            has_bounds = true;
        }
    }

    // Phase B: synthesise leaf generators in priority order.
    if let (Some(c), Some(coll)) = (elem_match, elem_collection) {
        return create_collection_generator(cache, pat, pat_name, coll, c);
    }
    if let (Some(c), Some(value)) = (point_match, point_value) {
        return create_point_generator(cache, pat, pat_name, value, c);
    }
    if has_bounds && matches!(pat_type, Type::Primitive(PrimitiveType::Int)) {
        return create_range_generator(
            cache,
            pat,
            pat_name,
            ordered,
            constraints,
        );
    }
    false
}

// ---------------------------------------------------------------------------
// Leaf strategies
// ---------------------------------------------------------------------------

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
        true, // assume the user-supplied collection has unique elements
        true, // sealed: the elem-conjunct is fully encoded by the scan
        vec![source_constraint.clone()],
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
    let list_t = Box::new(Type::List(Box::new((*elem_t).clone())));
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
    cache: &mut Cache,
    pat: &Pat,
    pat_name: &str,
    ordered: bool,
    constraints: &[Expr],
) -> bool {
    let lower = match lower_bound(pat_name, constraints) {
        Some(l) => l,
        None => return false,
    };
    let upper = match upper_bound(pat_name, constraints) {
        Some(u) => u,
        None => return false,
    };

    // Provenance: every bound constraint involving the pattern.
    let provenance: Vec<Expr> = constraints
        .iter()
        .filter(|c| is_bound_constraint(c, pat_name))
        .cloned()
        .collect();

    // Build:
    //   List.tabulate (upper - lower + 1, fn k => lower + k)
    // (for ordered; Bag.tabulate otherwise.)
    let int_t = Box::new(Type::Primitive(PrimitiveType::Int));

    let lower_expr = if lower.strict {
        // x > lower  ⇒  use `lower + 1` as the inclusive low.
        binop_int(BuiltInFunction::IntPlus, lower.bound.clone(), int_lit(1))
    } else {
        lower.bound.clone()
    };
    let upper_expr = if upper.strict {
        binop_int(BuiltInFunction::IntMinus, upper.bound.clone(), int_lit(1))
    } else {
        upper.bound.clone()
    };

    let count = binop_int(
        BuiltInFunction::IntPlus,
        binop_int(
            BuiltInFunction::IntMinus,
            upper_expr.clone(),
            lower_expr.clone(),
        ),
        int_lit(1),
    );

    // fn k => lower + k
    let k_pat = Pat::Identifier(int_t.clone(), "k".to_string());
    let body = binop_int(
        BuiltInFunction::IntPlus,
        lower_expr.clone(),
        Expr::Identifier(int_t.clone(), "k".to_string()),
    );
    let fn_t = Box::new(Type::Fn(int_t.clone(), int_t.clone()));
    let fn_expr = Expr::Fn(
        fn_t.clone(),
        vec![crate::compile::core::Match {
            pat: k_pat,
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
        Box::new(Type::List(int_t.clone()))
    } else {
        Box::new(Type::Bag(int_t.clone()))
    };
    let exp = call2(tabulate, count, fn_expr, coll_t);

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
    let ops = [
        BuiltInFunction::IntGt,
        BuiltInFunction::IntGe,
        BuiltInFunction::IntLt,
        BuiltInFunction::IntLe,
    ];
    if let Some((lhs, rhs)) = call2_args(constraint, &ops) {
        references(lhs, pat_name) || references(rhs, pat_name)
    } else {
        false
    }
}

/// Returns `(bound, strict)` for the pattern's lower bound, picking
/// the first matching constraint. Strict means `>` (exclusive).
fn lower_bound(pat_name: &str, constraints: &[Expr]) -> Option<Bound> {
    for c in constraints {
        if let Some((lhs, rhs, op)) = call2_args_op(
            c,
            &[
                BuiltInFunction::IntGt,
                BuiltInFunction::IntGe,
                BuiltInFunction::IntLt,
                BuiltInFunction::IntLe,
            ],
        ) {
            // p > e  or  p >= e
            if references(lhs, pat_name)
                && (op == BuiltInFunction::IntGt
                    || op == BuiltInFunction::IntGe)
            {
                return Some(Bound {
                    bound: rhs.clone(),
                    strict: op == BuiltInFunction::IntGt,
                });
            }
            // e < p  or  e <= p (i.e. p > e or p >= e)
            if references(rhs, pat_name)
                && (op == BuiltInFunction::IntLt
                    || op == BuiltInFunction::IntLe)
            {
                return Some(Bound {
                    bound: lhs.clone(),
                    strict: op == BuiltInFunction::IntLt,
                });
            }
        }
    }
    None
}

/// Returns `(bound, strict)` for the pattern's upper bound. Strict
/// means `<` (exclusive).
fn upper_bound(pat_name: &str, constraints: &[Expr]) -> Option<Bound> {
    for c in constraints {
        if let Some((lhs, rhs, op)) = call2_args_op(
            c,
            &[
                BuiltInFunction::IntGt,
                BuiltInFunction::IntGe,
                BuiltInFunction::IntLt,
                BuiltInFunction::IntLe,
            ],
        ) {
            // p < e  or  p <= e
            if references(lhs, pat_name)
                && (op == BuiltInFunction::IntLt
                    || op == BuiltInFunction::IntLe)
            {
                return Some(Bound {
                    bound: rhs.clone(),
                    strict: op == BuiltInFunction::IntLt,
                });
            }
            // e > p  or  e >= p (i.e. p < e or p <= e)
            if references(rhs, pat_name)
                && (op == BuiltInFunction::IntGt
                    || op == BuiltInFunction::IntGe)
            {
                return Some(Bound {
                    bound: lhs.clone(),
                    strict: op == BuiltInFunction::IntGt,
                });
            }
        }
    }
    None
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
    Expr::Literal(Box::new(Type::Primitive(PrimitiveType::Int)), Val::Int(n))
}

fn binop_int(f: BuiltInFunction, a: Expr, b: Expr) -> Expr {
    let int_t = Box::new(Type::Primitive(PrimitiveType::Int));
    let pair_t =
        Box::new(Type::Tuple(vec![(*int_t).clone(), (*int_t).clone()]));
    let fn_t = Box::new(Type::Fn(pair_t.clone(), int_t.clone()));
    let fn_expr = Expr::Literal(fn_t.clone(), Val::Fn(f));
    let arg = Expr::Tuple(pair_t, vec![a, b]);
    Expr::Apply(int_t, Box::new(fn_expr), Box::new(arg), Span::new(""))
}

fn call2(f: BuiltInFunction, a: Expr, b: Expr, result_t: Box<Type>) -> Expr {
    let arg_t = Box::new(Type::Tuple(vec![
        (*a.type_()).clone(),
        (*b.type_()).clone(),
    ]));
    let fn_t = Box::new(Type::Fn(arg_t.clone(), result_t.clone()));
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
