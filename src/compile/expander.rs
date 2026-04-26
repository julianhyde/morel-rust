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

use crate::compile::core::{Decl, Expr, Match, Pat, Step, StepKind, ValBind};
use crate::compile::generator::Cache;
use crate::compile::generators::{maybe_generator, split_conjuncts};
use crate::compile::library::BuiltInFunction;
use crate::compile::span::Span;
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::val::Val;
use std::collections::HashMap;

/// Map of let-bound function name → (parameter pattern, body
/// expression). Populated as `expand_decl` walks down through
/// nested `Let` expressions so that `maybe_function` can inline a
/// known function's body when it sees a constraint of the form
/// `f arg`.
pub type FnEnv = HashMap<String, (Pat, Expr)>;

/// Convenience wrapper for callers that don't have a function
/// environment available (e.g. the resolver, which calls this
/// before `expand_decl` runs the full tree-walk pass).
pub fn expand_from(expr: Expr) -> Expr {
    let env = FnEnv::new();
    expand_from_with(expr, &env)
}

/// If `expr` is a `From`, `Exists`, or `Forall` containing one or
/// more Scans over Extents, rewrite it by deriving generators from
/// `where` clauses and using them as the scan sources. Otherwise
/// returns `expr` unchanged.
pub fn expand_from_with(expr: Expr, env: &FnEnv) -> Expr {
    match expr {
        Expr::From(t, steps) => {
            if !has_extent_scan(&steps) {
                return Expr::From(t, steps);
            }
            Expr::From(t, expand_steps(steps, env))
        }
        Expr::Exists(t, steps) => {
            if !has_extent_scan(&steps) {
                return Expr::Exists(t, steps);
            }
            Expr::Exists(t, expand_steps(steps, env))
        }
        Expr::Forall(t, steps) => {
            if !has_extent_scan(&steps) {
                return Expr::Forall(t, steps);
            }
            Expr::Forall(t, expand_steps(steps, env))
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
pub fn expand_decl(decl: Decl) -> Decl {
    let env = FnEnv::new();
    walk_decl(decl, &env)
}

fn walk_decl(decl: Decl, env: &FnEnv) -> Decl {
    match decl {
        Decl::NonRecVal(b) => {
            let mut b2 = (*b).clone();
            b2.expr = walk_expr(b2.expr, env);
            Decl::NonRecVal(Box::new(b2))
        }
        Decl::RecVal(binds) => {
            let mut new_binds = Vec::with_capacity(binds.len());
            for mut b in binds {
                b.expr = walk_expr(b.expr, env);
                new_binds.push(b);
            }
            Decl::RecVal(new_binds)
        }
        other => other,
    }
}

fn walk_expr(expr: Expr, env: &FnEnv) -> Expr {
    match expr {
        Expr::Let(t, decls, body) => {
            // Extend the environment with single-arg `fn` bindings
            // before recursing into the body.
            let mut env2 = env.clone();
            for d in &decls {
                collect_fn_bindings(d, &mut env2);
            }
            let new_decls: Vec<Decl> =
                decls.into_iter().map(|d| walk_decl(d, &env2)).collect();
            let new_body = Box::new(walk_expr(*body, &env2));
            Expr::Let(t, new_decls, new_body)
        }
        Expr::From(_, _) | Expr::Exists(_, _) | Expr::Forall(_, _) => {
            // Recurse into nested expressions first (so inner
            // sub-queries also benefit from the env), then run the
            // expander on the resulting top-level expression.
            let inner = walk_query_steps(expr, env);
            expand_from_with(inner, env)
        }
        Expr::Apply(t, f, a, span) => Expr::Apply(
            t,
            Box::new(walk_expr(*f, env)),
            Box::new(walk_expr(*a, env)),
            span,
        ),
        Expr::Case(t, subject, arms, span) => Expr::Case(
            t,
            Box::new(walk_expr(*subject, env)),
            arms.into_iter()
                .map(|m| Match {
                    pat: m.pat,
                    expr: walk_expr(m.expr, env),
                })
                .collect(),
            span,
        ),
        Expr::Fn(t, arms, span) => Expr::Fn(
            t,
            arms.into_iter()
                .map(|m| Match {
                    pat: m.pat,
                    expr: walk_expr(m.expr, env),
                })
                .collect(),
            span,
        ),
        Expr::Tuple(t, items) => Expr::Tuple(
            t,
            items.into_iter().map(|e| walk_expr(e, env)).collect(),
        ),
        Expr::List(t, items) => Expr::List(
            t,
            items.into_iter().map(|e| walk_expr(e, env)).collect(),
        ),
        Expr::Aggregate(t, e1, e2) => Expr::Aggregate(
            t,
            Box::new(walk_expr(*e1, env)),
            Box::new(walk_expr(*e2, env)),
        ),
        other => other,
    }
}

/// Walk inside a `From`/`Exists`/`Forall`'s steps so that
/// expressions embedded in `Where`, `Yield`, and other step kinds
/// get the same treatment. The query's outer wrapper is recreated.
fn walk_query_steps(expr: Expr, env: &FnEnv) -> Expr {
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
                    Box::new(walk_expr(*source, env)),
                    cond.map(|c| Box::new(walk_expr(*c, env))),
                ),
                StepKind::Where(c) => {
                    StepKind::Where(Box::new(walk_expr(*c, env)))
                }
                StepKind::Yield(e) => {
                    StepKind::Yield(Box::new(walk_expr(*e, env)))
                }
                StepKind::Order(e) => {
                    StepKind::Order(Box::new(walk_expr(*e, env)))
                }
                StepKind::Compute(e) => {
                    StepKind::Compute(Box::new(walk_expr(*e, env)))
                }
                StepKind::Group(k, a) => StepKind::Group(
                    Box::new(walk_expr(*k, env)),
                    a.map(|e| Box::new(walk_expr(*e, env))),
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
            && let Match { pat, expr } = &arms[0]
        {
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

fn expand_steps(steps: Vec<Step>, env: &FnEnv) -> Vec<Step> {
    // Phase A: derive generators by scanning where-clauses.
    let mut cache = Cache::new();
    derive_generators(&steps, &mut cache, env);

    // Phase B: rebuild the steps. Replace each Scan-over-Extent with
    // the best generator's expression. Decompose every Where into
    // conjuncts and drop those whose text appears in a sealed
    // generator's provenance. Other steps pass through.
    let provenance: Vec<Expr> =
        cache.sealed_provenance().into_iter().cloned().collect();
    let mut out = Vec::with_capacity(steps.len());
    for step in steps {
        match step.kind {
            StepKind::Scan(pat, source, cond)
                if matches!(source.as_ref(), Expr::Extent(_)) =>
            {
                let Pat::Identifier(_, n) = pat.as_ref() else {
                    // Phase 1 only handles plain identifier patterns
                    // for unbounded vars. Compound patterns will be
                    // added in later phases.
                    out.push(Step::new(
                        StepKind::Scan(pat, source, cond),
                        step.env,
                    ));
                    continue;
                };
                let name = n.clone();
                if let Some(generator) = cache.best(&name) {
                    out.push(Step::new(
                        StepKind::Scan(
                            pat,
                            Box::new(generator.exp.clone()),
                            cond,
                        ),
                        step.env,
                    ));
                } else {
                    // No generator — leave the Extent in place; the
                    // compiler will emit the clean error.
                    out.push(Step::new(
                        StepKind::Scan(pat, source, cond),
                        step.env,
                    ));
                }
            }
            StepKind::Where(condition) => {
                let conjuncts = split_conjuncts(&condition);
                let kept: Vec<Expr> = conjuncts
                    .into_iter()
                    .filter(|c| !provenance_contains(&provenance, c))
                    .collect();
                if kept.is_empty() {
                    // Conjunction reduced to true; drop the Where.
                    continue;
                }
                let new_cond = and_all(kept);
                out.push(Step::new(
                    StepKind::Where(Box::new(new_cond)),
                    step.env,
                ));
            }
            other => {
                out.push(Step::new(other, step.env));
            }
        }
    }
    out
}

fn derive_generators(steps: &[Step], cache: &mut Cache, env: &FnEnv) {
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
fn expr_eq(a: &Expr, b: &Expr) -> bool {
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

fn and_all(conjuncts: Vec<Expr>) -> Expr {
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
