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

use crate::compile::core::{Expr, Pat, Step, StepKind};
use crate::compile::generator::Cache;
use crate::compile::generators::{maybe_generator, split_conjuncts};
use crate::compile::library::BuiltInFunction;
use crate::compile::span::Span;
use crate::compile::types::Type;
use crate::eval::val::Val;

/// If `expr` is a `From`, `Exists`, or `Forall` containing one or
/// more Scans over Extents, rewrite it by deriving generators from
/// `where` clauses and using them as the scan sources. Otherwise
/// returns `expr` unchanged.
pub fn expand_from(expr: Expr) -> Expr {
    match expr {
        Expr::From(t, steps) => {
            if !has_extent_scan(&steps) {
                return Expr::From(t, steps);
            }
            Expr::From(t, expand_steps(steps))
        }
        Expr::Exists(t, steps) => {
            if !has_extent_scan(&steps) {
                return Expr::Exists(t, steps);
            }
            Expr::Exists(t, expand_steps(steps))
        }
        Expr::Forall(t, steps) => {
            if !has_extent_scan(&steps) {
                return Expr::Forall(t, steps);
            }
            Expr::Forall(t, expand_steps(steps))
        }
        _ => expr,
    }
}

fn has_extent_scan(steps: &[Step]) -> bool {
    steps.iter().any(|s| {
        matches!(&s.kind,
            StepKind::Scan(_, source, _)
                if matches!(source.as_ref(), Expr::Extent(_)))
    })
}

fn expand_steps(steps: Vec<Step>) -> Vec<Step> {
    // Phase A: derive generators by scanning where-clauses.
    let mut cache = Cache::new();
    derive_generators(&steps, &mut cache);

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

fn derive_generators(steps: &[Step], cache: &mut Cache) {
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
            maybe_generator(cache, pat, name, t, ordered, &all_constraints);
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
        let bool_t = Box::new(Type::Primitive(
            crate::compile::types::PrimitiveType::Bool,
        ));
        let pair_t =
            Box::new(Type::Tuple(vec![(*bool_t).clone(), (*bool_t).clone()]));
        let fn_t = Box::new(Type::Fn(pair_t.clone(), bool_t.clone()));
        let fn_expr =
            Expr::Literal(fn_t, Val::Fn(BuiltInFunction::BoolAndAlso));
        let arg = Expr::Tuple(pair_t, vec![lhs, rhs]);
        Expr::Apply(bool_t, Box::new(fn_expr), Box::new(arg), Span::new(""))
    })
}
