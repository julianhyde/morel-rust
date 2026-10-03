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

//! Capture-aware substitution of free identifiers in a Core
//! expression.
//!
//! Used by the predicate-inversion pipeline to inline function
//! bodies and rewrite case-arm conditions.
//! Mirrors morel-java's `compile.Replacer`.
//!
//! The current implementation is the minimum needed for Phase 1+
//! of the port: it walks `Expr`, `Step`, and `Match` nodes,
//! substituting `Expr::Identifier(_, name)` whenever `name` is in
//! the supplied map *and* is not shadowed by an enclosing
//! pattern binding.

use crate::compile::core::{Expr, Match, Pat, PatField, Step, StepKind};
use std::collections::HashMap;

/// Substitutes every free occurrence of `name` (for `(name, expr) ∈
/// map`) with `expr`. Bound occurrences (introduced by patterns in
/// `fn`, `case`, query `Scan`, etc.) are not substituted.
pub fn substitute(expr: &Expr, map: &HashMap<String, Expr>) -> Expr {
    let mut shadow: Vec<String> = Vec::new();
    let no_slots = HashMap::new();
    let selections = Selections {
        name: "",
        slots: &no_slots,
    };
    visit_expr(expr, map, &mut shadow, &selections)
}

/// Which selections of a variable to replace, and with what.
pub struct Selections<'a> {
    /// The variable whose fields are being selected.
    name: &'a str,
    /// The slots to replace, and the expression to replace each with.
    /// A selection of a slot that is not here is left alone.
    slots: &'a HashMap<usize, Expr>,
}

/// Substitutes each `#slot name` named by `selections`.
///
/// Whether the rest of the expression still uses `name` is then a
/// question about free variables: if it does, some use of it was not
/// one of these selections.
pub fn substitute_selections(
    expr: &Expr,
    name: &str,
    slots: &HashMap<usize, Expr>,
) -> Expr {
    let mut shadow: Vec<String> = Vec::new();
    let map = HashMap::new();
    visit_expr(expr, &map, &mut shadow, &Selections { name, slots })
}

fn visit_expr(
    expr: &Expr,
    map: &HashMap<String, Expr>,
    shadow: &mut Vec<String>,
    selections: &Selections<'_>,
) -> Expr {
    match expr {
        // lint: sort until '#}' where '##Expr::'
        Expr::Aggregate(t, e1, e2, s) => Expr::Aggregate(
            t.clone(),
            Box::new(visit_expr(e1, map, shadow, selections)),
            Box::new(visit_expr(e2, map, shadow, selections)),
            s.clone(),
        ),
        Expr::Apply(t, f, a, span) => {
            // A selection of the record on a slot that is being
            // substituted, and not under a binding of the record's name,
            // is replaced by what stands for that slot.
            if let Expr::RecordSelector(_, slot) = f.as_ref()
                && let Expr::Identifier(_, n) = a.as_ref()
                && n == selections.name
                && !shadow.contains(n)
                && let Some(replacement) = selections.slots.get(slot)
            {
                return replacement.clone();
            }
            Expr::Apply(
                t.clone(),
                Box::new(visit_expr(f, map, shadow, selections)),
                Box::new(visit_expr(a, map, shadow, selections)),
                span.clone(),
            )
        }
        Expr::Case(t, subject, arms, span) => Expr::Case(
            t.clone(),
            Box::new(visit_expr(subject, map, shadow, selections)),
            arms.iter()
                .map(|a| visit_match(a, map, shadow, selections))
                .collect(),
            span.clone(),
        ),
        Expr::Current(t) => Expr::Current(t.clone()),
        Expr::Extent(t, span) => Expr::Extent(t.clone(), span.clone()),
        Expr::Fn(t, arms, span) => Expr::Fn(
            t.clone(),
            arms.iter()
                .map(|a| visit_match(a, map, shadow, selections))
                .collect(),
            span.clone(),
        ),
        Expr::From(t, steps) => {
            Expr::From(t.clone(), visit_steps(steps, map, shadow, selections))
        }
        Expr::Identifier(t, name) => {
            if !shadow.contains(name)
                && let Some(replacement) = map.get(name)
            {
                replacement.clone()
            } else {
                Expr::Identifier(t.clone(), name.clone())
            }
        }
        Expr::Let(t, decls, body) => {
            // For Phase 0 we don't model decl-introduced bindings;
            // recurse into the body without shadowing. Phase 3+
            // (function inlining) will refine this when it actually
            // needs to substitute through `let`s.
            Expr::Let(
                t.clone(),
                decls.clone(),
                Box::new(visit_expr(body, map, shadow, selections)),
            )
        }
        Expr::List(t, items) => Expr::List(
            t.clone(),
            items
                .iter()
                .map(|e| visit_expr(e, map, shadow, selections))
                .collect(),
        ),
        Expr::Literal(t, val) => Expr::Literal(t.clone(), val.clone()),
        Expr::Ordinal(t) => Expr::Ordinal(t.clone()),
        Expr::Raise(t, e, span) => Expr::Raise(
            t.clone(),
            Box::new(visit_expr(e, map, shadow, selections)),
            span.clone(),
        ),
        Expr::RecordSelector(t, slot) => Expr::RecordSelector(t.clone(), *slot),
        // A node binds its rows in the children that read them, so they
        // shadow a substitution there and nowhere else.
        Expr::Rel(t, rel) => {
            let base = shadow.clone();
            Expr::Rel(
                t.clone(),
                Box::new(rel.map_scoped(&|e, names| {
                    let mut inner = base.clone();
                    inner.extend(names.iter().map(|(n, _)| n.clone()));
                    visit_expr(e, map, &mut inner, selections)
                })),
            )
        }
        Expr::Tuple(t, items) => Expr::Tuple(
            t.clone(),
            items
                .iter()
                .map(|e| visit_expr(e, map, shadow, selections))
                .collect(),
        ),
    }
}

fn visit_match(
    m: &Match,
    map: &HashMap<String, Expr>,
    shadow: &mut Vec<String>,
    selections: &Selections<'_>,
) -> Match {
    let saved_len = shadow.len();
    collect_pat_bindings(&m.pat, shadow);
    let result = Match {
        pat: m.pat.clone(),
        expr: visit_expr(&m.expr, map, shadow, selections),
    };
    shadow.truncate(saved_len);
    result
}

fn visit_steps(
    steps: &[Step],
    map: &HashMap<String, Expr>,
    shadow: &mut Vec<String>,
    selections: &Selections<'_>,
) -> Vec<Step> {
    let saved_len = shadow.len();
    let mut out = Vec::with_capacity(steps.len());
    for step in steps {
        out.push(visit_step(step, map, shadow, selections));
    }
    shadow.truncate(saved_len);
    out
}

fn visit_step(
    step: &Step,
    map: &HashMap<String, Expr>,
    shadow: &mut Vec<String>,
    selections: &Selections<'_>,
) -> Step {
    let kind = match &step.kind {
        // lint: sort until '#}' where '##StepKind::'
        StepKind::Compute(e) => {
            StepKind::Compute(Box::new(visit_expr(e, map, shadow, selections)))
        }
        StepKind::Distinct => StepKind::Distinct,
        StepKind::Except(d, exprs) => StepKind::Except(
            *d,
            exprs
                .iter()
                .map(|e| visit_expr(e, map, shadow, selections))
                .collect(),
        ),
        StepKind::Exists => StepKind::Exists,
        StepKind::Group(key, agg) => StepKind::Group(
            Box::new(visit_expr(key, map, shadow, selections)),
            agg.as_deref()
                .map(|e| Box::new(visit_expr(e, map, shadow, selections))),
        ),
        StepKind::Intersect(d, exprs) => StepKind::Intersect(
            *d,
            exprs
                .iter()
                .map(|e| visit_expr(e, map, shadow, selections))
                .collect(),
        ),
        StepKind::Order(e) => {
            StepKind::Order(Box::new(visit_expr(e, map, shadow, selections)))
        }
        StepKind::Scan(pat, source, cond) => {
            // Substitute in the source first (it doesn't see the
            // pattern's bindings), then bring the pattern's names into
            // scope before walking the optional join condition. The
            // bindings stay live for subsequent sibling steps; the
            // outer `visit_steps` truncates at the end.
            let new_source =
                Box::new(visit_expr(source, map, shadow, selections));
            collect_pat_bindings(pat, shadow);
            let new_cond = cond
                .as_deref()
                .map(|c| Box::new(visit_expr(c, map, shadow, selections)));
            StepKind::Scan(pat.clone(), new_source, new_cond)
        }
        StepKind::Skip(e) => {
            StepKind::Skip(Box::new(visit_expr(e, map, shadow, selections)))
        }
        StepKind::Take(e) => {
            StepKind::Take(Box::new(visit_expr(e, map, shadow, selections)))
        }
        StepKind::Union(d, exprs) => StepKind::Union(
            *d,
            exprs
                .iter()
                .map(|e| visit_expr(e, map, shadow, selections))
                .collect(),
        ),
        StepKind::Unorder => StepKind::Unorder,
        StepKind::Where(e) => {
            StepKind::Where(Box::new(visit_expr(e, map, shadow, selections)))
        }
        StepKind::Yield(e) => {
            StepKind::Yield(Box::new(visit_expr(e, map, shadow, selections)))
        }
    };
    Step::new(kind, step.env.clone())
}

fn collect_pat_bindings(pat: &Pat, bound: &mut Vec<String>) {
    match pat {
        // lint: sort until '#}' where '##Pat::'
        Pat::As(_, name, inner) => {
            bound.push(name.clone());
            collect_pat_bindings(inner, bound);
        }
        Pat::Cons(_, head, tail) => {
            collect_pat_bindings(head, bound);
            collect_pat_bindings(tail, bound);
        }
        Pat::Constructor(_, _, None)
        | Pat::Literal(_, _)
        | Pat::Wildcard(_) => {}
        Pat::Constructor(_, _, Some(inner)) => {
            collect_pat_bindings(inner, bound)
        }
        Pat::Identifier(_, name) => bound.push(name.clone()),
        Pat::List(_, pats) | Pat::Tuple(_, pats) => {
            for p in pats {
                collect_pat_bindings(p, bound);
            }
        }
        Pat::Record(_, fields, _) => {
            for f in fields {
                match f {
                    PatField::Labeled(_, p) | PatField::Anonymous(p) => {
                        collect_pat_bindings(p, bound);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::span::Span;
    use crate::compile::types::{PrimitiveType, Type};
    use crate::eval::val::Val;
    use std::rc::Rc;

    fn t_int() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Int))
    }

    fn id(name: &str) -> Expr {
        Expr::Identifier(t_int(), name.to_string())
    }

    fn lit_int(n: i32) -> Expr {
        Expr::Literal(t_int(), Val::Int(n))
    }

    #[test]
    fn substitutes_a_free_identifier() {
        let mut map = HashMap::new();
        map.insert("x".to_string(), lit_int(7));
        let e = Expr::Tuple(t_int(), vec![id("x"), id("y")]);
        let r = substitute(&e, &map);
        match &r {
            Expr::Tuple(_, items) => {
                assert!(matches!(items[0], Expr::Literal(_, Val::Int(7))));
                assert!(
                    matches!(&items[1], Expr::Identifier(_, n) if n == "y")
                );
            }
            _ => panic!("expected tuple, got {:?}", r),
        }
    }

    #[test]
    fn does_not_substitute_shadowed_identifier() {
        let mut map = HashMap::new();
        map.insert("x".to_string(), lit_int(7));
        // fn x => x  — the inner `x` is bound by the pattern, not free.
        let pat = Pat::Identifier(t_int(), "x".to_string());
        let arm = Match { pat, expr: id("x") };
        let e = Expr::Fn(t_int(), vec![arm], Span::new(""));
        let r = substitute(&e, &map);
        match &r {
            Expr::Fn(_, arms, _) => match &arms[0].expr {
                Expr::Identifier(_, n) => assert_eq!(n, "x"),
                other => panic!("expected identifier, got {:?}", other),
            },
            _ => panic!("expected Fn, got {:?}", r),
        }
    }

    /// A substitution reaches inside a tree, except where a node binds
    /// the name: a row is a name of its own, which shadows.
    #[test]
    fn substitution_inside_a_tree_stops_at_a_row() {
        use crate::compile::core::{Rel, Row};
        let list = Rc::new(Type::List(t_int()));
        let gt = |a: Expr, b: Expr| {
            let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
            Expr::Apply(
                bool_t,
                Box::new(Expr::Identifier(t_int(), "gt".to_string())),
                Box::new(Expr::Tuple(
                    Rc::new(Type::Tuple(vec![t_int(), t_int()])),
                    vec![a, b],
                )),
                Span::new(""),
            )
        };
        let rel = Rel::Filter(
            Row {
                name: "x".to_string(),
                ordinal: None,
            },
            Box::new(Expr::Identifier(list.clone(), "xs".to_string())),
            Box::new(gt(id("x"), id("y"))),
        );
        let tree = Expr::Rel(list, Box::new(rel));
        let mut map = HashMap::new();
        map.insert("x".to_string(), Expr::Literal(t_int(), Val::Int(1)));
        map.insert("y".to_string(), Expr::Literal(t_int(), Val::Int(2)));
        let out = substitute(&tree, &map);
        let Expr::Rel(_, rel) = out else {
            panic!("a node");
        };
        let Rel::Filter(_, _, condition) = rel.as_ref() else {
            panic!("a filter");
        };
        // `x` is the filter's row, and stays; `y` is outer, and goes.
        assert_eq!(format!("{}", condition), "gt (x, 2)");
    }
}
