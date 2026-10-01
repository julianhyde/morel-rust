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

//! Lowers a relational tree into the form that executes: a `from`
//! whose steps bind names, which the compiler turns into a
//! pipeline. It is morel-java's `RelLowerer`.
//!
//! This is the reverse of the translation: the step list survives
//! as an unprinted lowering artifact. Where the translation
//! eliminates variables, the lowering reintroduces them.
//!
//! It linearizes. The tree is left-deep after translation, so one
//! step list carries the whole left spine rather than each node
//! nesting a query of its own. What makes that work is carrying a
//! node's element as an *expression* over the step list's bindings
//! instead of materializing it: a projection then changes the
//! expression, not the steps, and `from e in emps, d in depts where
//! p` lowers back to the three steps it began as.
//!
//! The element is materialized, by a yield, only where something
//! needs the row itself: before a sort, which reads it, and at the
//! end.

use crate::compile::core::{
    Decl, Expr, JoinKind, JoinRows, Match, Pat, Rel, Row, Step, StepKind,
    ValBind, element_type,
};
use crate::compile::expander::expr_eq;
use crate::compile::from_builder::{FromBuilder, ORDINAL_FIELD_PREFIX};
use crate::compile::library::BuiltInFunction;
use crate::compile::postfix::peel_type;
use crate::compile::rel_translator;
use crate::compile::span::Span;
use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::val::Val;
use crate::syntax::ast::JoinType;
use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::env;
use std::rc::Rc;

/// Lowers a tree into an expression that executes, or returns `None`
/// where it cannot.
pub fn lower(exp: &Expr) -> Option<Expr> {
    let mut l = Lowerer {};
    let out = l.rel(exp)?;
    l.all(&out)
}

/// Replaces every query in a declaration by its tree lowered back
/// to steps, where the translation and the lowering both succeed. A
/// check of the lowering: what runs is the tree's step list, and the
/// answer says whether the lowering preserved the rows.
pub fn flip_decl(decl: Decl) -> Decl {
    match decl {
        Decl::NonRecVal(b) => Decl::NonRecVal(Box::new(flip_bind(*b))),
        Decl::RecVal(binds) => {
            Decl::RecVal(binds.into_iter().map(flip_bind).collect())
        }
        other => other,
    }
}

fn flip_bind(mut b: ValBind) -> ValBind {
    b.expr = flip_expr(&b.expr);
    b
}

fn flip_arms(arms: &[Match]) -> Vec<Match> {
    arms.iter()
        .map(|m| Match {
            pat: m.pat.clone(),
            expr: flip_expr(&m.expr),
        })
        .collect()
}

/// Flips the queries in an expression, outermost first: a query that
/// translates and lowers is replaced whole, and its nested queries
/// went through the tree with it; one that does not has its nested
/// queries flipped each on its own.
fn flip_expr(e: &Expr) -> Expr {
    if let Expr::From(t, steps) = e
        && let Some(tree) = rel_translator::translate(steps, t)
        && let Some(lowered) = lower(&tree)
    {
        let lowered = scalarize(lowered, t);
        if env::var_os("MOREL_REL_DEBUG").is_some() {
            eprintln!("lowered: {}", lowered);
        }
        return lowered;
    }
    match e {
        // lint: sort until '#}' where '##Expr::'
        Expr::Aggregate(t, a, b, s) => Expr::Aggregate(
            t.clone(),
            Box::new(flip_expr(a)),
            Box::new(flip_expr(b)),
            s.clone(),
        ),
        Expr::Apply(t, a, b, s) => Expr::Apply(
            t.clone(),
            Box::new(flip_expr(a)),
            Box::new(flip_expr(b)),
            s.clone(),
        ),
        Expr::Case(t, subject, arms, s) => Expr::Case(
            t.clone(),
            Box::new(flip_expr(subject)),
            flip_arms(arms),
            s.clone(),
        ),
        Expr::Fn(t, arms, s) => Expr::Fn(t.clone(), flip_arms(arms), s.clone()),
        Expr::From(t, steps) => Expr::From(t.clone(), flip_steps(steps)),
        Expr::Let(t, decls, body) => Expr::Let(
            t.clone(),
            decls.iter().cloned().map(flip_decl).collect(),
            Box::new(flip_expr(body)),
        ),
        Expr::List(t, items) => {
            Expr::List(t.clone(), items.iter().map(flip_expr).collect())
        }
        Expr::Raise(t, a, s) => {
            Expr::Raise(t.clone(), Box::new(flip_expr(a)), s.clone())
        }
        Expr::Tuple(t, items) => {
            Expr::Tuple(t.clone(), items.iter().map(flip_expr).collect())
        }
        _ => e.clone(),
    }
}

/// Makes a lowered query the value its author wrote where the query
/// was one: a `compute` is a keyless group whose one element is the
/// query's value, and the step list says so with a `compute` step
/// in the group's place.
pub(crate) fn scalarize(lowered: Expr, want: &Rc<Type>) -> Expr {
    if element_type(want).is_some() {
        return lowered;
    }
    let Expr::From(_, mut steps) = lowered else {
        return lowered;
    };
    if let Some(last) = steps.last()
        && let StepKind::Group(_, Some(agg)) = &last.kind
    {
        let compute = Step {
            kind: StepKind::Compute(agg.clone()),
            env: last.env.clone(),
            join_type: last.join_type,
        };
        steps.pop();
        steps.push(compute);
    }
    Expr::From(want.clone(), steps)
}

fn flip_steps(steps: &[Step]) -> Vec<Step> {
    steps
        .iter()
        .map(|step| {
            let kind = match &step.kind {
                // lint: sort until '#}' where '##StepKind::'
                StepKind::Compute(e) => {
                    StepKind::Compute(Box::new(flip_expr(e)))
                }
                StepKind::Except(d, es) => {
                    StepKind::Except(*d, es.iter().map(flip_expr).collect())
                }
                StepKind::Group(k, a) => StepKind::Group(
                    Box::new(flip_expr(k)),
                    a.as_ref().map(|a| Box::new(flip_expr(a))),
                ),
                StepKind::Intersect(d, es) => {
                    StepKind::Intersect(*d, es.iter().map(flip_expr).collect())
                }
                StepKind::Order(e) => StepKind::Order(Box::new(flip_expr(e))),
                StepKind::Scan(p, e, c) => StepKind::Scan(
                    p.clone(),
                    Box::new(flip_expr(e)),
                    c.as_ref().map(|c| Box::new(flip_expr(c))),
                ),
                StepKind::Skip(e) => StepKind::Skip(Box::new(flip_expr(e))),
                StepKind::Take(e) => StepKind::Take(Box::new(flip_expr(e))),
                StepKind::Union(d, es) => {
                    StepKind::Union(*d, es.iter().map(flip_expr).collect())
                }
                StepKind::Where(e) => StepKind::Where(Box::new(flip_expr(e))),
                StepKind::Yield(e) => StepKind::Yield(Box::new(flip_expr(e))),
                other => other.clone(),
            };
            Step {
                kind,
                env: step.env.clone(),
                join_type: step.join_type,
            }
        })
        .collect()
}

/// One lowering, of one tree.
struct Lowerer {}

thread_local! {
    /// Numbers the binders every lowering invents. A tree has no
    /// names, so the lowering has to make them, and the compiler
    /// resolves a binder by name within a scope: two queries in one
    /// `let` must not both bind `w$0`, so the count runs across
    /// lowerings.
    static NEXT_NAME: Cell<usize> = const { Cell::new(0) };
}

/// A step list being built, and the binders its steps leave.
struct Builder {
    fb: FromBuilder,
    /// The binders the steps so far leave, in the order they were
    /// bound; each with its type.
    row: Vec<(String, Rc<Type>)>,
    started: bool,
}

impl Lowerer {
    /// Lowers every tree left inside an expression.
    ///
    /// A query may appear wherever an expression may -- the right
    /// input of a dependent join, the argument of `nonEmpty`, a field
    /// of a record -- and the lowering of the tree that holds one does
    /// not reach inside its expressions. What is left there is a
    /// node, and the compiler knows steps, not nodes.
    fn all(&mut self, e: &Expr) -> Option<Expr> {
        Some(match e {
            // lint: sort until '#}' where '##Expr::'
            Expr::Aggregate(t, a, b, s) => Expr::Aggregate(
                t.clone(),
                Box::new(self.all(a)?),
                Box::new(self.all(b)?),
                s.clone(),
            ),
            Expr::Apply(t, a, b, s) => Expr::Apply(
                t.clone(),
                Box::new(self.all(a)?),
                Box::new(self.all(b)?),
                s.clone(),
            ),
            Expr::Case(t, subject, arms, s) => Expr::Case(
                t.clone(),
                Box::new(self.all(subject)?),
                self.all_arms(arms)?,
                s.clone(),
            ),
            Expr::Fn(t, arms, s) => {
                Expr::Fn(t.clone(), self.all_arms(arms)?, s.clone())
            }
            Expr::From(t, steps) => {
                Expr::From(t.clone(), self.all_steps(steps)?)
            }
            Expr::Let(t, decls, body) => {
                let mut out = Vec::with_capacity(decls.len());
                for decl in decls {
                    out.push(self.all_decl(decl)?);
                }
                Expr::Let(t.clone(), out, Box::new(self.all(body)?))
            }
            Expr::List(t, items) => Expr::List(
                t.clone(),
                items
                    .iter()
                    .map(|i| self.all(i))
                    .collect::<Option<Vec<_>>>()?,
            ),
            Expr::Raise(t, a, s) => {
                Expr::Raise(t.clone(), Box::new(self.all(a)?), s.clone())
            }
            Expr::Rel(_, _) => {
                let lowered = self.rel(e)?;
                self.all(&lowered)?
            }
            Expr::Tuple(t, items) => Expr::Tuple(
                t.clone(),
                items
                    .iter()
                    .map(|i| self.all(i))
                    .collect::<Option<Vec<_>>>()?,
            ),
            _ => e.clone(),
        })
    }

    fn all_arms(&mut self, arms: &[Match]) -> Option<Vec<Match>> {
        arms.iter()
            .map(|m| {
                Some(Match {
                    pat: m.pat.clone(),
                    expr: self.all(&m.expr)?,
                })
            })
            .collect()
    }

    fn all_decl(&mut self, decl: &Decl) -> Option<Decl> {
        Some(match decl {
            Decl::NonRecVal(b) => {
                let mut bind = b.as_ref().clone();
                bind.expr = self.all(&b.expr)?;
                Decl::NonRecVal(Box::new(bind))
            }
            Decl::RecVal(binds) => Decl::RecVal(
                binds
                    .iter()
                    .map(|b| {
                        let mut bind = b.clone();
                        bind.expr = self.all(&b.expr)?;
                        Some(bind)
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
            other => other.clone(),
        })
    }

    fn all_steps(&mut self, steps: &[Step]) -> Option<Vec<Step>> {
        steps
            .iter()
            .map(|step| {
                let kind = match &step.kind {
                    // lint: sort until '#}' where '##StepKind::'
                    StepKind::Compute(e) => {
                        StepKind::Compute(Box::new(self.all(e)?))
                    }
                    StepKind::Except(d, es) => {
                        StepKind::Except(*d, self.all_list(es)?)
                    }
                    StepKind::Group(k, a) => StepKind::Group(
                        Box::new(self.all(k)?),
                        match a {
                            None => None,
                            Some(a) => Some(Box::new(self.all(a)?)),
                        },
                    ),
                    StepKind::Intersect(d, es) => {
                        StepKind::Intersect(*d, self.all_list(es)?)
                    }
                    StepKind::Order(e) => {
                        StepKind::Order(Box::new(self.all(e)?))
                    }
                    StepKind::Scan(p, e, c) => StepKind::Scan(
                        p.clone(),
                        Box::new(self.all(e)?),
                        match c {
                            None => None,
                            Some(c) => Some(Box::new(self.all(c)?)),
                        },
                    ),
                    StepKind::Skip(e) => StepKind::Skip(Box::new(self.all(e)?)),
                    StepKind::Take(e) => StepKind::Take(Box::new(self.all(e)?)),
                    StepKind::Union(d, es) => {
                        StepKind::Union(*d, self.all_list(es)?)
                    }
                    StepKind::Where(e) => {
                        StepKind::Where(Box::new(self.all(e)?))
                    }
                    StepKind::Yield(e) => {
                        StepKind::Yield(Box::new(self.all(e)?))
                    }
                    other => other.clone(),
                };
                Some(Step {
                    kind,
                    env: step.env.clone(),
                    join_type: step.join_type,
                })
            })
            .collect()
    }

    fn all_list(&mut self, es: &[Expr]) -> Option<Vec<Expr>> {
        es.iter().map(|e| self.all(e)).collect()
    }

    /// Lowers a node into an expression of collection type. A leaf is
    /// already an expression.
    fn rel(&mut self, exp: &Expr) -> Option<Expr> {
        let Expr::Rel(t, _) = exp else {
            return Some(exp.clone());
        };
        let mut b = Builder {
            fb: FromBuilder::new(),
            row: Vec::new(),
            started: false,
        };
        let element = self.into(&mut b, exp)?;
        b.finish(element);
        let built = b.fb.build_simplify().ok()?;
        // The query has the type the tree had, whatever the steps'
        // bindings say it should be.
        Some(match built {
            Expr::From(_, steps) => Expr::From(t.clone(), steps),
            other => other,
        })
    }

    /// Appends the steps for a node, and returns an expression, over
    /// the step list's bindings, that denotes the node's element.
    fn into(&mut self, b: &mut Builder, exp: &Expr) -> Option<Expr> {
        let Expr::Rel(_, rel) = exp else {
            return self.scan(b, exp);
        };
        match rel.as_ref() {
            // lint: sort until '#}' where '##Rel::'
            Rel::Except(distinct, args) => self.set_rel(
                b,
                args,
                |fb, d, a| {
                    fb.except(d, a);
                },
                *distinct,
            ),
            Rel::Filter(row, input, condition) => {
                let element = self.into(b, input)?;
                let (element, names) = self.counted(b, element, row);
                b.where_(replace_names(condition, &names));
                Some(element)
            }
            Rel::Group(row, input, keys, aggregates) => {
                self.group(b, row, input, keys, aggregates)
            }
            Rel::Intersect(distinct, args) => self.set_rel(
                b,
                args,
                |fb, d, a| {
                    fb.intersect(d, a);
                },
                *distinct,
            ),
            Rel::Join(kind, rows, condition, left, right) => {
                let dependent = rel.is_dependent();
                self.join(b, *kind, rows, dependent, condition, left, right)
            }
            Rel::Project(row, input, e) => {
                // A projection changes the element, not the steps;
                // nothing is emitted unless a later step needs the row
                // -- except for an ordinal, which counts rows: only a
                // step evaluates its expression exactly once per row.
                let element = self.into(b, input)?;
                let (_, names) = self.counted(b, element, row);
                let out = replace_names(e, &names);
                if out.uses_ordinal() {
                    return Some(self.materialize(b, out));
                }
                if is_group(input) {
                    // A group's element is a record whether it has one
                    // label or many, so a projection over one says
                    // "the field, not the record" -- a difference the
                    // deferred element cannot carry, because a row of
                    // one binding and that binding's value are the
                    // same expression. The yield says it.
                    return Some(self.yielded(b, out));
                }
                Some(out)
            }
            Rel::Skip(input, count) => {
                let element = self.into(b, input)?;
                b.fb.skip(count.as_ref().clone());
                Some(element)
            }
            Rel::Sort(row, input, key) => {
                // A sort reads the element, so a projection above it
                // must be paid for here rather than deferred.
                let element = self.into(b, input)?;
                let element = self.materialize(b, element);
                let (element, names) = self.counted(b, element, row);
                b.fb.order(replace_names(key, &names));
                Some(element)
            }
            Rel::Take(input, count) => {
                let element = self.into(b, input)?;
                b.fb.take(count.as_ref().clone());
                Some(element)
            }
            Rel::Union(distinct, args) => self.set_rel(
                b,
                args,
                |fb, d, a| {
                    fb.union(d, a);
                },
                *distinct,
            ),
            Rel::Unorder(input) => {
                let element = self.into(b, input)?;
                b.fb.unorder();
                Some(element)
            }
        }
    }

    /// Lowers a join: the right input becomes a scan beside the left's
    /// steps, which is what makes the whole left spine one step list.
    #[allow(clippy::too_many_arguments)]
    fn join(
        &mut self,
        b: &mut Builder,
        kind: JoinKind,
        rows: &JoinRows,
        dependent: bool,
        condition: &Expr,
        left: &Expr,
        right: &Expr,
    ) -> Option<Expr> {
        let left_element = self.into(b, left)?;
        let mut right_tree = right.clone();
        if dependent {
            // A dependent join reads the left element through its
            // left row; in a step list the collection is an expression
            // beside the bindings, so the row becomes the element.
            right_tree = substitute_name(right, &rows.left, &left_element);
        }
        let right_lowered = self.rel(&right_tree)?;
        let right_elem = element_type(&right_lowered.type_())?;
        let name = self.fresh_name();
        let pat = Pat::Identifier(right_elem.clone(), name.clone());
        let right_element = Expr::Identifier(right_elem.clone(), name.clone());
        let join_type = match kind {
            JoinKind::Full => JoinType::Full,
            JoinKind::Inner => JoinType::Inner,
            JoinKind::Left => JoinType::Left,
            JoinKind::Right => JoinType::Right,
        };
        let tested = replace_names(
            condition,
            &BTreeMap::from([
                (rows.left.clone(), left_element.clone()),
                (rows.right.clone(), right_element.clone()),
            ]),
        );
        if join_type == JoinType::Inner {
            b.fb.scan_with_join(join_type, pat, right_lowered, None);
            b.row.push((name, right_elem));
            b.started = true;
            b.where_(tested);
        } else {
            // An outer join's condition is evaluated on candidate
            // pairs, where both elements are present, so it reads them
            // as they are.
            b.fb.scan_with_join(join_type, pat, right_lowered, Some(tested));
            b.row.push((name, right_elem));
            b.started = true;
        }
        Some(join_element(left, right, left_element, right_element))
    }

    /// Lowers a group: its keys and aggregates become the step's, and
    /// its element is the record they build.
    fn group(
        &mut self,
        b: &mut Builder,
        row: &Row,
        input: &Expr,
        keys: &[(Label, Expr)],
        aggregates: &[(Label, Expr)],
    ) -> Option<Expr> {
        let element = self.into(b, input)?;
        let (_, names) = self.counted(b, element, row);
        // A key the query named "current" is a row nothing named, and
        // the step list's builder treats a binding of that name as
        // the row rather than a field, so it is renamed.
        let keys: Vec<(Label, Expr)> = keys
            .iter()
            .map(|(label, e)| match label {
                Label::String(name) if name == "current" => {
                    (Label::String(self.fresh_name()), e.clone())
                }
                _ => (label.clone(), e.clone()),
            })
            .collect();
        let key_expr = if keys.is_empty() {
            Expr::Tuple(Rc::new(Type::Primitive(PrimitiveType::Unit)), vec![])
        } else {
            labelled_record(&keys, |e| replace_names(e, &names))
        };
        let agg_expr = if aggregates.is_empty() {
            None
        } else {
            Some(labelled_record(aggregates, |e| {
                replace_names(&aggregate_fns(e, &keys), &names)
            }))
        };
        b.fb.group(None, key_expr, agg_expr);
        b.started = true;
        b.row =
            b.fb.step_env()
                .bindings
                .iter()
                .map(|bd| (bd.id.name.clone(), bd.type_.clone()))
                .collect();
        // A record whether there is one label or many, because that is
        // what the tree's group builds.
        Some(record_of(&b.row))
    }

    /// Lowers a set operator, whose inputs are collections rather than
    /// steps, so the row is needed first.
    fn set_rel(
        &mut self,
        b: &mut Builder,
        args: &[Expr],
        add: impl FnOnce(&mut FromBuilder, bool, Vec<Expr>),
        distinct: bool,
    ) -> Option<Expr> {
        let element = self.into(b, &args[0])?;
        let element = self.materialize(b, element);
        let mut rest = Vec::with_capacity(args.len() - 1);
        for arg in &args[1..] {
            rest.push(self.rel(arg)?);
        }
        add(&mut b.fb, distinct, rest);
        Some(element)
    }

    /// Adds a scan of a collection, binding its element to a fresh
    /// name, and returns the expression that denotes it.
    fn scan(&mut self, b: &mut Builder, collection: &Expr) -> Option<Expr> {
        if is_unit_collection(collection) {
            // The inverse of the translation's unit collection: a
            // query with no scan iterates over one row, which is unit,
            // and the tree says so with a leaf holding that one row. A
            // step list says it by having no scan.
            return Some(Expr::Literal(
                Rc::new(Type::Primitive(PrimitiveType::Unit)),
                Val::Unit,
            ));
        }
        let lowered = self.rel(collection)?;
        let elem = element_type(&lowered.type_())?;
        let name = self.fresh_name();
        let pat = Pat::Identifier(elem.clone(), name.clone());
        b.fb.scan(pat, lowered);
        b.row.push((name.clone(), elem.clone()));
        b.started = true;
        Some(Expr::Identifier(elem, name))
    }

    /// Returns what a node's row and its position denote, as the steps
    /// for the node's own expressions read them.
    ///
    /// A node that counts its rows has the position yielded beside the
    /// element first, because only a yield evaluates its expression
    /// exactly once for each row that reaches it; a counter read where
    /// it is used -- in a sort's key, while the rows are being sorted --
    /// would count something else. This is what the resolver does when
    /// a step list's step reads `ordinal`. The element returned is the
    /// one read out of what was yielded.
    fn counted(
        &mut self,
        b: &mut Builder,
        element: Expr,
        row: &Row,
    ) -> (Expr, BTreeMap<String, Expr>) {
        let Some(ordinal) = &row.ordinal else {
            let names = BTreeMap::from([(row.name.clone(), element.clone())]);
            return (element, names);
        };
        // A record of two binders, the position's named as the
        // resolver names the field it puts `ordinal` in, which is the
        // shape the compiler knows a counted row by. A pair under one
        // binder is not: a query nested in a yield that read an
        // enclosing `let` through it read the wrong slot.
        let element_name = self.fresh_name();
        let ordinal_name = format!("{}{}", ORDINAL_FIELD_PREFIX, element_name);
        let row_vars = vec![
            (element_name.clone(), element.type_()),
            (ordinal_name.clone(), int_type()),
        ];
        let Expr::Tuple(t, vars) = record_of(&row_vars) else {
            unreachable!()
        };
        let values = vars
            .into_iter()
            .map(|var| match &var {
                Expr::Identifier(_, n) if *n == ordinal_name => {
                    Expr::Ordinal(int_type())
                }
                _ => element.clone(),
            })
            .collect();
        b.fb.yield_(Expr::Tuple(t, values));
        b.row = row_vars;
        b.started = true;
        let element = Expr::Identifier(element.type_(), element_name);
        let names = BTreeMap::from([
            (row.name.clone(), element.clone()),
            (ordinal.clone(), Expr::Identifier(int_type(), ordinal_name)),
        ]);
        (element, names)
    }

    /// Makes the element the step list's row, where it is not that
    /// already, and returns the expression that denotes it afterwards.
    fn materialize(&mut self, b: &mut Builder, element: Expr) -> Expr {
        if b.is_row(&element) {
            return element;
        }
        self.yielded(b, element)
    }

    /// Yields an element, whether or not it is already the row.
    fn yielded(&mut self, b: &mut Builder, element: Expr) -> Expr {
        let name = self.fresh_name();
        let t = element.type_();
        b.fb.yield_binder(&name, element);
        b.row = vec![(name.clone(), t.clone())];
        b.started = true;
        Expr::Identifier(t, name)
    }

    /// Creates a binder the lowering needs and the query did not
    /// write. Its prefix is the lowering's own, so that a tree's `v$`
    /// and a lowering's `w$` do not interleave when a plan renumbers
    /// them.
    fn fresh_name(&mut self) -> String {
        NEXT_NAME.with(|cell| {
            let n = cell.get();
            cell.set(n + 1);
            format!("w${}", n)
        })
    }
}

impl Builder {
    /// Filters the rows, and emits no step for a condition that is the
    /// literal `true`.
    fn where_(&mut self, condition: Expr) {
        if let Expr::Literal(_, Val::Bool(true)) = condition {
            return;
        }
        self.fb.where_(condition);
    }

    /// Makes the element the query's result. A trailing yield says
    /// "this is the value", where a mid-query one rebinds; and where
    /// the element is already what the steps leave, neither is needed.
    fn finish(&mut self, element: Expr) {
        if self.is_row(&element) {
            return;
        }
        self.fb.yield_(element);
    }

    /// Reports whether an expression is already what the steps leave:
    /// the one binder's value where there is one binder, and otherwise
    /// the record of them all, in label order.
    fn is_row(&self, element: &Expr) -> bool {
        if self.row.len() == 1 {
            return matches!(element, Expr::Identifier(_, name)
                if *name == self.row[0].0);
        }
        let Expr::Tuple(t, args) = element else {
            return false;
        };
        let Type::Record(_, fields) = peel_type(t) else {
            return false;
        };
        if args.len() != self.row.len() || fields.len() != self.row.len() {
            return false;
        }
        let mut sorted: Vec<&(String, Rc<Type>)> = self.row.iter().collect();
        sorted.sort_by(|x, y| label_cmp(&x.0, &y.0));
        for ((label, _), (arg, (name, _))) in
            fields.iter().zip(args.iter().zip(sorted))
        {
            let Label::String(label) = label else {
                return false;
            };
            if label != name {
                return false;
            }
            if !matches!(arg, Expr::Identifier(_, n) if n == name) {
                return false;
            }
        }
        true
    }
}

/// Compares two labels as a record orders its fields.
fn label_cmp(x: &str, y: &str) -> Ordering {
    Label::String(x.to_string()).cmp(&Label::String(y.to_string()))
}

/// The record of some binders' values, whether there is one of them
/// or many, in label order.
fn record_of(row: &[(String, Rc<Type>)]) -> Expr {
    let mut fields: BTreeMap<Label, Rc<Type>> = BTreeMap::new();
    for (name, t) in row {
        fields.insert(Label::String(name.clone()), t.clone());
    }
    let args = fields
        .iter()
        .map(|(label, t)| {
            let Label::String(name) = label else {
                unreachable!()
            };
            Expr::Identifier(t.clone(), name.clone())
        })
        .collect();
    Expr::Tuple(Rc::new(Type::Record(false, fields)), args)
}

/// A record whose fields are some labelled expressions, each
/// rewritten.
fn labelled_record(
    parts: &[(Label, Expr)],
    rewrite: impl Fn(&Expr) -> Expr,
) -> Expr {
    let mut fields: BTreeMap<Label, Rc<Type>> = BTreeMap::new();
    let mut values: BTreeMap<Label, Expr> = BTreeMap::new();
    for (label, e) in parts {
        let e = rewrite(e);
        fields.insert(label.clone(), e.type_());
        values.insert(label.clone(), e);
    }
    let args = values.into_values().collect();
    Expr::Tuple(Rc::new(Type::Record(false, fields)), args)
}

/// Prepares the aggregates of a group for the step list: a function
/// that names a key through the element names the key's binder
/// instead, because the steps evaluate it once per group, where the
/// element is no longer at hand; and a bag aggregate the translation
/// composed with a converter is the aggregate itself, because the
/// step list's aggregates take a list as they find it.
fn aggregate_fns(e: &Expr, keys: &[(Label, Expr)]) -> Expr {
    match e {
        Expr::Aggregate(t, f, arg, span) => {
            let mut f = unconverted(f);
            for (label, key) in keys {
                if let Label::String(name) = label {
                    let binder = Expr::Identifier(key.type_(), name.clone());
                    f = replace_expr(&f, key, &binder);
                }
            }
            Expr::Aggregate(
                t.clone(),
                Box::new(f),
                Box::new(aggregate_fns(arg, keys)),
                span.clone(),
            )
        }
        _ => map_children(e, &|x| aggregate_fns(x, keys)),
    }
}

/// The aggregate a converter was composed with, or the function
/// itself: `fn col$0 => sum (Bag.fromList col$0)` is `sum`.
fn unconverted(f: &Expr) -> Expr {
    if let Expr::Fn(_, arms, _) = f
        && let [
            Match {
                pat: Pat::Identifier(_, param),
                expr: Expr::Apply(_, g, arg, _),
            },
        ] = arms.as_slice()
        && param.starts_with("col$")
        && let Expr::Apply(_, converter, inner, _) = arg.as_ref()
        && matches!(
            converter.as_ref(),
            Expr::Literal(_, Val::Fn(BuiltInFunction::BagFromList))
        )
        && matches!(inner.as_ref(), Expr::Identifier(_, n) if n == param)
    {
        return g.as_ref().clone();
    }
    f.clone()
}

/// Replaces every occurrence of an expression, by structure, with
/// another.
fn replace_expr(e: &Expr, target: &Expr, replacement: &Expr) -> Expr {
    if expr_eq(e, target) || e.to_string() == target.to_string() {
        return replacement.clone();
    }
    map_children(e, &|x| replace_expr(x, target, replacement))
}

/// The tuple of a join's components, which is its element.
fn join_element(
    left: &Expr,
    right: &Expr,
    left_element: Expr,
    right_element: Expr,
) -> Expr {
    let mut args = components_of(left, left_element);
    args.extend(components_of(right, right_element));
    if args.len() == 1 {
        return args.remove(0);
    }
    let types = args.iter().map(Expr::type_).collect();
    Expr::Tuple(Rc::new(Type::Tuple(types)), args)
}

/// Reads a node's components out of an expression for its element.
fn components_of(node: &Expr, exp: Expr) -> Vec<Expr> {
    let n = component_count(node);
    if n == 1 {
        return vec![exp];
    }
    (0..n).map(|i| field_at(&exp, i)).collect()
}

/// How many components a node's element has: a join's is its inputs'
/// concatenated, and any other node's is one.
pub(crate) fn component_count(node: &Expr) -> usize {
    match node {
        Expr::Rel(_, rel) => match rel.as_ref() {
            Rel::Join(_, _, _, left, right) => {
                component_count(left) + component_count(right)
            }
            _ => 1,
        },
        _ => 1,
    }
}

/// Reads component `i` (0-based) of an expression: the component
/// itself where the expression is a tuple, and otherwise a selection.
pub(crate) fn field_at(exp: &Expr, i: usize) -> Expr {
    if let Expr::Tuple(_, args) = exp
        && i < args.len()
    {
        return args[i].clone();
    }
    let elem = exp.type_();
    let field_type = match peel_type(&elem) {
        Type::Tuple(types) => types.get(i).cloned(),
        Type::Record(_, fields) => fields.values().nth(i).cloned(),
        _ => None,
    }
    .unwrap_or_else(|| elem.clone());
    let selector_type = Rc::new(Type::Fn(elem, field_type.clone()));
    Expr::Apply(
        field_type,
        Box::new(Expr::RecordSelector(selector_type, i)),
        Box::new(exp.clone()),
        Span::new(""),
    )
}

/// The type of a position, `int`.
fn int_type() -> Rc<Type> {
    Rc::new(Type::Primitive(PrimitiveType::Int))
}

/// Replaces several names at once, so that no substitution can see
/// another's result, folding a selection of a component of each: `#2
/// v$0` where `v$0` is `(a, b)` is `b`. A row's name is unique, so
/// nothing in the expression shadows it.
pub(crate) fn replace_names(e: &Expr, map: &BTreeMap<String, Expr>) -> Expr {
    match e {
        Expr::Identifier(_, name) => match map.get(name) {
            Some(replacement) => replacement.clone(),
            None => e.clone(),
        },
        Expr::Apply(_, fx, a, _)
            if matches!(fx.as_ref(), Expr::RecordSelector(_, _))
                && matches!(a.as_ref(), Expr::Identifier(_, n)
                    if map.contains_key(n)) =>
        {
            let (Expr::RecordSelector(_, slot), Expr::Identifier(_, n)) =
                (fx.as_ref(), a.as_ref())
            else {
                unreachable!()
            };
            field_at(&map[n], *slot)
        }
        Expr::Rel(t, rel) => Expr::Rel(
            t.clone(),
            Box::new(rel.map_children(&|x| replace_names(x, map))),
        ),
        _ => map_children(e, &|x| replace_names(x, map)),
    }
}

/// Replaces a name in an expression, through the nodes of a tree; a
/// generated binder is shadowed by nothing.
pub(crate) fn substitute_name(
    e: &Expr,
    name: &str,
    replacement: &Expr,
) -> Expr {
    let sub = |x: &Expr| substitute_name(x, name, replacement);
    match e {
        Expr::Identifier(_, n) if n == name => replacement.clone(),
        Expr::Rel(t, rel) => {
            Expr::Rel(t.clone(), Box::new(rel.map_children(&sub)))
        }
        _ => map_children(e, &sub),
    }
}

/// Rebuilds an expression with a function applied to each of its
/// immediate sub-expressions.
pub(crate) fn map_children(e: &Expr, f: &dyn Fn(&Expr) -> Expr) -> Expr {
    match e {
        // lint: sort until '#}' where '##Expr::'
        Expr::Aggregate(t, a, b, s) => Expr::Aggregate(
            t.clone(),
            Box::new(f(a)),
            Box::new(f(b)),
            s.clone(),
        ),
        Expr::Apply(t, a, b, s) => {
            Expr::Apply(t.clone(), Box::new(f(a)), Box::new(f(b)), s.clone())
        }
        Expr::Case(t, subject, arms, s) => Expr::Case(
            t.clone(),
            Box::new(f(subject)),
            arms.iter()
                .map(|m| Match {
                    pat: m.pat.clone(),
                    expr: f(&m.expr),
                })
                .collect(),
            s.clone(),
        ),
        Expr::Fn(t, arms, s) => Expr::Fn(
            t.clone(),
            arms.iter()
                .map(|m| Match {
                    pat: m.pat.clone(),
                    expr: f(&m.expr),
                })
                .collect(),
            s.clone(),
        ),
        Expr::Let(t, decls, body) => Expr::Let(
            t.clone(),
            decls
                .iter()
                .map(|d| match d {
                    Decl::NonRecVal(b) => {
                        let mut bind = b.as_ref().clone();
                        bind.expr = f(&b.expr);
                        Decl::NonRecVal(Box::new(bind))
                    }
                    Decl::RecVal(binds) => Decl::RecVal(
                        binds
                            .iter()
                            .map(|b| {
                                let mut bind = b.clone();
                                bind.expr = f(&b.expr);
                                bind
                            })
                            .collect(),
                    ),
                    other => other.clone(),
                })
                .collect(),
            Box::new(f(body)),
        ),
        Expr::List(t, items) => {
            Expr::List(t.clone(), items.iter().map(f).collect())
        }
        Expr::Raise(t, a, s) => {
            Expr::Raise(t.clone(), Box::new(f(a)), s.clone())
        }
        Expr::Tuple(t, items) => {
            Expr::Tuple(t.clone(), items.iter().map(f).collect())
        }
        _ => e.clone(),
    }
}

/// Returns whether a node is a group.
fn is_group(node: &Expr) -> bool {
    matches!(node, Expr::Rel(_, rel) if matches!(rel.as_ref(), Rel::Group(..)))
}

/// Reports whether an expression is the one-unit list a scanless
/// query iterates over.
fn is_unit_collection(exp: &Expr) -> bool {
    matches!(exp, Expr::List(_, items)
        if matches!(items.as_slice(), [Expr::Literal(_, Val::Unit)]))
}
