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

//! Translates a step list into a relational tree.
//!
//! This is variable elimination. A step list is a sequence of steps
//! each executing in an environment of bindings; a tree's expressions
//! name their input element `$0` and bind nothing. So a binder becomes
//! an expression over `$0` -- the element itself, where the element is
//! that binder's value, otherwise a component or a field of it -- and
//! the binding list disappears, because a node's element type says
//! everything the bindings said.
//!
//! It **declines rather than guesses**: a construct it cannot translate
//! gives `None`, and the caller counts the declines. morel-java's
//! translator does the same, and the count is how it knew when it was
//! finished.
//!
//! Nothing depends on the answer yet. The tree is built beside the step
//! list that does the work, which is what makes this safe to be wrong
//! about: a disagreement shows up as a tree that fails the validator or
//! prints a different plan, with the step list still running the query.

// The translator has no caller outside the tests until the shadow that
// runs it over the corpus lands. Remove when it does.
#![allow(dead_code)]

use crate::compile::core::{
    Expr, JoinKind, Pat, Rel, Step, StepKind, element_type,
};
use crate::compile::free_finder::free_names_in;
use crate::compile::postfix::peel_type;
use crate::compile::span::Span;
use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::val::Val;
use crate::syntax::ast::JoinType;
use std::collections::BTreeMap;
use std::rc::Rc;

/// Translates the query `from steps`, whose type is `query_type`, into
/// a tree; or returns `None` where it declines.
pub fn translate(steps: &[Step], query_type: &Rc<Type>) -> Option<Expr> {
    let mut t = Translator {
        tree: None,
        bindings: Vec::new(),
    };
    for step in steps {
        t.step(step)?;
    }
    let tree = t.tree.take()?;
    if tree.type_() == *query_type {
        return Some(tree);
    }
    // A query with several binders has a row that no step built: the
    // step list carries the binders in an environment, and the tree's
    // element is its inputs' components. So it ends in a projection
    // that names them -- which is where the names a tree does not hold
    // come back. This is also the check: if the projection does not
    // give the query's own type, the translation is wrong and declines
    // rather than printing a plan for a different query.
    let tree = t.name_the_components(tree, query_type)?;
    (tree.type_() == *query_type).then_some(tree)
}

/// Where in its input's element a binder's value is.
///
/// A binder is not an expression until the element type is known, and
/// the element type changes under it: a join makes the element a tuple
/// of components, so a binder that was the whole element becomes the
/// first of them, and the components' own types grow as further inputs
/// join. Holding the path and reading it against the current element
/// keeps every binder right after each step, where holding the
/// expression would leave the earlier ones stale.
#[derive(Clone, Debug)]
enum Path {
    /// The element itself, `$0`.
    Whole,
    /// Component `i` of the element, 1-based as the source writes it.
    Component(usize),
    /// Field `label` of the element, which a `yield` of a record makes.
    Field(String),
}

impl Path {
    /// Returns the expression that reads this path out of an element of
    /// type `elem`.
    fn read(&self, elem: &Rc<Type>) -> Option<Expr> {
        let input = Expr::Input(elem.clone(), 0);
        match self {
            Path::Whole => Some(input),
            Path::Component(i) => {
                let Type::Tuple(types) = peel(elem) else {
                    return None;
                };
                let t = types.get(i - 1)?.clone();
                Some(selector(input, i - 1, t))
            }
            Path::Field(label) => {
                let Type::Record(_, fields) = peel(elem) else {
                    return None;
                };
                let slot = fields.keys().position(|l| l.matches(label))?;
                let t = fields.values().nth(slot)?.clone();
                Some(selector(input, slot, t))
            }
        }
    }
}

/// What a query's binders have become, as the translation walks its
/// steps.
struct Translator {
    /// The tree built so far. `None` before the first step; a query
    /// with no scan gets the unit leaf.
    tree: Option<Expr>,
    /// Where each binder's value is in the current element, in the
    /// order the query bound them.
    bindings: Vec<(String, Path)>,
}

impl Translator {
    /// Translates one step, or declines.
    fn step(&mut self, step: &Step) -> Option<()> {
        // An outer join re-types the names it binds, and that is the
        // one thing this does not do yet.
        if step.join_type != JoinType::Inner {
            return None;
        }
        // A query with no scan iterates over a single element, which
        // is unit, so its leaf is `[()]` -- a leaf its author did not
        // write, and the whole of why the answer has one row rather
        // than none. See spec.md §3.1.
        if self.tree.is_none() && !matches!(step.kind, StepKind::Scan(..)) {
            self.tree = Some(unit_leaf());
        }
        match &step.kind {
            StepKind::Scan(pat, source, condition) => {
                self.scan(pat, source, condition.as_deref())
            }
            StepKind::Where(condition) => {
                let condition = self.rewrite(condition)?;
                self.wrap(|input| Rel::Filter(input, Box::new(condition)))
            }
            StepKind::Yield(e) => self.yield_(e),
            StepKind::Order(e) => {
                let key = self.rewrite(e)?;
                self.wrap(|input| Rel::Sort(input, Box::new(key)))
            }
            StepKind::Skip(n) => {
                let n = self.rewrite(n)?;
                self.wrap(|input| Rel::Skip(input, Box::new(n)))
            }
            StepKind::Take(n) => {
                let n = self.rewrite(n)?;
                self.wrap(|input| Rel::Take(input, Box::new(n)))
            }
            StepKind::Unorder => self.wrap(Rel::Unorder),
            // A set operator's flag is whether it keeps duplicates;
            // the node's is whether it removes them.
            StepKind::Except(all, inputs) => {
                self.set_op(*all, inputs, Rel::Except)
            }
            StepKind::Intersect(all, inputs) => {
                self.set_op(*all, inputs, Rel::Intersect)
            }
            StepKind::Union(all, inputs) => {
                self.set_op(*all, inputs, Rel::Union)
            }
            // Everything else -- group, compute, distinct, exists --
            // needs more than this does, and is declined rather than
            // guessed at.
            _ => None,
        }
    }

    /// Translates a scan: the first is the tree's leaf, and a later one
    /// joins.
    fn scan(
        &mut self,
        pat: &Pat,
        source: &Expr,
        condition: Option<&Expr>,
    ) -> Option<()> {
        // Only a variable pattern for now. A pattern that destructures
        // becomes a projection, and one that can fail becomes a filter
        // and a projection; both are more than this does.
        let Pat::Identifier(_, name) = pat else {
            return None;
        };
        match self.tree.take() {
            None => {
                if condition.is_some() {
                    return None;
                }
                self.tree = Some(source.clone());
                self.bindings = vec![(name.clone(), Path::Whole)];
            }
            Some(left) => {
                // A scan that reads an earlier binder is a dependent
                // join, which carries a binder; and an `on` condition
                // reads the new binder, which is not in scope until the
                // join exists. Both are declined.
                if reads_a_binding(source, &self.bindings)
                    || condition.is_some()
                {
                    self.tree = Some(left);
                    return None;
                }
                let n = components_of(&left) + 1;
                let join = Rel::Join(
                    JoinKind::Inner,
                    None,
                    Box::new(true_literal()),
                    Box::new(left),
                    Box::new(source.clone()),
                );
                let tree = node(join)?;
                // The components concatenate, so a binder that was the
                // whole element becomes the first of them, and one that
                // was a component keeps its index.
                for (_, path) in &mut self.bindings {
                    if matches!(path, Path::Whole) {
                        *path = Path::Component(1);
                    }
                }
                self.bindings.push((name.clone(), Path::Component(n)));
                self.tree = Some(tree);
            }
        }
        Some(())
    }

    /// Translates a `yield`: a projection, whose element is what the
    /// expression builds, and whose value names what the query called
    /// its binders.
    fn yield_(&mut self, e: &Expr) -> Option<()> {
        let value = self.rewrite(e)?;
        let elem = value.type_();
        self.wrap(|input| Rel::Project(input, Box::new(value)))?;
        // After a yield the element is what the yield built, so the
        // binders are its fields -- or the element itself, where the
        // yield is one value with a name.
        self.bindings = match (e, peel(&elem)) {
            (Expr::Tuple(_, _), Type::Record(_, fields)) => fields
                .keys()
                .filter_map(|label| match label {
                    Label::String(name) => {
                        Some((name.clone(), Path::Field(name.clone())))
                    }
                    Label::Ordinal(_) => None,
                })
                .collect(),
            _ => match e.implicit_label() {
                Some(name) => vec![(name, Path::Whole)],
                None => Vec::new(),
            },
        };
        Some(())
    }

    /// Translates a set operator: the tree so far, and the step's
    /// inputs.
    fn set_op(
        &mut self,
        distinct: bool,
        inputs: &[Expr],
        f: impl FnOnce(bool, Vec<Expr>) -> Rel,
    ) -> Option<()> {
        let left = self.tree.take()?;
        let mut all_inputs = vec![left];
        all_inputs.extend(inputs.iter().cloned());
        self.tree = Some(node(f(distinct, all_inputs))?);
        // A set operator's element is its inputs', so the binder that
        // named the element still does.
        Some(())
    }

    /// Adds the projection that builds the query's row out of the
    /// components the tree's element holds.
    fn name_the_components(
        &self,
        tree: Expr,
        query_type: &Rc<Type>,
    ) -> Option<Expr> {
        let row = element_type(query_type)?;
        let Type::Record(_, fields) = peel(&row) else {
            return None;
        };
        let elem = element_type(&tree.type_())?;
        let mut values = Vec::with_capacity(fields.len());
        for label in fields.keys() {
            let Label::String(name) = label else {
                return None;
            };
            let (_, path) =
                self.bindings.iter().find(|(bound, _)| bound == name)?;
            values.push(path.read(&elem)?);
        }
        let value = Expr::Tuple(row, values);
        node(Rel::Project(Box::new(tree), Box::new(value)))
    }

    /// Replaces the tree with a node built over it.
    fn wrap(&mut self, f: impl FnOnce(Box<Expr>) -> Rel) -> Option<()> {
        let input = self.tree.take()?;
        self.tree = Some(node(f(Box::new(input)))?);
        Some(())
    }

    /// Rewrites an expression over the query's binders into one over
    /// `$0`.
    fn rewrite(&self, e: &Expr) -> Option<Expr> {
        let elem = element_type(&self.tree.as_ref()?.type_())?;
        let mut map = BTreeMap::new();
        for (name, path) in &self.bindings {
            map.insert(name.clone(), path.read(&elem)?);
        }
        substitute(e, &map)
    }
}

/// Returns how many components an expression's element has: a join's
/// inputs' components concatenated, and otherwise one.
fn components_of(exp: &Expr) -> usize {
    match exp {
        Expr::Rel(_, rel) => match rel.as_ref() {
            Rel::Join(_, _, _, left, right) => {
                components_of(left) + components_of(right)
            }
            _ => 1,
        },
        _ => 1,
    }
}

/// Builds `#slot e`, reading a field or a component. The printer writes
/// it by the name of the field, or by its 1-based position where the
/// element is a tuple.
fn selector(e: Expr, slot: usize, t: Rc<Type>) -> Expr {
    let selector_type = Rc::new(Type::Fn(e.type_(), t.clone()));
    Expr::Apply(
        t,
        Box::new(Expr::RecordSelector(selector_type, slot)),
        Box::new(e),
        Span::new(""),
    )
}

/// Returns the literal `true`, which a join with no condition carries
/// and the printer omits.
fn true_literal() -> Expr {
    Expr::Literal(
        Rc::new(Type::Primitive(PrimitiveType::Bool)),
        Val::Bool(true),
    )
}

/// Looks through a type alias, as the structural tests here must.
fn peel(t: &Rc<Type>) -> &Type {
    peel_type(t)
}

/// Returns the leaf `[()]`, over which a query with no scan iterates.
fn unit_leaf() -> Expr {
    let unit = Rc::new(Type::Primitive(PrimitiveType::Unit));
    Expr::List(
        Rc::new(Type::List(unit.clone())),
        vec![Expr::Literal(unit, Val::Unit)],
    )
}

/// Builds the expression for a node, with the type it derives.
fn node(rel: Rel) -> Option<Expr> {
    let t = rel.derive_type()?;
    Some(Expr::Rel(t, Box::new(rel)))
}

/// Returns whether `source` reads any of the query's binders, which
/// makes a scan dependent.
fn reads_a_binding(source: &Expr, bindings: &[(String, Path)]) -> bool {
    let free = free_names_in(source);
    bindings.iter().any(|(name, _)| free.contains(name))
}

/// Replaces every identifier named in `map` with the expression it maps
/// to, and declines where an expression is not one it knows how to
/// walk.
fn substitute(e: &Expr, map: &BTreeMap<String, Expr>) -> Option<Expr> {
    Some(match e {
        Expr::Identifier(_, name) => match map.get(name) {
            Some(replacement) => replacement.clone(),
            None => e.clone(),
        },
        Expr::Literal(_, _)
        | Expr::RecordSelector(_, _)
        | Expr::Input(_, _)
        | Expr::Extent(_, _) => e.clone(),
        Expr::Apply(t, f, a, span) => Expr::Apply(
            t.clone(),
            Box::new(substitute(f, map)?),
            Box::new(substitute(a, map)?),
            span.clone(),
        ),
        Expr::Aggregate(t, a, b, span) => Expr::Aggregate(
            t.clone(),
            Box::new(substitute(a, map)?),
            Box::new(substitute(b, map)?),
            span.clone(),
        ),
        Expr::Tuple(t, items) => Expr::Tuple(
            t.clone(),
            items
                .iter()
                .map(|i| substitute(i, map))
                .collect::<Option<Vec<_>>>()?,
        ),
        Expr::List(t, items) => Expr::List(
            t.clone(),
            items
                .iter()
                .map(|i| substitute(i, map))
                .collect::<Option<Vec<_>>>()?,
        ),
        Expr::Raise(t, a, span) => {
            Expr::Raise(t.clone(), Box::new(substitute(a, map)?), span.clone())
        }
        // A construct that binds names of its own, or that is a query
        // in its own right, needs more care than this: a `let` or a
        // `case` may shadow a binder, and a nested query rebinds `$0`.
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use crate::shell::Kernel;

    /// Compiles `code` and returns the plan of the tree it translates
    /// to, or `None` where the translator declines.
    fn tree_of(code: &str) -> Option<String> {
        let mut kernel = Kernel::new(&[]);
        // A plan is longer than the default `stringDepth`, which would
        // truncate it.
        kernel
            .process_statement("Sys.set (\"stringDepth\", ~1)", None)
            .expect("sets stringDepth");
        let statement = format!("Sys.planOf ({})", code);
        let output = kernel
            .process_statement(&statement, None)
            .expect("compiles");
        // `Sys.planOf` returns the plan as a string, so the output is
        // `val it = "..." : string`.
        let start = output.find('"')? + 1;
        let end = output.rfind('"')?;
        let text = output[start..end].replace("\\n", "\n");
        // A step list has no newline in it, and a tree always does.
        text.contains('\n').then_some(text)
    }

    /// A filter over a leaf, which is the smallest tree there is. The
    /// binder `i` is gone, and the condition reads the element.
    #[test]
    fn a_filter_over_a_leaf() {
        assert_eq!(
            tree_of("from i in [1, 2, 3] where i > 1").unwrap(),
            "filter [$0 > 1] : int list\n  [1, 2, 3] : int list\n"
        );
    }

    /// A query with no scan iterates over one unit row, which is a
    /// visible leaf its author did not write.
    #[test]
    fn a_query_with_no_scan_has_a_unit_leaf() {
        assert_eq!(
            tree_of("from yield 1").unwrap(),
            "project [1] : int list\n  [()] : unit list\n"
        );
    }

    /// `order`, `skip` and `take` are nodes of their own, and a sort's
    /// output is a list whatever its input was.
    #[test]
    fn order_skip_and_take_are_nodes() {
        let text =
            tree_of("from i in [3, 1, 2] order i skip 1 take 1").unwrap();
        assert_eq!(
            text,
            "take [1] : int list\n  \
             skip [1] : int list\n    \
             sort [$0] : int list\n      \
             [3, 1, 2] : int list\n"
        );
    }

    /// A join concatenates its inputs' components, and the projection
    /// above it is where the names come back.
    #[test]
    fn a_join_concatenates_and_the_projection_names() {
        let text =
            tree_of("from i in [1, 2], j in [3, 4] where i < j yield {i, j}")
                .unwrap();
        assert!(
            text.starts_with(
                "project [{i = #1 $0, j = #2 $0}] : {i:int, j:int} list\n  \
                 filter [#1 $0 < #2 $0] : (int * int) list\n    join : \
                 (int * int) list\n"
            ),
            "{}",
            text
        );
    }

    /// A set operator carries whether it removes duplicates, and the
    /// plan says `all` where it does not.
    #[test]
    fn a_set_operator_says_whether_it_keeps_duplicates() {
        assert!(
            tree_of("from i in [1, 2] union [3]")
                .unwrap()
                .starts_with("union [all] : int list\n"),
        );
        assert!(
            tree_of("from i in [1, 2] union distinct [3]")
                .unwrap()
                .starts_with("union : int list\n"),
        );
    }

    /// It declines rather than guesses. A `group` is more than this
    /// does, and the plan falls back to the step list.
    #[test]
    fn it_declines_what_it_cannot_translate() {
        assert_eq!(tree_of("from i in [1, 2] group j = i"), None);
        // A scan whose pattern destructures becomes a projection, which
        // is more than this does.
        assert_eq!(tree_of("from (i, j) in [(1, 2)]"), None);
    }

    /// Every tree the translator builds passes the validator.
    #[test]
    fn what_it_builds_is_well_formed() {
        for code in [
            "from i in [1, 2, 3] where i > 1",
            "from i in [1, 2], j in [3, 4] where i < j yield {i, j}",
            "from i in [3, 1, 2] order i skip 1 take 1",
            "from i in [1, 2] union [3]",
            "from yield 1",
        ] {
            let text = tree_of(code).unwrap_or_else(|| {
                panic!("declined: {}", code);
            });
            assert!(
                !text.contains("INVALID"),
                "{} gave an invalid tree: {}",
                code,
                text
            );
        }
    }
}
