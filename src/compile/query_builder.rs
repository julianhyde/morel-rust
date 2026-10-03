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

//! Builds a query's tree as the resolver resolves its steps, which is
//! what morel-java's `StepResolver` does with its `RelBuilder`.
//!
//! Each step is shaped by [`FromBuilder`] -- the environment it leaves,
//! the `current` it reads, the position it counts -- and translated as
//! soon as no later step can change it, which is every step but the
//! last: a trivial yield is dropped once another step follows it. The
//! step list is kept beside the tree for a query the translator
//! declines, which the step list still carries.

use crate::compile::core::{Expr, Pat};
use crate::compile::from_builder::FromBuilder;
use crate::compile::rel_lowerer;
use crate::compile::rel_translator::{StepTranslator, same_type};
use crate::syntax::ast::JoinType;

/// A query being built, and its tree so far.
pub struct QueryBuilder {
    fb: FromBuilder,
    tree: StepTranslator,
    /// How many of the steps have been translated.
    translated: usize,
    /// Whether the query is inside no other; see [`QueryBuilder::build`].
    outermost: bool,
}

impl QueryBuilder {
    /// Creates a builder for a query, saying whether it is inside no
    /// other.
    pub fn new(outermost: bool) -> QueryBuilder {
        QueryBuilder {
            fb: FromBuilder::new(),
            tree: start(outermost),
            translated: 0,
            outermost,
        }
    }

    /// Starts the query again, as `through` does with what comes after
    /// it.
    pub fn clear(&mut self) {
        self.fb.clear();
        self.tree = start(self.outermost);
        self.translated = 0;
    }

    /// Returns whether the query's rows so far are ordered.
    pub fn is_ordered(&self) -> bool {
        self.fb.is_ordered()
    }

    /// Translates the steps that no later step can change: all but the
    /// last.
    fn sync(&mut self) {
        let steps = self.fb.steps();
        while self.translated + 1 < steps.len() {
            self.tree.step(&steps[self.translated]);
            self.translated += 1;
        }
    }

    pub fn compute(&mut self, e: Expr) {
        self.fb.compute(e);
        self.sync();
    }

    pub fn distinct(&mut self) {
        self.fb.distinct();
        self.sync();
    }

    pub fn except(&mut self, distinct: bool, args: Vec<Expr>) {
        self.fb.except(distinct, args);
        self.sync();
    }

    pub fn group(
        &mut self,
        binder: Option<&str>,
        keys: Expr,
        aggregates: Option<Expr>,
    ) {
        self.fb.group(binder, keys, aggregates);
        self.sync();
    }

    pub fn intersect(&mut self, distinct: bool, args: Vec<Expr>) {
        self.fb.intersect(distinct, args);
        self.sync();
    }

    pub fn order(&mut self, e: Expr) {
        self.fb.order(e);
        self.sync();
    }

    pub fn scan(&mut self, pat: Pat, e: Expr) {
        self.fb.scan(pat, e);
        self.sync();
    }

    pub fn scan_with_condition(
        &mut self,
        pat: Pat,
        e: Expr,
        condition: Option<Expr>,
    ) {
        self.fb.scan_with_condition(pat, e, condition);
        self.sync();
    }

    pub fn scan_with_join(
        &mut self,
        join_type: JoinType,
        pat: Pat,
        e: Expr,
        condition: Option<Expr>,
    ) {
        self.fb.scan_with_join(join_type, pat, e, condition);
        self.sync();
    }

    pub fn skip(&mut self, count: Expr) {
        self.fb.skip(count);
        self.sync();
    }

    pub fn take(&mut self, count: Expr) {
        self.fb.take(count);
        self.sync();
    }

    pub fn union(&mut self, distinct: bool, args: Vec<Expr>) {
        self.fb.union(distinct, args);
        self.sync();
    }

    pub fn unorder(&mut self) {
        self.fb.unorder();
        self.sync();
    }

    pub fn where_(&mut self, condition: Expr) {
        self.fb.where_(condition);
        self.sync();
    }

    pub fn yield_(&mut self, e: Expr) {
        self.fb.yield_(e);
        self.sync();
    }

    pub fn yield_binder(&mut self, binder: &str, e: Expr) {
        self.fb.yield_binder(binder, e);
        self.sync();
    }

    /// Returns the query so far as steps, for `through`, which hands it
    /// to a function and scans what that returns; the query that
    /// encloses it translates it in context.
    pub fn build_steps(&mut self) -> Expr {
        self.fb
            .build_simplify()
            .expect("Failed to build From expression")
    }

    /// Returns the query as the resolver hands it on: its tree, where the
    /// translator can express it, and otherwise its steps.
    ///
    /// The outermost query's tree has the queries nested in it made
    /// trees too, and is checked to lower; a nested query's has the
    /// names of the queries around it free, for the enclosing query's
    /// translation to substitute. A query that is only an unbounded scan
    /// has a leaf for a tree, which says nothing to ground, and stays
    /// steps.
    pub fn build(mut self) -> Expr {
        let query = self.build_steps();
        let Expr::From(t, steps) = &query else {
            return query;
        };
        for step in &steps[self.translated..] {
            self.tree.step(step);
        }
        let tree = self.tree.finish(t);
        let tree = if self.outermost {
            tree.and_then(|tree| rel_lowerer::finished(&tree))
        } else {
            tree
        };
        match tree {
            Some(Expr::Extent(..)) | None => query,
            // The query's type is the resolver's, which keeps the
            // aliases the user wrote; the translation's is the same type
            // with them spelled out.
            Some(Expr::Rel(u, rel)) if self.outermost && same_type(&u, t) => {
                Expr::Rel(t.clone(), rel)
            }
            Some(tree) => tree,
        }
    }
}

/// Starts the translation of a query, inside no other or nested in one.
fn start(outermost: bool) -> StepTranslator {
    if outermost {
        StepTranslator::outermost()
    } else {
        StepTranslator::nested()
    }
}
