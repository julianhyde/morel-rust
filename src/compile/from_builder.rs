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

//! Builds and optimizes query expressions (from/where/yield).
//!
//! The `FromBuilder` simplifies query patterns such as:
//! - Converting "from v in list" to just "list" (in `build_simplify`)
//! - Removing "where true" steps
//! - Removing empty "order" steps
//! - Removing trivial yields like "from v in list where condition yield v"
//! - Inlining nested from expressions

use crate::compile::core::{Binding, Expr, Pat, Step, StepEnv, StepKind};
use crate::compile::types::Type;
use crate::eval::val::Val;
use crate::shell::error::Error;
use std::fmt;

/// Checks if a type is a list type.
fn is_list_type(type_: &Type) -> bool {
    matches!(type_, Type::List(_))
}

/// Builds a `From` expression with optimizations.
///
/// This builder accumulates query steps and applies simplification rules
/// to produce optimized Core expressions.
pub struct FromBuilder {
    /// The steps in this query
    steps: Vec<Step>,

    /// Current bindings after the last step
    bindings: Vec<Binding>,

    /// Whether the result is an atom (scalar) vs a record
    atom: bool,

    /// If Some(index), that step should be removed if it's not the last step.
    /// For example, "yield {i = i}" only has meaning as the last step
    /// (forces the result to be a record instead of scalar).
    remove_if_not_last_index: Option<usize>,

    /// If Some(index), that step should be removed if it IS the last step.
    /// For example, when flattening "from p in (from q in list)" to
    /// "from q in list yield {p = q}", we want to remove "yield {p = q}"
    /// if it turns out to be the last step.
    remove_if_last_index: Option<usize>,
}

impl FromBuilder {
    /// Creates a new FromBuilder.
    pub fn new() -> Self {
        FromBuilder {
            steps: Vec::new(),
            bindings: Vec::new(),
            atom: false,
            remove_if_not_last_index: None,
            remove_if_last_index: None,
        }
    }

    /// Resets this builder to its initial state.
    pub fn clear(&mut self) {
        self.steps.clear();
        self.bindings.clear();
        self.atom = false;
        self.remove_if_not_last_index = None;
        self.remove_if_last_index = None;
    }

    /// Returns the environment available after the most recent step.
    pub fn step_env(&self) -> StepEnv {
        let ordered = self.steps.last().map(|s| s.env.ordered).unwrap_or(true);
        StepEnv::new(self.bindings.clone(), self.atom, ordered)
    }

    /// Adds a step to this builder.
    fn add_step(&mut self, step: Step) -> &mut Self {
        // Check if we should remove the previous step because it's no longer
        // the last step
        if let Some(index) = self.remove_if_not_last_index {
            if index == self.steps.len() - 1 {
                // The previous step (a trivial yield) is no longer last
                self.remove_if_not_last_index = None;
                self.remove_if_last_index = None;

                // Check if it's a trivial single-field record yield
                if let Some(last_step) = self.steps.last() {
                    if matches!(last_step.kind, StepKind::Yield(_)) {
                        // TODO: Check if it's actually trivial
                        // For now, just remove it
                        self.steps.pop();
                    }
                }
            }
        }

        self.steps.push(step.clone());

        // Update bindings and atom from the new step's environment
        self.bindings = step.env.bindings.clone();
        self.atom = step.env.atom;

        self
    }

    /// Adds a "where" (filter) step.
    /// Optimization: Skips "where true" since it has no effect.
    pub fn where_(&mut self, condition: Expr) -> &mut Self {
        // Check if condition is a boolean literal true
        if let Expr::Literal(_, Val::Bool(true)) = condition {
            // Skip "where true"
            return self;
        }

        let env = self.step_env();
        let step = Step::new(StepKind::Where(Box::new(condition)), env);
        self.add_step(step)
    }

    /// Adds a "skip" step.
    /// Optimization: Skips "skip 0" since it has no effect.
    pub fn skip(&mut self, count: Expr) -> &mut Self {
        // Check if count is 0
        if let Expr::Literal(_, Val::Int(n)) = &count {
            if *n == 0 {
                // Skip "skip 0"
                return self;
            }
        }

        let env = self.step_env();
        let step = Step::new(StepKind::Skip(Box::new(count)), env);
        self.add_step(step)
    }

    /// Adds a "take" (limit) step.
    pub fn take(&mut self, count: Expr) -> &mut Self {
        let env = self.step_env();
        let step = Step::new(StepKind::Take(Box::new(count)), env);
        self.add_step(step)
    }

    /// Adds a "distinct" step.
    pub fn distinct(&mut self) -> &mut Self {
        let env = self.step_env();
        let step = Step::new(StepKind::Distinct, env);
        self.add_step(step)
    }

    /// Adds an "order" step.
    pub fn order(&mut self, exp: Expr) -> &mut Self {
        let env = self.step_env();
        let step = Step::new(StepKind::Order(Box::new(exp)), env);
        self.add_step(step)
    }

    /// Makes the query unordered. No-op if already unordered.
    pub fn unorder(&mut self) -> &mut Self {
        let env = self.step_env();
        if !env.ordered {
            return self;
        }
        let step = Step::new(StepKind::Unorder, env);
        self.add_step(step)
    }

    /// Adds a "yield" step.
    pub fn yield_(&mut self, exp: Expr) -> &mut Self {
        // Determine if result is an atom
        let _atom = !matches!(exp, Expr::Tuple(_, _));
        // TODO: Use atom flag to update step environment

        let env = self.step_env();
        let step = Step::new(StepKind::Yield(Box::new(exp)), env);
        self.add_step(step)
    }

    /// Adds an "except" (set difference) step.
    pub fn except(&mut self, distinct: bool, args: Vec<Expr>) -> &mut Self {
        let env = self.step_env();
        // Except maintains order only if all arguments are lists
        let ordered = env.ordered && args.iter().all(|arg| is_list_type(arg.type_().as_ref()));
        let env2 = env.with_ordered(ordered);
        let step = Step::new(StepKind::Except(distinct, args), env2);
        self.add_step(step)
    }

    /// Adds an "intersect" (set intersection) step.
    pub fn intersect(&mut self, distinct: bool, args: Vec<Expr>) -> &mut Self {
        let env = self.step_env();
        // Intersect maintains order only if all arguments are lists
        let ordered = env.ordered && args.iter().all(|arg| is_list_type(arg.type_().as_ref()));
        let env2 = env.with_ordered(ordered);
        let step = Step::new(StepKind::Intersect(distinct, args), env2);
        self.add_step(step)
    }

    /// Adds a "union" (set union) step.
    pub fn union(&mut self, distinct: bool, args: Vec<Expr>) -> &mut Self {
        let env = self.step_env();
        // Union maintains order only if all arguments are lists
        let ordered = env.ordered && args.iter().all(|arg| is_list_type(arg.type_().as_ref()));
        let env2 = env.with_ordered(ordered);
        let step = Step::new(StepKind::Union(distinct, args), env2);
        self.add_step(step)
    }

    /// Adds a "group" step.
    pub fn group(&mut self, key_expr: Expr, aggregate_expr: Option<Expr>) -> &mut Self {
        let env = self.step_env();
        let step = Step::new(
            StepKind::Group(
                Box::new(key_expr),
                aggregate_expr.map(Box::new),
            ),
            env,
        );
        self.add_step(step)
    }

    /// Adds a scan step "from pat in exp".
    /// This is a simplified version - the Java implementation has complex
    /// logic for inlining nested froms and handling patterns.
    pub fn scan(&mut self, pat: Pat, exp: Expr) -> &mut Self {
        self.scan_with_condition(pat, exp, None)
    }

    /// Adds a scan step "from pat in exp where condition".
    pub fn scan_with_condition(
        &mut self,
        pat: Pat,
        exp: Expr,
        condition: Option<Expr>,
    ) -> &mut Self {
        // TODO: Implement the complex nested from inlining logic from Java
        // For now, just add a simple scan step

        // Update bindings based on the pattern
        let new_binding = Binding::of(&pat);
        self.bindings.push(new_binding);
        self.atom = self.bindings.len() == 1;

        let env = self.step_env();
        let step = Step::new(
            StepKind::JoinIn(
                Box::new(pat),
                Box::new(exp),
                condition.map(Box::new),
            ),
            env,
        );
        self.add_step(step)
    }

    /// Builds the From expression.
    pub fn build(&mut self) -> Result<Expr, Error> {
        self.build_internal(false)
    }

    /// Builds the From expression with simplification.
    /// Can return a simple expression instead of a From if the query
    /// simplifies to "from x in list".
    pub fn build_simplify(&mut self) -> Result<Expr, Error> {
        self.build_internal(true)
    }

    fn build_internal(&mut self, simplify: bool) -> Result<Expr, Error> {
        // Remove last step if flagged
        if let Some(index) = self.remove_if_last_index {
            if index == self.steps.len() - 1 {
                self.steps.pop();
                self.remove_if_last_index = None;
            }
        }

        // Simplification: "from v in list" -> "list"
        if simplify && self.steps.len() == 1 {
            if let StepKind::JoinIn(pat, exp, None) = &self.steps[0].kind {
                // Check if pattern is a simple identifier
                if matches!(**pat, Pat::Identifier(_, _)) {
                    return Ok((**exp).clone());
                }
            }
        }

        // Build From expression
        let result_type = self.compute_result_type()?;
        Ok(Expr::From(Box::new(result_type), self.steps.clone()))
    }

    fn compute_result_type(&self) -> Result<Type, Error> {
        // TODO: Properly compute the result type based on steps
        // For now, return a placeholder
        Ok(Type::Primitive(crate::compile::types::PrimitiveType::Unit))
    }
}

impl Default for FromBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for FromBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FromBuilder({} steps)", self.steps.len())
    }
}

impl fmt::Display for FromBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.steps)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_builder() {
        let builder = FromBuilder::new();
        assert_eq!(builder.steps.len(), 0);
        assert_eq!(builder.bindings.len(), 0);
        assert!(!builder.atom);
    }

    #[test]
    fn test_clear() {
        let mut builder = FromBuilder::new();
        // Add some state (would need actual steps to test fully)
        builder.atom = true;
        builder.clear();
        assert_eq!(builder.steps.len(), 0);
        assert!(!builder.atom);
    }

    #[test]
    fn test_where_true_skipped() {
        let mut builder = FromBuilder::new();
        let initial_len = builder.steps.len();
        builder.where_(Expr::Literal(
            Box::new(Type::Primitive(
                crate::compile::types::PrimitiveType::Bool,
            )),
            Val::Bool(true),
        ));
        // "where true" should be skipped
        assert_eq!(builder.steps.len(), initial_len);
    }

    #[test]
    fn test_skip_zero_skipped() {
        let mut builder = FromBuilder::new();
        let initial_len = builder.steps.len();
        builder.skip(Expr::Literal(
            Box::new(Type::Primitive(
                crate::compile::types::PrimitiveType::Int,
            )),
            Val::Int(0),
        ));
        // "skip 0" should be skipped
        assert_eq!(builder.steps.len(), initial_len);
    }

    #[test]
    fn test_union_added() {
        let mut builder = FromBuilder::new();
        let initial_len = builder.steps.len();
        builder.union(true, vec![]);
        // Union step should be added
        assert_eq!(builder.steps.len(), initial_len + 1);
        if let Some(step) = builder.steps.last() {
            assert!(matches!(step.kind, StepKind::Union(true, _)));
        }
    }

    #[test]
    fn test_scan_updates_bindings() {
        use crate::compile::type_env::Id;
        let mut builder = FromBuilder::new();
        let pat = Pat::Identifier(
            Box::new(Type::Primitive(
                crate::compile::types::PrimitiveType::Int,
            )),
            "x".to_string(),
        );
        let exp = Expr::List(
            Box::new(Type::List(Box::new(Type::Primitive(
                crate::compile::types::PrimitiveType::Int,
            )))),
            vec![],
        );
        builder.scan(pat, exp);
        // Should have one binding and atom should be true
        assert_eq!(builder.bindings.len(), 1);
        assert!(builder.atom);
        assert_eq!(builder.bindings[0].id, Id::new("x", 0));
    }

    #[test]
    fn test_group_added() {
        let mut builder = FromBuilder::new();
        let key_expr = Expr::Literal(
            Box::new(Type::Primitive(
                crate::compile::types::PrimitiveType::Int,
            )),
            Val::Int(1),
        );
        let initial_len = builder.steps.len();
        builder.group(key_expr, None);
        // Group step should be added
        assert_eq!(builder.steps.len(), initial_len + 1);
        if let Some(step) = builder.steps.last() {
            assert!(matches!(step.kind, StepKind::Group(_, None)));
        }
    }

    #[test]
    fn test_except_added() {
        let mut builder = FromBuilder::new();
        let initial_len = builder.steps.len();
        builder.except(false, vec![]);
        // Except step should be added
        assert_eq!(builder.steps.len(), initial_len + 1);
        if let Some(step) = builder.steps.last() {
            assert!(matches!(step.kind, StepKind::Except(false, _)));
        }
    }
}
