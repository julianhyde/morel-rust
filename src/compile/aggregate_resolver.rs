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

//! Aggregate resolver for group queries.
//!
//! Handles extraction and resolution of aggregate expressions (e.g., `sum over
//! e.sal`) within group...compute queries.

use crate::compile::core::{Binding, Expr};
use crate::compile::resolver::Resolver;
use crate::compile::type_env::Id;
use crate::compile::types::Type;
use crate::syntax::ast;
use std::collections::HashSet;
use ast::ExprKind;

/// Resolves aggregate expressions within group queries.
///
/// The AggregateResolver extracts aggregate expressions like `sum over e.sal`
/// from compute clauses, creates Core.Aggregate nodes for them, and replaces
/// them with variable references.
///
/// For example, `{x = 1 + (sum over e.sal)}` becomes:
/// - Aggregate: `agg$1 = Aggregate(sum, e.sal)`
/// - Post-expression: `{x = 1 + agg$1}`
pub trait AggregateResolver {
    /// Converts an Ast.Aggregate expression to a Core expression.
    ///
    /// Creates a Core.Aggregate node, adds it to the aggregates list,
    /// and returns an Id reference to the generated aggregate binding.
    ///
    /// # Arguments
    /// * `aggregate` - The AST aggregate expression (function + argument)
    /// * `ordered_agg` - Whether the aggregate expects a list vs bag
    /// * `outer_resolver` - Resolver for the group context (has group keys)
    /// * `id` - Optional name hint for the generated binding
    fn to_core_aggregate(
        &mut self,
        aggregate: &ast::Expr,
        ordered_agg: bool,
        outer_resolver: &Resolver,
        id: Option<&str>,
    ) -> Expr;

    /// Converts an Ast.Elements expression to a Core expression.
    ///
    /// The `elements` keyword refers to the list of rows in a group.
    /// Creates an Aggregate with the identity function.
    ///
    /// # Arguments
    /// * `elements` - The AST elements expression
    /// * `outer_resolver` - Resolver for the group context
    fn to_core_elements(
        &mut self,
        elements: &ast::Expr,
        outer_resolver: &Resolver,
    ) -> Expr;

    /// Returns the list of bindings generated for aggregates.
    ///
    /// These bindings will be available after the group step.
    fn bindings(&self) -> Vec<Binding>;
}

/// Aggregate binding: (name, type, aggregate_expression).
pub type AggregateBinding = (String, Box<Type>, Expr);

/// Implementation of AggregateResolver.
///
/// Tracks:
/// - `group_keys`: The bindings for group key fields
/// - `input_resolver`: Resolver with access to input rows (before grouping)
/// - `aggregates`: List of aggregate bindings being collected
pub struct AggregateResolverImpl<'a> {
    /// Group key bindings (available after grouping).
    pub group_keys: Vec<Binding>,
    /// Whether the input is ordered (list vs bag).
    pub ordered: bool,
    /// Resolver for input context (sees original row bindings).
    pub input_resolver: &'a Resolver<'a>,
    /// List of aggregates being collected: (name, type, aggregate_expr).
    pub aggregates: Vec<AggregateBinding>,
    /// Set of used names (group keys + aggregates) to avoid collisions.
    used_names: HashSet<String>,
}

impl<'a> AggregateResolverImpl<'a> {
    /// Creates a new AggregateResolverImpl.
    pub fn new(
        group_keys: Vec<Binding>,
        ordered: bool,
        input_resolver: &'a Resolver<'a>,
    ) -> Self {
        let mut used_names = HashSet::new();
        for key in &group_keys {
            used_names.insert(key.id.name.clone());
        }

        Self {
            group_keys,
            ordered,
            input_resolver,
            aggregates: Vec::new(),
            used_names,
        }
    }

    /// Generates a unique name based on a base name.
    ///
    /// If `base` is already used, tries `base1`, `base2`, etc.
    fn generate_name(&self, base: &str) -> String {
        let mut name = base.to_string();
        let mut i = 0;
        while self.used_names.contains(&name) {
            i += 1;
            name = format!("{}{}", base, i);
        }
        name
    }
}

impl<'a> AggregateResolver for AggregateResolverImpl<'a> {
    fn to_core_aggregate(
        &mut self,
        aggregate: &ast::Expr,
        _ordered_agg: bool,
        outer_resolver: &Resolver,
        id: Option<&str>,
    ) -> Expr {
        // Extract the aggregate function and argument from the AST.
        // The AST is Aggregate(fn_expr, arg_expr) representing "fn over arg".
        let (fn_expr, arg_expr) = match &aggregate.kind {
            ExprKind::Aggregate(f, a) => (f.as_ref(), a.as_ref()),
            _ => panic!("Expected Aggregate expression"),
        };

        // Get the type of the aggregate result.
        let agg_type = outer_resolver
            .type_map()
            .get_type(aggregate.id.expect("Aggregate should have an id"))
            .expect("Aggregate expression should have a type");

        // Resolve the aggregate function in the outer context (group context).
        // This has access to group keys but not individual input rows.
        let fn_core = outer_resolver.resolve_expr(fn_expr);

        // Resolve the argument in the input context (row context).
        // This has access to the original input row bindings.
        let arg_core = self.input_resolver.resolve_expr(arg_expr);

        // Create the Core.Aggregate expression.
        let core_aggregate = Expr::Aggregate(
            agg_type.clone(),
            Box::new(fn_core),
            Box::new(arg_core),
        );

        // Generate a unique name for this aggregate binding.
        let implicit_label = fn_expr.implicit_label_opt();
        let base_name = id.or(implicit_label.as_deref()).unwrap_or("aggregate");
        let name = self.generate_name(base_name);

        // Add to used names set.
        self.used_names.insert(name.clone());

        // Add the aggregate binding to our list.
        self.aggregates
            .push((name.clone(), agg_type.clone(), core_aggregate));

        // Return an Id reference to the aggregate binding.
        Expr::Identifier(agg_type, name)
    }

    fn to_core_elements(
        &mut self,
        elements: &ast::Expr,
        outer_resolver: &Resolver,
    ) -> Expr {
        // The `elements` keyword refers to the list of rows in the current
        // group. It's implemented as an Aggregate with the identity function
        // applied to the current collection.

        // Get the type of elements (should be a list type).
        let _elem_type = outer_resolver
            .type_map()
            .get_type(elements.id.expect("Elements should have an id"))
            .expect("Elements expression should have a type");

        // TODO: Implement elements properly.
        // This requires:
        // 1. Creating an identity function (fn x => x) from the BuiltIn
        //    library.
        // 2. Getting the "current" expression from input_resolver.
        // 3. Creating Core.Aggregate(elem_type, fn_id, current).
        // 4. Generating a binding and returning an Id reference.
        //
        // For now, return a placeholder that will be implemented when we
        // integrate with the Resolver and have access to BuiltIn functions.
        todo!("to_core_elements: need BuiltIn::FN_ID and inputResolver.current")
    }

    fn bindings(&self) -> Vec<Binding> {
        self.aggregates
            .iter()
            .map(|(name, type_, _)| Binding {
                id: Id {
                    name: name.clone(),
                    ordinal: 0,
                },
                type_: type_.clone(),
            })
            .collect()
    }
}
