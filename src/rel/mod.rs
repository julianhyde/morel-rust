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

//! Relational algebra module.
//!
//! Provides a [`Rel`] enum of logical relational operators and a
//! [`builder::RelBuilder`] for constructing query plans, modelled on
//! Apache Calcite's `RelNode` and `RelBuilder`.

// lint: sort until '^$' erase 'pub '
pub mod builder;
pub mod display;
pub mod schema;

use crate::compile::core::Expr;
use crate::compile::types::{Label, PrimitiveType, Type};
use std::collections::BTreeMap;

// -----------------------------------------------------------------------
// Supporting types
// -----------------------------------------------------------------------

/// Direction of ordering for a sort key.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Direction {
    Ascending,
    Descending,
}

/// Null ordering relative to non-null values.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum NullDirection {
    First,
    Last,
    Unspecified,
}

/// One key in an ORDER BY clause, comprising a field ordinal, sort
/// direction, and null ordering.
#[derive(Clone, Debug)]
pub struct FieldCollation {
    /// Zero-based ordinal into the input row type.
    pub index: usize,
    pub direction: Direction,
    pub null_direction: NullDirection,
}

/// Aggregate function.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum AggFunction {
    // lint: sort until '^$' erase 'pub '
    Avg,
    Count,
    CountStar,
    Max,
    Min,
    Sum,
}

/// A call to an aggregate function within [`Rel::Aggregate`].
///
/// Arguments are ordinals into the input row type.
#[derive(Clone, Debug)]
pub struct AggCall {
    pub agg: AggFunction,
    /// Zero-based ordinals of input columns consumed by the aggregate.
    pub args: Vec<usize>,
    pub distinct: bool,
    /// Optional FILTER (WHERE …) clause.
    pub filter: Option<Expr>,
    /// Output column name.
    pub name: Option<String>,
    pub return_type: Type,
}

/// Join variant.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum JoinType {
    // lint: sort until '^$' erase 'pub '
    Anti,
    Full,
    Inner,
    Left,
    Right,
    Semi,
}

// -----------------------------------------------------------------------
// Rel
// -----------------------------------------------------------------------

/// A logical relational expression (query plan node).
///
/// Scalar expressions inside `Rel` nodes use [`crate::compile::core::Expr`].
/// Row types are ordered `Vec<(String, Type)>` so that field ordinals are
/// well-defined; use [`Rel::row_type`] to access them and
/// [`Rel::type_`] to obtain the corresponding Morel [`Type`].
#[derive(Clone, Debug)]
pub enum Rel {
    /// Inline constant rows.
    Values {
        /// Ordered columns `(name, type)`.
        row_type: Vec<(String, Type)>,
        /// Each inner `Vec` is one row of literal [`Expr`] values.
        rows: Vec<Vec<Expr>>,
    },

    /// Full scan of a named table from a schema.
    TableScan {
        /// Qualified table name, e.g. `["scott", "EMP"]`.
        table_name: Vec<String>,
        row_type: Vec<(String, Type)>,
    },

    /// Filter: select rows where `condition` is true.
    Filter {
        input: Box<Rel>,
        /// Boolean-typed scalar expression.
        condition: Expr,
    },

    /// Project: compute a new row from `exprs` over the input.
    Project {
        input: Box<Rel>,
        exprs: Vec<Expr>,
        row_type: Vec<(String, Type)>,
    },

    /// Sort (and optionally limit) the input.
    ///
    /// When `collation` is empty and only `offset`/`fetch` are set, this
    /// node acts as a pure LIMIT/OFFSET.
    Sort {
        input: Box<Rel>,
        collation: Vec<FieldCollation>,
        offset: Option<usize>,
        /// `None` means no row limit.
        fetch: Option<usize>,
    },

    /// Group by `group_set` fields and apply `agg_calls`.
    Aggregate {
        input: Box<Rel>,
        /// Zero-based ordinals of grouping columns.
        group_set: Vec<usize>,
        /// For CUBE / ROLLUP / GROUPING SETS; `[group_set]` for plain
        /// GROUP BY.
        group_sets: Vec<Vec<usize>>,
        agg_calls: Vec<AggCall>,
        row_type: Vec<(String, Type)>,
    },

    /// Join two inputs.
    Join {
        left: Box<Rel>,
        right: Box<Rel>,
        join_type: JoinType,
        condition: Expr,
        row_type: Vec<(String, Type)>,
    },

    /// UNION [ALL].
    Union {
        inputs: Vec<Rel>,
        all: bool,
        row_type: Vec<(String, Type)>,
    },

    /// INTERSECT [ALL].
    Intersect {
        inputs: Vec<Rel>,
        all: bool,
        row_type: Vec<(String, Type)>,
    },

    /// EXCEPT / MINUS [ALL].
    Minus {
        inputs: Vec<Rel>,
        all: bool,
        row_type: Vec<(String, Type)>,
    },
}

impl Rel {
    /// Returns the output row type as an ordered slice of `(name, type)`.
    pub fn row_type(&self) -> &[(String, Type)] {
        match self {
            // lint: sort until '^$' where '##Rel::'
            Rel::Aggregate { row_type, .. } => row_type,
            Rel::Filter { input, .. } => input.row_type(),
            Rel::Intersect { row_type, .. } => row_type,
            Rel::Join { row_type, .. } => row_type,
            Rel::Minus { row_type, .. } => row_type,
            Rel::Project { row_type, .. } => row_type,
            Rel::Sort { input, .. } => input.row_type(),
            Rel::TableScan { row_type, .. } => row_type,
            Rel::Union { row_type, .. } => row_type,
            Rel::Values { row_type, .. } => row_type,
        }
    }

    /// Returns the direct inputs of this node.
    pub fn inputs(&self) -> Vec<&Rel> {
        match self {
            // lint: sort until '^$' where '##Rel::'
            Rel::Aggregate { input, .. } => vec![input],
            Rel::Filter { input, .. } => vec![input],
            Rel::Intersect { inputs, .. } => {
                inputs.iter().collect()
            }
            Rel::Join { left, right, .. } => vec![left, right],
            Rel::Minus { inputs, .. } => inputs.iter().collect(),
            Rel::Project { input, .. } => vec![input],
            Rel::Sort { input, .. } => vec![input],
            Rel::TableScan { .. } => vec![],
            Rel::Union { inputs, .. } => inputs.iter().collect(),
            Rel::Values { .. } => vec![],
        }
    }

    /// Returns the Morel type of this relation:
    /// `Type::Bag(Box<Type::Record(…)>)`.
    pub fn type_(&self) -> Type {
        Type::Bag(Box::new(columns_to_record_type(self.row_type())))
    }
}

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

/// Converts an ordered column list to [`Type::Record`].
pub(crate) fn columns_to_record_type(
    columns: &[(String, Type)],
) -> Type {
    let fields = columns
        .iter()
        .map(|(name, t)| (Label::String(name.clone()), t.clone()))
        .collect::<BTreeMap<_, _>>();
    Type::Record(false, fields)
}

/// Returns `Type::Primitive(PrimitiveType::Bool)`.
pub fn bool_type() -> Type {
    Type::Primitive(PrimitiveType::Bool)
}

/// Returns `Type::Primitive(PrimitiveType::Int)`.
pub fn int_type() -> Type {
    Type::Primitive(PrimitiveType::Int)
}

/// Returns `Type::Primitive(PrimitiveType::String)`.
pub fn string_type() -> Type {
    Type::Primitive(PrimitiveType::String)
}
