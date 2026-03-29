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

//! Fluent builder for [`Rel`] query plan trees, modelled on Calcite's
//! `RelBuilder`.
//!
//! # Example
//!
//! ```
//! use morel::rel::builder::RelBuilder;
//! use morel::rel::schema::scott_schema;
//! use std::sync::Arc;
//!
//! let schema = Arc::new(scott_schema());
//! let mut b = RelBuilder::new(schema);
//! b.scan(&["scott", "EMP"]);
//! let cond = b.gt(b.field("SAL").unwrap(), b.literal_int(1000));
//! b.filter(cond);
//! let plan = b.build().unwrap();
//! ```

use crate::compile::core::Expr;
use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::code::Span;
use crate::eval::val::Val;
use crate::rel::schema::Schema;
use crate::rel::{
    AggCall, AggFunction, Direction, FieldCollation, JoinType, NullDirection,
    Rel, bool_type, columns_to_record_type, int_type, string_type,
};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::Arc;

// -----------------------------------------------------------------------
// RelError
// -----------------------------------------------------------------------

/// Errors produced by [`RelBuilder`] operations.
#[derive(Debug)]
pub enum RelError {
    // lint: sort until '#}' where '##[A-Z]'
    /// A field name was not found in the current row type.
    FieldNotFound(String),
    /// A field was accessed on an expression that is not of record type.
    FieldOnNonRecord(String),
    /// A field ordinal was out of range.
    FieldOrdinalOutOfRange { ordinal: usize, len: usize },
    /// A grouping set references a column not in the group key.
    GroupingSetNotSubset(String),
    /// A `GROUPING` or `GROUPING_ID` aggregate call had a FILTER clause,
    /// which is not supported.
    GroupingWithFilter,
    /// A group key expression did not resolve to an input column.
    InvalidGroupKey(String),
    /// `values()` was called with no field names but non-empty rows.
    NoFieldNames,
    /// A filter condition did not have boolean type.
    NonBooleanCondition(String),
    /// A row passed to `values()` has a different length from `names`.
    RowLengthMismatch {
        row: usize,
        expected: usize,
        got: usize,
    },
    /// Set-operation inputs have different column counts.
    SetOpColumnMismatch { expected: usize, got: usize },
    /// A table name was not found in the schema.
    TableNotFound(Vec<String>),
    /// An operator was applied to operands of incompatible types.
    TypeMismatch {
        op: String,
        left: String,
        right: String,
    },
    /// A correlation variable was referenced or used but never declared.
    UndeclaredCorrelationId(String),
    /// Right and Full correlate join types are not supported.
    UnsupportedCorrelateJoinType(String),
}

impl fmt::Display for RelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // lint: sort until '#}' where '##[A-Z]'
            RelError::FieldNotFound(name) => {
                write!(f, "field '{}' not found", name)
            }
            RelError::FieldOnNonRecord(got) => {
                write!(f, "field access on non-record type: {}", got)
            }
            RelError::FieldOrdinalOutOfRange { ordinal, len } => {
                write!(
                    f,
                    "field ordinal {} out of range (row has {} columns)",
                    ordinal, len
                )
            }
            RelError::GroupingSetNotSubset(name) => {
                write!(f, "grouping set column '{}' not in group key", name)
            }
            RelError::GroupingWithFilter => {
                write!(f, "GROUPING / GROUPING_ID does not support FILTER")
            }
            RelError::InvalidGroupKey(expr) => {
                write!(f, "group key expression not in input: {}", expr)
            }
            RelError::NoFieldNames => {
                write!(f, "values() called with no field names")
            }
            RelError::NonBooleanCondition(got) => {
                write!(f, "filter condition must be boolean, got {}", got)
            }
            RelError::RowLengthMismatch { row, expected, got } => write!(
                f,
                "row {} has {} values but {} field names were given",
                row, got, expected
            ),
            RelError::SetOpColumnMismatch { expected, got } => write!(
                f,
                "set-op inputs have different column counts: \
                 expected {}, got {}",
                expected, got
            ),
            RelError::TableNotFound(name) => {
                write!(f, "table not found: {:?}", name)
            }
            RelError::TypeMismatch { op, left, right } => {
                write!(
                    f,
                    "operator '{}' requires numeric operands, \
                     got '{}' and '{}'",
                    op, left, right
                )
            }
            RelError::UndeclaredCorrelationId(id) => {
                write!(f, "correlation variable '{}' was not declared", id)
            }
            RelError::UnsupportedCorrelateJoinType(jt) => {
                write!(f, "correlate does not support join type {}", jt)
            }
        }
    }
}

impl std::error::Error for RelError {}

// -----------------------------------------------------------------------
// SortKey
// -----------------------------------------------------------------------

/// A sort key: an expression plus direction and null ordering.
///
/// Constructed by [`RelBuilder::desc`], [`RelBuilder::nulls_first`], and
/// [`RelBuilder::nulls_last`]; consumed by [`RelBuilder::sort`] and
/// [`RelBuilder::sort_limit`].
#[derive(Clone, Debug)]
pub struct SortKey {
    /// The expression to sort by (must be a field reference).
    pub expr: Expr,
    pub direction: Direction,
    pub null_direction: NullDirection,
}

// -----------------------------------------------------------------------
// GroupKey
// -----------------------------------------------------------------------

/// Specifies the GROUP BY columns for [`RelBuilder::aggregate`].
///
/// Constructed by [`RelBuilder::group_key`] or
/// [`RelBuilder::grouping_sets`].
#[derive(Clone, Debug)]
pub struct GroupKey {
    /// Ordered list of grouping expressions (field references).
    pub exprs: Vec<Expr>,
    /// Optional explicit grouping sets.  When `None`, the single group
    /// set `[exprs]` is used.  When `Some`, each inner `Vec` is one
    /// grouping set; the union of all sets must be a subset of `exprs`.
    pub group_sets: Option<Vec<Vec<Expr>>>,
}

// -----------------------------------------------------------------------
// AggCallDef
// -----------------------------------------------------------------------

/// A pending aggregate-function call, built by `count_star`, `sum`, etc.
///
/// Use `.alias(name)`, `.distinct()`, and `.within_distinct(col)` to
/// customise before passing to [`RelBuilder::aggregate`].
#[derive(Clone, Debug)]
pub struct AggCallDef {
    pub agg: AggFunction,
    /// Input column names (one per argument to the function).
    pub arg_names: Vec<String>,
    /// Optional scalar expression arguments.  When `Some`, these
    /// override `arg_names`; the builder inserts a `Project` to
    /// materialise any non-field-reference expressions.
    pub arg_exprs: Option<Vec<Expr>>,
    pub distinct: bool,
    pub name: Option<String>,
    pub filter: Option<Expr>,
    /// Column names for `WITHIN DISTINCT (…)`; empty means none.
    pub within_distinct_names: Vec<String>,
}

impl AggCallDef {
    /// Sets the output column name.
    ///
    /// Corresponds to [`as`] in Calcite's Java `RelBuilder.AggCall`.
    ///
    /// [`as`]: https://calcite.apache.org/javadocAggregate/org/apache/calcite/tools/RelBuilder.AggCall.html#as(java.lang.String)
    pub fn alias(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }

    /// Makes the aggregate call DISTINCT.
    pub fn distinct(mut self) -> Self {
        self.distinct = true;
        self
    }

    /// Attaches a FILTER clause to the aggregate call.
    pub fn with_filter(mut self, filter: Expr) -> Self {
        self.filter = Some(filter);
        self
    }

    /// Attaches a `WITHIN DISTINCT (col)` clause to the aggregate call.
    pub fn within_distinct(mut self, col: impl Into<String>) -> Self {
        self.within_distinct_names.push(col.into());
        self
    }
}

// -----------------------------------------------------------------------
// BuilderConfig
// -----------------------------------------------------------------------

/// Controls optional simplifications applied by [`RelBuilder`].
///
/// All flags default to `true` (simplifications on), matching Calcite's
/// default `RelBuilder.Config`.
#[derive(Clone, Debug)]
pub struct BuilderConfig {
    /// Simplify `Filter(true, input)` → `input`.
    pub simplify_filter_true: bool,
    /// Simplify `Filter(false, input)` → `Values([], row_type)`.
    pub simplify_filter_false: bool,
    /// Simplify `Project(identity, input)` → `input`.
    pub simplify_project_identity: bool,
    /// Merge consecutive `Project` nodes into one.
    pub simplify_project_merge: bool,
    /// Merge `limit()` applied over a `Sort` into a single `Sort` node.
    pub simplify_sort_limit_merge: bool,
    /// Eliminate `distinct()` applied directly to an `Aggregate` node
    /// (aggregate already produces distinct rows per group key).
    pub simplify_aggregate_distinct: bool,
    /// Insert a pruning `Project` before `Aggregate` to drop input columns
    /// not referenced by the group key or any aggregate-call argument.
    pub simplify_aggregate_project_prune: bool,
}

impl Default for BuilderConfig {
    fn default() -> Self {
        BuilderConfig {
            simplify_filter_true: true,
            simplify_filter_false: true,
            simplify_project_identity: true,
            simplify_project_merge: true,
            simplify_sort_limit_merge: true,
            simplify_aggregate_distinct: true,
            simplify_aggregate_project_prune: false,
        }
    }
}

// -----------------------------------------------------------------------
// Frame (stack entry)
// -----------------------------------------------------------------------

/// One entry on the [`RelBuilder`] stack.
struct Frame {
    /// The relational node.
    rel: Rel,
    /// Optional table alias assigned by [`RelBuilder::alias`].
    alias: Option<String>,
}

// -----------------------------------------------------------------------
// RelBuilder
// -----------------------------------------------------------------------

/// Fluent builder for [`Rel`] query plan trees.
///
/// The builder maintains a stack of [`Rel`] nodes. Operator methods
/// (e.g. [`scan`], [`filter`], [`project`]) pop inputs from the stack
/// and push the result. Expression-building methods
/// (e.g. [`field`], [`literal_int`], [`gt`]) return [`Expr`] values
/// without touching the stack.
///
/// Call [`build`] to pop and return the top-of-stack node.
///
/// [`scan`]: RelBuilder::scan
/// [`filter`]: RelBuilder::filter
/// [`project`]: RelBuilder::project
/// [`build`]: RelBuilder::build
/// [`field`]: RelBuilder::field
/// [`literal_int`]: RelBuilder::literal_int
/// [`gt`]: RelBuilder::gt
pub struct RelBuilder {
    schema: Arc<dyn Schema>,
    config: BuilderConfig,
    stack: Vec<Frame>,
    /// Sticky error: the first error encountered. Once set, all subsequent
    /// builder methods short-circuit, and [`build`] returns `Err(…)`.
    ///
    /// [`build`]: RelBuilder::build
    error: Option<RelError>,
    /// Counter for generating unique correlation-variable names.
    next_cor_id: usize,
    /// Maps each declared correlation-variable name to its row type and
    /// the (sorted) ordinals of left columns referenced via [`cor_field`].
    ///
    /// [`cor_field`]: RelBuilder::cor_field
    #[allow(clippy::type_complexity)]
    declared_variables: HashMap<String, (Vec<(String, Type)>, Vec<usize>)>,
}

impl RelBuilder {
    /// Creates a new builder backed by the given schema.
    pub fn new(schema: Arc<dyn Schema>) -> Self {
        RelBuilder {
            schema,
            config: BuilderConfig::default(),
            stack: Vec::new(),
            error: None,
            next_cor_id: 0,
            declared_variables: HashMap::new(),
        }
    }

    /// Creates a new builder with a custom configuration.
    pub fn with_config(schema: Arc<dyn Schema>, config: BuilderConfig) -> Self {
        RelBuilder {
            schema,
            config,
            stack: Vec::new(),
            error: None,
            next_cor_id: 0,
            declared_variables: HashMap::new(),
        }
    }

    /// Records a sticky error (first error wins) and returns `self`.
    fn set_error(&mut self, e: RelError) -> &mut Self {
        if self.error.is_none() {
            self.error = Some(e);
        }
        self
    }

    // -------------------------------------------------------------------
    // Stack operations
    // -------------------------------------------------------------------

    /// Pushes an arbitrary [`Rel`] node onto the stack and returns
    /// `&mut self` for chaining.
    pub fn push(&mut self, rel: Rel) -> &mut Self {
        self.stack.push(Frame { rel, alias: None });
        self
    }

    /// Pops the top node from the stack and returns it, or returns the
    /// first error encountered during building.
    ///
    /// # Panics
    ///
    /// Panics if the stack is empty and there is no pending error.
    pub fn build(&mut self) -> Result<Rel, RelError> {
        if let Some(e) = self.error.take() {
            return Err(e);
        }
        Ok(self.stack.pop().expect("RelBuilder stack is empty").rel)
    }

    /// Pops `n` frames from the stack and returns them in bottom-to-top
    /// order (i.e. the first element was the bottommost of the n frames).
    ///
    /// # Panics
    ///
    /// Panics if the stack has fewer than `n` frames.
    fn pop_n(&mut self, n: usize, caller: &str) -> Vec<Rel> {
        assert!(
            self.stack.len() >= n,
            "{}: need {} frames, have {}",
            caller,
            n,
            self.stack.len()
        );
        let drain_from = self.stack.len() - n;
        self.stack.drain(drain_from..).map(|f| f.rel).collect()
    }

    /// Returns a reference to the top-of-stack node's row type.
    ///
    /// # Panics
    ///
    /// Panics if the stack is empty.
    fn peek_row_type(&self) -> &[(String, Type)] {
        self.stack
            .last()
            .expect("RelBuilder stack is empty")
            .rel
            .row_type()
    }

    // -------------------------------------------------------------------
    // Relational operators
    // -------------------------------------------------------------------

    /// Pushes a table scan for the named table.
    ///
    /// `name` is a slice of name parts, e.g. `&["scott", "EMP"]`.
    ///
    /// # Panics
    ///
    /// Panics if the table is not found in the schema.
    pub fn scan(&mut self, name: &[&str]) -> &mut Self {
        if self.error.is_some() {
            return self;
        }
        let name_vec: Vec<String> =
            name.iter().map(ToString::to_string).collect();
        match self.schema.table(name) {
            None => self.set_error(RelError::TableNotFound(name_vec)),
            Some(entry) => {
                // Auto-set alias to the last name part (e.g. "EMP").
                let auto_alias = entry.name.last().cloned();
                let rel = Rel::TableScan {
                    table_name: entry.name.clone(),
                    row_type: entry.columns.clone(),
                };
                self.push(rel);
                if let Some(a) = auto_alias {
                    self.stack.last_mut().unwrap().alias = Some(a);
                }
                self
            }
        }
    }

    /// Pushes a zero-row `Values` node with the given row type.
    pub fn empty(&mut self, row_type: Vec<(String, Type)>) -> &mut Self {
        let rel = Rel::Values {
            row_type,
            rows: vec![],
        };
        self.push(rel)
    }

    /// Pushes a `Values` node with the given column names and rows.
    ///
    /// `names` is the ordered list of column names; `rows` is a list of
    /// rows, each a list of literal [`Val`] values.
    ///
    /// Returns [`RelError::NoFieldNames`] if `names` is empty but `rows`
    /// is non-empty. Returns [`RelError::RowLengthMismatch`] if any row
    /// has a different length from `names`.
    pub fn values(&mut self, names: &[&str], rows: Vec<Vec<Val>>) -> &mut Self {
        if self.error.is_some() {
            return self;
        }
        // Validate: non-empty rows require non-empty names.
        if names.is_empty() && !rows.is_empty() {
            return self.set_error(RelError::NoFieldNames);
        }
        // Validate: every row must have exactly names.len() values.
        for (i, row) in rows.iter().enumerate() {
            if row.len() != names.len() {
                return self.set_error(RelError::RowLengthMismatch {
                    row: i,
                    expected: names.len(),
                    got: row.len(),
                });
            }
        }
        // Infer column types from the first row. If there are no rows,
        // default every column to `string`.
        let col_types: Vec<Type> = if let Some(first) = rows.first() {
            first.iter().map(val_type).collect()
        } else {
            names.iter().map(|_| string_type()).collect()
        };
        let row_type: Vec<(String, Type)> = names
            .iter()
            .zip(col_types.iter())
            .map(|(n, t)| (n.to_string(), t.clone()))
            .collect();
        let expr_rows: Vec<Vec<Expr>> = rows
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .zip(col_types.iter())
                    .map(|(v, t)| Expr::Literal(Box::new(t.clone()), v))
                    .collect()
            })
            .collect();
        let rel = Rel::Values {
            row_type,
            rows: expr_rows,
        };
        self.push(rel)
    }

    /// Applies a filter to the top-of-stack node.
    ///
    /// If `simplify_filter_true` is set and `condition` is the literal
    /// `true`, the filter is elided. If `simplify_filter_false` is set
    /// and `condition` is the literal `false`, the input is replaced by
    /// an empty `Values` with the same row type.
    pub fn filter(&mut self, condition: Expr) -> &mut Self {
        if self.error.is_some() {
            return self;
        }
        // Validate that the condition has boolean type.
        if *condition.type_() != bool_type() {
            let got = format!("{:?}", condition.type_());
            return self.set_error(RelError::NonBooleanCondition(got));
        }
        if self.config.simplify_filter_true && is_true(&condition) {
            return self; // identity
        }
        if self.config.simplify_filter_false && is_false(&condition) {
            let row_type = self.peek_row_type().to_vec();
            // build() cannot fail here: error is None and stack is non-empty
            let input = self.build().expect("filter: empty stack");
            drop(input);
            return self.empty(row_type);
        }
        // Filter on empty input is always empty.
        if matches!(
            self.stack.last().map(|f| &f.rel),
            Some(Rel::Values { rows, .. }) if rows.is_empty()
        ) {
            return self;
        }
        let alias = self.stack.last().and_then(|f| f.alias.clone());
        let input = Box::new(self.build().expect("filter: empty stack"));
        self.push(Rel::Filter { input, condition });
        if let Some(a) = alias {
            self.stack.last_mut().unwrap().alias = Some(a);
        }
        self
    }

    /// Applies a projection to the top-of-stack node.
    ///
    /// `exprs` are the output expressions; each must carry its result
    /// type. Column names are derived from expression display or defaulted
    /// to `$N`.
    pub fn project(&mut self, exprs: Vec<Expr>) -> &mut Self {
        let input_row_type = self.peek_row_type().to_vec();
        // Build output row type: derive names from expressions.
        let row_type: Vec<(String, Type)> = exprs
            .iter()
            .enumerate()
            .map(|(i, e)| {
                let name = expr_name(e, &input_row_type)
                    .unwrap_or_else(|| format!("${}", i));
                (name, *e.type_())
            })
            .collect();
        // Identity-project elimination.
        if self.config.simplify_project_identity
            && is_identity_project(&exprs, &input_row_type)
        {
            return self;
        }
        // Save alias from the current top-of-stack before any pop.
        let alias = self.stack.last().and_then(|f| f.alias.clone());
        // Project-over-project merge: compose the two projections into one.
        if self.config.simplify_project_merge {
            let composed = match self.stack.last().map(|f| &f.rel) {
                Some(Rel::Project {
                    exprs: inner_exprs,
                    row_type: inner_row_type,
                    ..
                }) => try_compose_projects(&exprs, inner_exprs, inner_row_type),
                _ => None,
            };
            if let Some(composed_exprs) = composed {
                let inner_frame = self.stack.pop().unwrap();
                if let Rel::Project {
                    input: inner_input, ..
                } = inner_frame.rel
                {
                    self.push(Rel::Project {
                        input: inner_input,
                        exprs: composed_exprs,
                        row_type,
                    });
                    if let Some(a) = alias {
                        self.stack.last_mut().unwrap().alias = Some(a);
                    }
                    return self;
                }
            }
        }
        let input = Box::new(self.build().expect("project: empty stack"));
        self.push(Rel::Project {
            input,
            exprs,
            row_type,
        });
        if let Some(a) = alias {
            self.stack.last_mut().unwrap().alias = Some(a);
        }
        self
    }

    /// Applies a named projection to the top-of-stack node.
    ///
    /// Like [`project`] but the caller supplies explicit output column
    /// names. `names` must have the same length as `exprs`.
    ///
    /// [`project`]: RelBuilder::project
    pub fn project_named(
        &mut self,
        exprs: Vec<Expr>,
        names: Vec<String>,
    ) -> &mut Self {
        assert_eq!(
            exprs.len(),
            names.len(),
            "exprs and names must have the same length"
        );
        let input_row_type = self.peek_row_type().to_vec();
        let row_type: Vec<(String, Type)> = names
            .into_iter()
            .zip(exprs.iter())
            .map(|(name, e)| (name, *e.type_()))
            .collect();
        // Identity-project elimination.
        if self.config.simplify_project_identity
            && is_identity_project(&exprs, &input_row_type)
            && row_type == input_row_type
        {
            return self;
        }
        let alias = self.stack.last().and_then(|f| f.alias.clone());
        let input = Box::new(self.build().expect("project_named: empty stack"));
        self.push(Rel::Project {
            input,
            exprs,
            row_type,
        });
        if let Some(a) = alias {
            self.stack.last_mut().unwrap().alias = Some(a);
        }
        self
    }

    /// Projects all columns of the top-of-stack node **except** those at
    /// the given ordinals.
    ///
    /// Returns [`RelError::FieldOrdinalOutOfRange`] if any ordinal is out
    /// of range.
    pub fn project_except_ordinals(
        &mut self,
        exclude: &[usize],
    ) -> Result<&mut Self, RelError> {
        let row = self.peek_row_type().to_vec();
        let n = row.len();
        for &ord in exclude {
            if ord >= n {
                return Err(RelError::FieldOrdinalOutOfRange {
                    ordinal: ord,
                    len: n,
                });
            }
        }
        let exprs: Vec<Expr> = row
            .iter()
            .enumerate()
            .filter(|(i, _)| !exclude.contains(i))
            .map(|(_, (name, ty))| {
                Expr::Identifier(Box::new(ty.clone()), name.clone())
            })
            .collect();
        Ok(self.project(exprs))
    }

    /// Projects all columns of the top-of-stack node **except** those
    /// with the given names.
    ///
    /// Returns [`RelError::FieldNotFound`] if any name is absent.
    pub fn project_except_names(
        &mut self,
        exclude: &[&str],
    ) -> Result<&mut Self, RelError> {
        let row = self.peek_row_type().to_vec();
        for &name in exclude {
            if !row.iter().any(|(n, _)| n == name) {
                return Err(RelError::FieldNotFound(name.to_string()));
            }
        }
        let exprs: Vec<Expr> = row
            .iter()
            .filter(|(name, _)| !exclude.contains(&name.as_str()))
            .map(|(name, ty)| {
                Expr::Identifier(Box::new(ty.clone()), name.clone())
            })
            .collect();
        Ok(self.project(exprs))
    }

    // -------------------------------------------------------------------
    // Sort / limit
    // -------------------------------------------------------------------

    /// Sorts the top-of-stack node by the given keys.
    ///
    /// Duplicate sort keys (same ordinal + direction) are eliminated.
    /// If `keys` is empty, this is a no-op.
    pub fn sort(&mut self, keys: &[SortKey]) -> &mut Self {
        // sort() on empty input is already empty.
        if matches!(
            self.stack.last().map(|f| &f.rel),
            Some(Rel::Values { rows, .. }) if rows.is_empty()
        ) {
            return self;
        }
        let row_type = self.peek_row_type().to_vec();
        let collation = sort_keys_to_collation(keys, &row_type);
        if collation.is_empty() {
            return self;
        }
        let alias = self.stack.last().and_then(|f| f.alias.clone());
        let input = Box::new(self.build().expect("sort: empty stack"));
        // Sort-over-project-sort: if the input is Project(Sort(...)) and the
        // outer collation is satisfied by the inner sort (remapped through
        // the project), drop the inner sort node.
        let input = {
            let rel = *input;
            if let Rel::Project {
                input: proj_input,
                exprs,
                row_type: proj_rt,
            } = rel
            {
                let proj_rel = *proj_input;
                if let Rel::Sort {
                    input: inner_input,
                    collation: inner_coll,
                    offset: None,
                    fetch: None,
                } = proj_rel
                {
                    if can_subsume_inner_sort(
                        &collation,
                        &exprs,
                        &inner_coll,
                        inner_input.row_type(),
                    ) {
                        Box::new(Rel::Project {
                            input: inner_input,
                            exprs,
                            row_type: proj_rt,
                        })
                    } else {
                        Box::new(Rel::Project {
                            input: Box::new(Rel::Sort {
                                input: inner_input,
                                collation: inner_coll,
                                offset: None,
                                fetch: None,
                            }),
                            exprs,
                            row_type: proj_rt,
                        })
                    }
                } else {
                    Box::new(Rel::Project {
                        input: Box::new(proj_rel),
                        exprs,
                        row_type: proj_rt,
                    })
                }
            } else {
                Box::new(rel)
            }
        };
        self.push(Rel::Sort {
            input,
            collation,
            offset: None,
            fetch: None,
        });
        if let Some(a) = alias {
            self.stack.last_mut().unwrap().alias = Some(a);
        }
        self
    }

    /// Limits the top-of-stack node to at most `fetch` rows, optionally
    /// skipping the first `offset` rows.
    ///
    /// Implemented as `Rel::Sort` with an empty collation. If
    /// `simplify_sort_limit_merge` is set and the top-of-stack is already
    /// a `Sort` with no existing `offset` or `fetch`, the two nodes are
    /// merged into one.
    pub fn limit(
        &mut self,
        offset: Option<usize>,
        fetch: Option<usize>,
    ) -> &mut Self {
        let alias = self.stack.last().and_then(|f| f.alias.clone());
        // Sort-then-limit merge: absorb limit into an existing Sort.
        if self.config.simplify_sort_limit_merge {
            let can_merge = matches!(
                self.stack.last().map(|f| &f.rel),
                Some(Rel::Sort {
                    offset: None,
                    fetch: None,
                    ..
                })
            );
            if can_merge {
                let frame = self.stack.pop().unwrap();
                if let Rel::Sort {
                    input, collation, ..
                } = frame.rel
                {
                    self.push(Rel::Sort {
                        input,
                        collation,
                        offset,
                        fetch,
                    });
                    if let Some(a) = alias {
                        self.stack.last_mut().unwrap().alias = Some(a);
                    }
                    return self;
                }
            }
        }
        let input = Box::new(self.build().expect("limit: empty stack"));
        self.push(Rel::Sort {
            input,
            collation: vec![],
            offset,
            fetch,
        });
        if let Some(a) = alias {
            self.stack.last_mut().unwrap().alias = Some(a);
        }
        self
    }

    /// Sorts and optionally limits the top-of-stack node.
    ///
    /// If `fetch` is `Some(0)`, produces an empty `Values` (no rows can
    /// satisfy the limit) regardless of `keys` or `offset`.
    pub fn sort_limit(
        &mut self,
        offset: Option<usize>,
        fetch: Option<usize>,
        keys: &[SortKey],
    ) -> &mut Self {
        if fetch == Some(0) {
            let row_type = self.peek_row_type().to_vec();
            let _ = self.build(); // discard input
            return self.empty(row_type);
        }
        let row_type = self.peek_row_type().to_vec();
        let collation = sort_keys_to_collation(keys, &row_type);
        let input = Box::new(self.build().expect("sort_limit: empty stack"));
        self.push(Rel::Sort {
            input,
            collation,
            offset,
            fetch,
        })
    }

    /// Renames the output columns of the top-of-stack node.
    ///
    /// Equivalent to a `Project` that passes all columns through but
    /// changes their names. If `names` matches the existing column names,
    /// this is a no-op.
    pub fn rename(&mut self, names: Vec<String>) -> &mut Self {
        let input_row_type = self.peek_row_type().to_vec();
        assert_eq!(
            names.len(),
            input_row_type.len(),
            "rename: expected {} names, got {}",
            input_row_type.len(),
            names.len()
        );
        // Check if renaming would actually change anything.
        let unchanged = names
            .iter()
            .zip(input_row_type.iter())
            .all(|(new, (old, _))| new == old);
        if unchanged {
            return self;
        }
        let exprs: Vec<Expr> = input_row_type
            .iter()
            .map(|(name, ty)| {
                Expr::Identifier(Box::new(ty.clone()), name.clone())
            })
            .collect();
        let row_type: Vec<(String, Type)> = names
            .into_iter()
            .zip(input_row_type.iter())
            .map(|(name, (_, ty))| (name, ty.clone()))
            .collect();
        let alias = self.stack.last().and_then(|f| f.alias.clone());
        let input = Box::new(self.build().expect("rename: empty stack"));
        self.push(Rel::Project {
            input,
            exprs,
            row_type,
        });
        if let Some(a) = alias {
            self.stack.last_mut().unwrap().alias = Some(a);
        }
        self
    }

    // -------------------------------------------------------------------
    // Sort-key wrappers
    // -------------------------------------------------------------------

    /// Wraps `expr` as a descending sort key with default null ordering.
    pub fn desc(&self, expr: Expr) -> SortKey {
        SortKey {
            expr,
            direction: Direction::Descending,
            null_direction: NullDirection::Unspecified,
        }
    }

    /// Wraps `expr` as an ascending sort key with NULLS FIRST.
    pub fn nulls_first(&self, expr: Expr) -> SortKey {
        SortKey {
            expr,
            direction: Direction::Ascending,
            null_direction: NullDirection::First,
        }
    }

    /// Wraps `expr` as an ascending sort key with NULLS LAST.
    pub fn nulls_last(&self, expr: Expr) -> SortKey {
        SortKey {
            expr,
            direction: Direction::Ascending,
            null_direction: NullDirection::Last,
        }
    }

    // -------------------------------------------------------------------
    // Aggregate
    // -------------------------------------------------------------------

    /// Returns a `GroupKey` for `GROUP BY exprs`.
    ///
    /// Each expression must be a field reference to a column in the
    /// current top-of-stack row type.
    pub fn group_key(&self, exprs: Vec<Expr>) -> GroupKey {
        GroupKey {
            exprs,
            group_sets: None,
        }
    }

    /// Returns a `GroupKey` with explicit `GROUPING SETS`.
    ///
    /// `exprs` is the union of all columns used in any grouping set;
    /// `sets` lists each individual grouping set.  Each set is a
    /// sub-list of field-reference `Expr`s drawn from `exprs`.
    pub fn grouping_sets(
        &self,
        exprs: Vec<Expr>,
        sets: Vec<Vec<Expr>>,
    ) -> GroupKey {
        GroupKey {
            exprs,
            group_sets: Some(sets),
        }
    }

    /// Applies GROUP BY and aggregation to the top-of-stack node.
    ///
    /// `group_key` supplies the grouping columns. `agg_calls` supplies
    /// the aggregate functions. The output row type is: grouping columns
    /// first (in the order they appear in `group_key`), then aggregate
    /// results.
    pub fn aggregate(
        &mut self,
        group_key: &GroupKey,
        agg_calls: Vec<AggCallDef>,
    ) -> &mut Self {
        if self.error.is_some() {
            return self;
        }
        let mut input_row_type = self.peek_row_type().to_vec();
        // Materialise non-identifier group key expressions (e.g. literals)
        // and non-field-ref agg call arg_exprs by appending them as extra
        // columns ($f<n>) in a single pre-project node.
        let n_in = input_row_type.len();
        let mut extra: Vec<(String, Expr)> = Vec::new();
        // Resolve group key expressions:
        //  - Field refs that exist in input_row_type → kept as-is.
        //  - Field refs NOT in input_row_type → InvalidGroupKey error.
        //  - Non-identifiers (literals, etc.) → materialised into extra.
        let mut gk_exprs: Vec<Expr> = Vec::new();
        for e in &group_key.exprs {
            if let Expr::Identifier(_, name) = e {
                if input_row_type.iter().any(|(n, _)| n == name) {
                    gk_exprs.push(e.clone());
                } else {
                    return self
                        .set_error(RelError::InvalidGroupKey(name.clone()));
                }
            } else {
                // Non-identifier: materialise as a new column.
                let col = format!("$f{}", n_in + extra.len());
                let ty = *e.type_();
                extra.push((col.clone(), e.clone()));
                gk_exprs.push(Expr::Identifier(Box::new(ty), col));
            }
        }
        // Resolve agg call arg_exprs: field refs stay as arg_names; others
        // are appended to `extra`.
        let agg_calls: Vec<AggCallDef> = agg_calls
            .into_iter()
            .map(|mut def| {
                if let Some(exprs) = def.arg_exprs.take() {
                    let mut names: Vec<String> = Vec::new();
                    for expr in exprs {
                        if let Expr::Identifier(_, ref name) = expr
                            && input_row_type.iter().any(|(n, _)| n == name)
                        {
                            names.push(name.clone());
                            continue;
                        }
                        let col = format!("$f{}", n_in + extra.len());
                        extra.push((col.clone(), expr));
                        names.push(col);
                    }
                    def.arg_names = names;
                }
                def
            })
            .collect();
        if !extra.is_empty() {
            let orig = self.stack.pop().expect("RelBuilder stack is empty").rel;
            let mut proj_exprs: Vec<Expr> = input_row_type
                .iter()
                .map(|(name, ty)| {
                    Expr::Identifier(Box::new(ty.clone()), name.clone())
                })
                .collect();
            let mut proj_rt = input_row_type.clone();
            for (col, expr) in extra {
                let ty = *expr.type_();
                proj_exprs.push(expr);
                proj_rt.push((col, ty));
            }
            input_row_type = proj_rt.clone();
            self.stack.push(Frame {
                rel: Rel::Project {
                    input: Box::new(orig),
                    exprs: proj_exprs,
                    row_type: proj_rt,
                },
                alias: None,
            });
        }
        // Resolve grouping expressions to ordinals; error on any unresolved.
        let mut group_set: Vec<usize> = Vec::new();
        for e in &gk_exprs {
            if let Expr::Identifier(_, name) = e {
                if let Some(idx) =
                    input_row_type.iter().position(|(n, _)| n == name)
                {
                    group_set.push(idx);
                } else {
                    return self
                        .set_error(RelError::InvalidGroupKey(name.clone()));
                }
            } else {
                let msg = format!("{:?}", e);
                return self.set_error(RelError::InvalidGroupKey(msg));
            }
        }
        // Build output row type: grouping columns first.
        let mut row_type: Vec<(String, Type)> = group_set
            .iter()
            .map(|&i| input_row_type[i].clone())
            .collect();
        // Validate agg-call filter expressions.
        for def in &agg_calls {
            // GROUPING / GROUPING_ID cannot have a FILTER clause.
            if def.filter.is_some()
                && matches!(
                    def.agg,
                    AggFunction::Grouping | AggFunction::GroupingId
                )
            {
                return self.set_error(RelError::GroupingWithFilter);
            }
            if let Some(f) = &def.filter {
                if *f.type_() == bool_type() {
                    continue;
                }
                let got = format!("{:?}", f.type_());
                return self.set_error(RelError::NonBooleanCondition(got));
            }
        }
        // Resolve grouping sets (if any).
        let mut group_sets: Vec<Vec<usize>> = if let Some(sets) =
            group_key.group_sets.clone()
        {
            // Build a debug-string → resolved name map for materialised
            // non-identifier group key expressions.
            let gk_matl: HashMap<String, String> = group_key
                .exprs
                .iter()
                .zip(gk_exprs.iter())
                .filter_map(|(orig, mat)| {
                    if let Expr::Identifier(_, mat_name) = mat {
                        // Non-identifiers were materialised; skip pass-through
                        // field refs (where orig is already mat_name).
                        let same = matches!(
                            orig,
                            Expr::Identifier(_, n) if n == mat_name
                        );
                        if !same {
                            return Some((
                                format!("{:?}", orig),
                                mat_name.clone(),
                            ));
                        }
                    }
                    None
                })
                .collect();
            let mut resolved_sets: Vec<Vec<usize>> = Vec::new();
            for set in sets {
                let mut ordinals: Vec<usize> = Vec::new();
                for e in &set {
                    // Resolve: field-ref identifier, or materialized name.
                    let name = if let Expr::Identifier(_, n) = e {
                        n.clone()
                    } else {
                        let key = format!("{:?}", e);
                        match gk_matl.get(&key) {
                            Some(n) => n.clone(),
                            None => {
                                let msg = format!("{:?}", e);
                                return self
                                    .set_error(RelError::InvalidGroupKey(msg));
                            }
                        }
                    };
                    if let Some(idx) =
                        input_row_type.iter().position(|(n, _)| n == &name)
                    {
                        if !group_set.contains(&idx) {
                            return self.set_error(
                                RelError::GroupingSetNotSubset(name),
                            );
                        }
                        ordinals.push(idx);
                    } else {
                        return self.set_error(RelError::InvalidGroupKey(name));
                    }
                }
                resolved_sets.push(ordinals);
            }
            // Deduplicate grouping sets (preserve first occurrence).
            let mut seen: HashSet<Vec<usize>> = HashSet::new();
            resolved_sets.retain(|s| {
                let mut key = s.clone();
                key.sort_unstable();
                seen.insert(key)
            });
            resolved_sets
        } else {
            vec![group_set.clone()]
        };
        // Prune unused input columns before the aggregate.
        if self.config.simplify_aggregate_project_prune {
            // Collect all input ordinals used by the group key or any
            // aggregate call argument (including within-distinct).
            let mut needed: Vec<usize> = group_set.clone();
            for def in &agg_calls {
                for name in &def.arg_names {
                    if let Some(idx) =
                        input_row_type.iter().position(|(n, _)| n == name)
                    {
                        needed.push(idx);
                    }
                }
                for name in &def.within_distinct_names {
                    if let Some(idx) =
                        input_row_type.iter().position(|(n, _)| n == name)
                    {
                        needed.push(idx);
                    }
                }
            }
            needed.sort_unstable();
            needed.dedup();
            // Only insert the pruning Project when columns can be dropped.
            if needed.len() < input_row_type.len() {
                let orig =
                    self.stack.pop().expect("RelBuilder stack is empty").rel;
                let proj_exprs: Vec<Expr> = needed
                    .iter()
                    .map(|&i| {
                        let (name, ty) = &input_row_type[i];
                        Expr::Identifier(Box::new(ty.clone()), name.clone())
                    })
                    .collect();
                let proj_rt: Vec<(String, Type)> =
                    needed.iter().map(|&i| input_row_type[i].clone()).collect();
                self.stack.push(Frame {
                    rel: Rel::Project {
                        input: Box::new(orig),
                        exprs: proj_exprs,
                        row_type: proj_rt.clone(),
                    },
                    alias: None,
                });
                // Remap group_set and group_sets to new column positions.
                group_set = group_set
                    .iter()
                    .map(|&o| needed.iter().position(|&x| x == o).unwrap())
                    .collect();
                group_sets = group_sets
                    .iter()
                    .map(|set| {
                        set.iter()
                            .map(|&o| {
                                needed.iter().position(|&x| x == o).unwrap()
                            })
                            .collect()
                    })
                    .collect();
                input_row_type = proj_rt;
                // Merge the pruning Project with an underlying
                // materialisation Project (Project-over-project compose).
                if self.config.simplify_project_merge {
                    let frame = self.stack.pop().unwrap();
                    if let Rel::Project {
                        input: prun_input,
                        exprs: prun_exprs,
                        row_type: prun_rt,
                    } = frame.rel
                    {
                        if let Rel::Project {
                            input: inner_input,
                            exprs: inner_exprs,
                            row_type: inner_rt,
                        } = *prun_input
                        {
                            if let Some(composed) = try_compose_projects(
                                &prun_exprs,
                                &inner_exprs,
                                &inner_rt,
                            ) {
                                self.stack.push(Frame {
                                    rel: Rel::Project {
                                        input: inner_input,
                                        exprs: composed,
                                        row_type: prun_rt,
                                    },
                                    alias: None,
                                });
                            } else {
                                // Cannot compose; restore nested projects.
                                let inner = Box::new(Rel::Project {
                                    input: inner_input,
                                    exprs: inner_exprs,
                                    row_type: inner_rt,
                                });
                                self.stack.push(Frame {
                                    rel: Rel::Project {
                                        input: inner,
                                        exprs: prun_exprs,
                                        row_type: prun_rt,
                                    },
                                    alias: None,
                                });
                            }
                        } else {
                            self.stack.push(Frame {
                                rel: Rel::Project {
                                    input: prun_input,
                                    exprs: prun_exprs,
                                    row_type: prun_rt,
                                },
                                alias: None,
                            });
                        }
                    } else {
                        self.stack.push(frame);
                    }
                }
            }
        }
        // Resolve agg calls; collect names for later dedup project.
        let n_group = group_set.len();
        let mut all_names: Vec<String> = Vec::new();
        let resolved: Vec<AggCall> = agg_calls
            .into_iter()
            .enumerate()
            .map(|(i, def)| {
                let args: Vec<usize> = def
                    .arg_names
                    .iter()
                    .filter_map(|name| {
                        input_row_type.iter().position(|(n, _)| n == name)
                    })
                    .collect();
                let within_distinct: Vec<usize> = def
                    .within_distinct_names
                    .iter()
                    .filter_map(|name| {
                        input_row_type.iter().position(|(n, _)| n == name)
                    })
                    .collect();
                let return_type =
                    agg_return_type(def.agg, &args, &input_row_type);
                let name =
                    def.name.unwrap_or_else(|| format!("${}", n_group + i));
                all_names.push(name.clone());
                row_type.push((name.clone(), return_type.clone()));
                AggCall {
                    agg: def.agg,
                    args,
                    distinct: def.distinct,
                    filter: def.filter,
                    name: Some(name),
                    return_type,
                    within_distinct,
                }
            })
            .collect();
        // Deduplicate identical agg calls: only emit one computation per
        // unique (agg, args, distinct, filter) tuple, then add a project
        // to expose the original names.
        let mut unique_calls: Vec<AggCall> = Vec::new();
        let mut dedup_keys: Vec<String> = Vec::new();
        let mut dedup_map: Vec<usize> = Vec::new();
        for call in &resolved {
            let key = agg_call_key(call);
            let idx =
                if let Some(pos) = dedup_keys.iter().position(|k| k == &key) {
                    pos
                } else {
                    let pos = unique_calls.len();
                    unique_calls.push(call.clone());
                    dedup_keys.push(key);
                    pos
                };
            dedup_map.push(idx);
        }
        let has_duplicates = unique_calls.len() < resolved.len();
        // Build unique row_type for the Aggregate node.
        let agg_row_type: Vec<(String, Type)> = if has_duplicates {
            let mut rt: Vec<(String, Type)> = group_set
                .iter()
                .map(|&i| input_row_type[i].clone())
                .collect();
            for c in &unique_calls {
                rt.push((
                    c.name.clone().unwrap_or_default(),
                    c.return_type.clone(),
                ));
            }
            rt
        } else {
            row_type.clone()
        };
        let alias = self.stack.last().and_then(|f| f.alias.clone());
        let input = Box::new(self.build().expect("aggregate: empty stack"));
        self.push(Rel::Aggregate {
            input,
            group_set: group_set.clone(),
            group_sets,
            agg_calls: unique_calls,
            row_type: agg_row_type.clone(),
        });
        if let Some(ref a) = alias {
            self.stack.last_mut().unwrap().alias = Some(a.clone());
        }
        // If duplicates were removed, add a project to re-expose the
        // original names (including duplicated columns).
        if has_duplicates {
            let project_exprs: Vec<Expr> = agg_row_type[..n_group]
                .iter()
                .map(|(name, ty)| {
                    Expr::Identifier(Box::new(ty.clone()), name.clone())
                })
                .chain(dedup_map.iter().enumerate().map(|(orig_i, &uniq_i)| {
                    let (ref name, ref ty) = agg_row_type[n_group + uniq_i];
                    let _ = &all_names[orig_i]; // original name
                    Expr::Identifier(Box::new(ty.clone()), name.clone())
                }))
                .collect();
            let project_names: Vec<String> = agg_row_type[..n_group]
                .iter()
                .map(|(name, _)| name.clone())
                .chain(all_names)
                .collect();
            self.project_named(project_exprs, project_names);
            if let Some(a) = alias {
                self.stack.last_mut().unwrap().alias = Some(a);
            }
        }
        self
    }

    /// Deduplicates the top-of-stack node (equivalent to
    /// `GROUP BY` all columns with no aggregates).
    ///
    /// If `simplify_aggregate_distinct` is set and the top-of-stack node
    /// is already a `Rel::Aggregate`, the `distinct()` is a no-op because
    /// every aggregate already produces at most one row per group key.
    pub fn distinct(&mut self) -> &mut Self {
        if self.config.simplify_aggregate_distinct
            && matches!(
                self.stack.last().map(|f| &f.rel),
                Some(Rel::Aggregate { .. })
            )
        {
            return self;
        }
        // distinct() on empty input is already empty.
        if matches!(
            self.stack.last().map(|f| &f.rel),
            Some(Rel::Values { rows, .. }) if rows.is_empty()
        ) {
            return self;
        }
        let row_type = self.peek_row_type().to_vec();
        let all_exprs: Vec<Expr> = row_type
            .iter()
            .map(|(name, ty)| {
                Expr::Identifier(Box::new(ty.clone()), name.clone())
            })
            .collect();
        let gk = GroupKey {
            exprs: all_exprs,
            group_sets: None,
        };
        self.aggregate(&gk, vec![])
    }

    // --- agg-call constructors ------------------------------------------

    /// Returns a `COUNT(*)` aggregate call definition.
    pub fn count_star(&self) -> AggCallDef {
        AggCallDef {
            agg: AggFunction::CountStar,
            arg_names: vec![],
            arg_exprs: None,
            distinct: false,
            name: None,
            filter: None,
            within_distinct_names: vec![],
        }
    }

    /// Returns a `COUNT(col)` aggregate call definition.
    pub fn count(&self, col: &str) -> AggCallDef {
        AggCallDef {
            agg: AggFunction::Count,
            arg_names: vec![col.to_string()],
            arg_exprs: None,
            distinct: false,
            name: None,
            filter: None,
            within_distinct_names: vec![],
        }
    }

    /// Returns a `SUM(col)` aggregate call definition.
    pub fn sum(&self, col: &str) -> AggCallDef {
        AggCallDef {
            agg: AggFunction::Sum,
            arg_names: vec![col.to_string()],
            arg_exprs: None,
            distinct: false,
            name: None,
            filter: None,
            within_distinct_names: vec![],
        }
    }

    /// Returns a `SUM(expr)` aggregate call definition where `expr` may
    /// be any scalar expression.
    pub fn sum_expr(&self, expr: Expr) -> AggCallDef {
        AggCallDef {
            agg: AggFunction::Sum,
            arg_names: vec![],
            arg_exprs: Some(vec![expr]),
            distinct: false,
            name: None,
            filter: None,
            within_distinct_names: vec![],
        }
    }

    /// Returns a `MIN(col)` aggregate call definition.
    pub fn min(&self, col: &str) -> AggCallDef {
        AggCallDef {
            agg: AggFunction::Min,
            arg_names: vec![col.to_string()],
            arg_exprs: None,
            distinct: false,
            name: None,
            filter: None,
            within_distinct_names: vec![],
        }
    }

    /// Returns a `MAX(col)` aggregate call definition.
    pub fn max(&self, col: &str) -> AggCallDef {
        AggCallDef {
            agg: AggFunction::Max,
            arg_names: vec![col.to_string()],
            arg_exprs: None,
            distinct: false,
            name: None,
            filter: None,
            within_distinct_names: vec![],
        }
    }

    /// Returns an `AVG(col)` aggregate call definition.
    pub fn avg(&self, col: &str) -> AggCallDef {
        AggCallDef {
            agg: AggFunction::Avg,
            arg_names: vec![col.to_string()],
            arg_exprs: None,
            distinct: false,
            name: None,
            filter: None,
            within_distinct_names: vec![],
        }
    }

    /// Returns a `GROUPING_ID(col, …)` aggregate call definition.
    ///
    /// `cols` are the column names from the group key; the call returns
    /// an integer that identifies which grouping set applies to each row.
    pub fn grouping_id(&self, cols: Vec<&str>) -> AggCallDef {
        AggCallDef {
            agg: AggFunction::GroupingId,
            arg_names: cols.into_iter().map(str::to_string).collect(),
            arg_exprs: None,
            distinct: false,
            name: None,
            filter: None,
            within_distinct_names: vec![],
        }
    }

    /// Returns a `GROUPING(col)` aggregate call definition.
    ///
    /// Returns 1 when the column is not part of the current grouping
    /// set, 0 otherwise.
    pub fn grouping(&self, col: &str) -> AggCallDef {
        AggCallDef {
            agg: AggFunction::Grouping,
            arg_names: vec![col.to_string()],
            arg_exprs: None,
            distinct: false,
            name: None,
            filter: None,
            within_distinct_names: vec![],
        }
    }

    // -------------------------------------------------------------------
    // Join and alias
    // -------------------------------------------------------------------

    /// Sets an alias on the top-of-stack frame.
    ///
    /// The alias can later be used with [`field2`] to disambiguate
    /// columns when two aliased frames are on the stack.
    ///
    /// Corresponds to [`as`] in Calcite's Java `RelBuilder`.
    /// Note: this is unrelated to Java's
    /// [`alias(RexNode, String)`][calcite-alias], which names an
    /// expression within a `project` call.
    ///
    /// [`as`]: https://calcite.apache.org/javadocAggregate/org/apache/calcite/tools/RelBuilder.html#as(java.lang.String)
    /// [calcite-alias]: https://calcite.apache.org/javadocAggregate/org/apache/calcite/tools/RelBuilder.html#alias(org.apache.calcite.rex.RexNode,java.lang.String)
    /// [`field2`]: RelBuilder::field2
    pub fn alias(&mut self, alias: impl Into<String>) -> &mut Self {
        self.stack
            .last_mut()
            .expect("RelBuilder stack is empty")
            .alias = Some(alias.into());
        self
    }

    /// Joins the top two frames with the given join type and condition.
    ///
    /// Pops the top two frames (right = top, left = second), concatenates
    /// their row types, and pushes a `Rel::Join`.
    pub fn join(&mut self, join_type: JoinType, condition: Expr) -> &mut Self {
        let right_frame =
            self.stack.pop().expect("RelBuilder stack is empty (right)");
        let left_frame =
            self.stack.pop().expect("RelBuilder stack is empty (left)");
        let mut row_type = left_frame.rel.row_type().to_vec();
        row_type.extend_from_slice(right_frame.rel.row_type());
        let rel = Rel::Join {
            left: Box::new(left_frame.rel),
            right: Box::new(right_frame.rel),
            join_type,
            condition,
            row_type,
        };
        self.push(rel)
    }

    /// Joins the top two frames using equality of shared column names.
    ///
    /// For each name in `field_names`, an equality condition
    /// `left.col = right.col` is built. The conditions are ANDed.
    /// Uses an INNER join unless `join_type` is specified.
    pub fn join_using(
        &mut self,
        join_type: JoinType,
        field_names: &[&str],
    ) -> &mut Self {
        if self.error.is_some() {
            return self;
        }
        // Peek at the two top frames (don't pop yet).
        let n = self.stack.len();
        assert!(n >= 2, "join_using requires at least two frames");
        let left_rt = self.stack[n - 2].rel.row_type().to_vec();
        let right_rt = self.stack[n - 1].rel.row_type().to_vec();
        let left_len = left_rt.len();
        // Build equality conditions for each shared field.
        // Use "$N" identifiers to encode absolute ordinals so that
        // write_expr emits them verbatim and avoids name collisions.
        let mut conditions: Vec<Expr> = Vec::new();
        for name in field_names {
            let l_idx = match left_rt.iter().position(|(n, _)| n == name) {
                Some(i) => i,
                None => {
                    return self.set_error(RelError::FieldNotFound(format!(
                        "{} (left input)",
                        name
                    )));
                }
            };
            let r_idx = match right_rt.iter().position(|(n, _)| n == name) {
                Some(i) => i,
                None => {
                    return self.set_error(RelError::FieldNotFound(format!(
                        "{} (right input)",
                        name
                    )));
                }
            };
            let l_ty = left_rt[l_idx].1.clone();
            let r_ty = right_rt[r_idx].1.clone();
            let abs_r = left_len + r_idx;
            let l_expr =
                Expr::Identifier(Box::new(l_ty), format!("${}", l_idx));
            let r_expr =
                Expr::Identifier(Box::new(r_ty), format!("${}", abs_r));
            conditions.push(binary_op("=", bool_type(), l_expr, r_expr));
        }
        let condition = conditions
            .into_iter()
            .reduce(|a, b| binary_op("andalso", bool_type(), a, b))
            .unwrap_or_else(|| {
                Expr::Literal(Box::new(bool_type()), Val::Bool(true))
            });
        self.join(join_type, condition)
    }

    /// Returns a field-reference to column `name` in the frame at
    /// `input_offset` from the top of the stack (0 = top, 1 = second).
    ///
    /// When called with two frames on the stack (e.g. before a join),
    /// this can unambiguously reference a column in either input.
    /// `input_offset=1` is the left input; `input_offset=0` is the right.
    ///
    /// The identifier name is encoded as `"$N"` where N is the absolute
    /// ordinal in the combined (future) join row type. This lets
    /// `write_expr` emit `$N` verbatim when the name is unambiguous.
    /// Returns a field-reference to column `name` in the frame at
    /// `input_offset` from the top of the stack (0 = top, 1 = second).
    ///
    /// Returns [`RelError::FieldNotFound`] if the column is absent.
    pub fn field2(
        &self,
        input_offset: usize,
        name: &str,
    ) -> Result<Expr, RelError> {
        let n = self.stack.len();
        assert!(
            input_offset < n,
            "field2: input_offset {} out of range",
            input_offset
        );
        let frame_idx = n - 1 - input_offset;
        let row = self.stack[frame_idx].rel.row_type();
        let col_ord = match row.iter().position(|(col, _)| col == name) {
            Some(i) => i,
            None => return Err(RelError::FieldNotFound(name.to_string())),
        };
        let (_, ty) = &row[col_ord];
        // Compute the absolute ordinal: sum column counts of frames
        // that appear to the LEFT (i.e. at lower stack indices).
        // In the join's combined row type, stack[0] is leftmost.
        let preceding_cols: usize = self.stack[..frame_idx]
            .iter()
            .map(|f| f.rel.row_type().len())
            .sum();
        let abs_ord = preceding_cols + col_ord;
        // Encode as "$N" so write_expr emits it verbatim.
        Ok(Expr::Identifier(
            Box::new(ty.clone()),
            format!("${}", abs_ord),
        ))
    }

    /// Returns a field-reference expression for column `name` in the
    /// frame whose alias matches `alias`.
    ///
    /// The returned expression encodes the column as an absolute ordinal
    /// `"$N"` across all frames on the stack (left-to-right), matching
    /// the semantics of [`field2`].
    ///
    /// Returns [`RelError::FieldNotFound`] if no frame carries `alias`
    /// or the named column is absent in the matching frame.
    ///
    /// [`field2`]: RelBuilder::field2
    pub fn field_from(
        &self,
        alias: &str,
        name: &str,
    ) -> Result<Expr, RelError> {
        let mut base = 0usize;
        for frame in &self.stack {
            let row = frame.rel.row_type();
            if frame.alias.as_deref() == Some(alias) {
                return match row.iter().position(|(col, _)| col == name) {
                    Some(i) => {
                        let (_, ty) = &row[i];
                        Ok(Expr::Identifier(
                            Box::new(ty.clone()),
                            format!("${}", base + i),
                        ))
                    }
                    None => Err(RelError::FieldNotFound(name.to_string())),
                };
            }
            base += row.len();
        }
        Err(RelError::FieldNotFound(format!("{}.{}", alias, name)))
    }

    // -------------------------------------------------------------------
    // Set operations
    // -------------------------------------------------------------------

    /// Pops 2 frames and pushes their UNION \[ALL\].
    ///
    /// The two inputs must have the same number of columns. The row type
    /// is taken from the left (bottom) input.
    ///
    /// Returns [`RelError::SetOpColumnMismatch`] if column counts differ.
    pub fn union(&mut self, all: bool) -> Result<&mut Self, RelError> {
        self.union_n(all, 2)
    }

    /// Pops `n` frames and pushes their UNION \[ALL\].
    ///
    /// If `n == 1`, the single input is left on the stack unchanged
    /// (identity). Returns [`RelError::SetOpColumnMismatch`] if any input
    /// has a different column count from the first.
    pub fn union_n(
        &mut self,
        all: bool,
        n: usize,
    ) -> Result<&mut Self, RelError> {
        if n == 1 {
            return Ok(self);
        }
        let expected = self.stack[self.stack.len() - n].rel.row_type().len();
        for i in 1..n {
            let got = self.stack[self.stack.len() - n + i].rel.row_type().len();
            if got != expected {
                return Err(RelError::SetOpColumnMismatch { expected, got });
            }
        }
        let inputs = self.pop_n(n, "union_n");
        let row_type = inputs[0].row_type().to_vec();
        Ok(self.push(Rel::Union {
            inputs,
            all,
            row_type,
        }))
    }

    /// Pops 2 frames and pushes their INTERSECT \[ALL\].
    ///
    /// Returns [`RelError::SetOpColumnMismatch`] if column counts differ.
    pub fn intersect(&mut self, all: bool) -> Result<&mut Self, RelError> {
        self.intersect_n(all, 2)
    }

    /// Pops `n` frames and pushes their INTERSECT \[ALL\].
    ///
    /// If `n == 1`, the single input is left on the stack unchanged
    /// (identity). Returns [`RelError::SetOpColumnMismatch`] if any input
    /// has a different column count from the first.
    pub fn intersect_n(
        &mut self,
        all: bool,
        n: usize,
    ) -> Result<&mut Self, RelError> {
        if n == 1 {
            return Ok(self);
        }
        let expected = self.stack[self.stack.len() - n].rel.row_type().len();
        for i in 1..n {
            let got = self.stack[self.stack.len() - n + i].rel.row_type().len();
            if got != expected {
                return Err(RelError::SetOpColumnMismatch { expected, got });
            }
        }
        let inputs = self.pop_n(n, "intersect_n");
        let row_type = inputs[0].row_type().to_vec();
        Ok(self.push(Rel::Intersect {
            inputs,
            all,
            row_type,
        }))
    }

    /// Pops 2 frames and pushes their EXCEPT \[ALL\] (set difference).
    ///
    /// Returns [`RelError::SetOpColumnMismatch`] if column counts differ.
    pub fn minus(&mut self, all: bool) -> Result<&mut Self, RelError> {
        let expected = self.stack[self.stack.len() - 2].rel.row_type().len();
        let got = self.stack[self.stack.len() - 1].rel.row_type().len();
        if got != expected {
            return Err(RelError::SetOpColumnMismatch { expected, got });
        }
        let inputs = self.pop_n(2, "minus");
        let row_type = inputs[0].row_type().to_vec();
        Ok(self.push(Rel::Minus {
            inputs,
            all,
            row_type,
        }))
    }

    // -------------------------------------------------------------------
    // Recursive union
    // -------------------------------------------------------------------

    /// Builds a `Rel::RepeatUnion` from the top two items on the stack.
    ///
    /// The second-from-top item is the **seed** relation (evaluated once);
    /// the top item is the **iterative** relation (applied repeatedly).
    /// `all` controls whether duplicate rows are kept.
    /// `iteration_limit` caps the number of recursive steps; `None` means
    /// run until a fixed point (no new rows).
    ///
    /// Both inputs must have the same column count.
    pub fn repeat_union(
        &mut self,
        all: bool,
        iteration_limit: Option<usize>,
    ) -> Result<&mut Self, RelError> {
        if self.error.is_some() {
            return Ok(self);
        }
        let expected = self.stack[self.stack.len() - 2].rel.row_type().len();
        let got = self.stack[self.stack.len() - 1].rel.row_type().len();
        if got != expected {
            return Err(RelError::SetOpColumnMismatch { expected, got });
        }
        let mut inputs = self.pop_n(2, "repeat_union");
        let iterative = Box::new(inputs.pop().unwrap());
        let seed = Box::new(inputs.pop().unwrap());
        let row_type = seed.row_type().to_vec();
        Ok(self.push(Rel::RepeatUnion {
            seed,
            iterative,
            all,
            iteration_limit,
            row_type,
        }))
    }

    /// Declares a new correlation variable bound to the current
    /// top-of-stack row type and returns its name (e.g. `"$cor0"`).
    ///
    /// Call this after pushing the left input, before building the right
    /// sub-plan.  Use the returned name with [`cor_field`] to reference
    /// left columns inside the right sub-plan, then pass the name to
    /// [`correlate`].
    ///
    /// [`cor_field`]: RelBuilder::cor_field
    /// [`correlate`]: RelBuilder::correlate
    pub fn declare_variable(&mut self) -> String {
        let row_type = self.peek_row_type().to_vec();
        let id = format!("$cor{}", self.next_cor_id);
        self.next_cor_id += 1;
        self.declared_variables
            .insert(id.clone(), (row_type, vec![]));
        id
    }

    /// Returns a correlation-variable field reference for `field_name`
    /// within `cor_id`.
    ///
    /// Records `field_name`'s ordinal in the correlation variable's
    /// required-columns set.  Returns [`RelError::UndeclaredCorrelationId`]
    /// if `cor_id` was not previously declared, or
    /// [`RelError::FieldNotFound`] if the field does not exist in the
    /// declared row type.
    pub fn cor_field(
        &mut self,
        cor_id: &str,
        field_name: &str,
    ) -> Result<Expr, RelError> {
        let (row_type, required) =
            self.declared_variables.get_mut(cor_id).ok_or_else(|| {
                RelError::UndeclaredCorrelationId(cor_id.to_string())
            })?;
        match row_type.iter().position(|(n, _)| n == field_name) {
            Some(idx) => {
                let ty = row_type[idx].1.clone();
                if !required.contains(&idx) {
                    required.push(idx);
                    required.sort();
                }
                let ref_name = format!("{}::{}", cor_id, field_name);
                Ok(Expr::Identifier(Box::new(ty), ref_name))
            }
            None => Err(RelError::FieldNotFound(field_name.to_string())),
        }
    }

    /// Creates a [`Rel::Correlate`] node by popping the right input then
    /// the left input from the stack.
    ///
    /// `cor_id` must be a name previously returned by [`declare_variable`].
    /// `join_type` must be `Inner`, `Left`, `Semi`, or `Anti`; `Right` and
    /// `Full` are unsupported and return
    /// [`RelError::UnsupportedCorrelateJoinType`].
    ///
    /// The `required_columns` of the node are the ordinals of left columns
    /// that were referenced via [`cor_field`] for this `cor_id`.
    ///
    /// [`declare_variable`]: RelBuilder::declare_variable
    /// [`cor_field`]: RelBuilder::cor_field
    pub fn correlate(
        &mut self,
        join_type: JoinType,
        cor_id: &str,
    ) -> Result<&mut Self, RelError> {
        if matches!(join_type, JoinType::Right | JoinType::Full) {
            return Err(RelError::UnsupportedCorrelateJoinType(format!(
                "{:?}",
                join_type
            )));
        }
        let required_columns = self
            .declared_variables
            .get(cor_id)
            .ok_or_else(|| {
                RelError::UndeclaredCorrelationId(cor_id.to_string())
            })?
            .1
            .clone();
        let mut inputs = self.pop_n(2, "correlate");
        let right = Box::new(inputs.pop().unwrap());
        let left = Box::new(inputs.pop().unwrap());
        let row_type = match join_type {
            JoinType::Semi | JoinType::Anti => left.row_type().to_vec(),
            _ => {
                let mut rt = left.row_type().to_vec();
                rt.extend_from_slice(right.row_type());
                rt
            }
        };
        Ok(self.push(Rel::Correlate {
            left,
            right,
            correlation_id: cor_id.to_string(),
            join_type,
            required_columns,
            row_type,
        }))
    }

    // -------------------------------------------------------------------
    // Expression builders
    // -------------------------------------------------------------------

    /// Returns a field-reference expression for the named column in the
    /// top-of-stack row type.
    ///
    /// Returns [`RelError::FieldNotFound`] if no column with that name
    /// exists.
    pub fn field(&self, name: &str) -> Result<Expr, RelError> {
        let row = self.peek_row_type();
        match row.iter().find(|(n, _)| n == name) {
            Some((_, ty)) => {
                Ok(Expr::Identifier(Box::new(ty.clone()), name.to_string()))
            }
            None => Err(RelError::FieldNotFound(name.to_string())),
        }
    }

    /// Returns a field-reference expression for the column at `ordinal`
    /// in the top-of-stack row type.
    ///
    /// Returns [`RelError::FieldOrdinalOutOfRange`] if the ordinal is out
    /// of range.
    pub fn field_ordinal(&self, ordinal: usize) -> Result<Expr, RelError> {
        let row = self.peek_row_type();
        match row.get(ordinal) {
            Some((name, ty)) => {
                Ok(Expr::Identifier(Box::new(ty.clone()), name.clone()))
            }
            None => Err(RelError::FieldOrdinalOutOfRange {
                ordinal,
                len: row.len(),
            }),
        }
    }

    /// Returns the named field of a record-typed expression.
    ///
    /// Returns `Err(FieldOnNonRecord)` if `expr` is not of record type, or
    /// `Err(FieldNotFound)` if the record has no field with that name.
    pub fn field_on(&self, expr: &Expr, name: &str) -> Result<Expr, RelError> {
        match *expr.type_() {
            Type::Record(_, ref fields) => {
                let label = Label::String(name.to_string());
                match fields.get(&label) {
                    Some(ty) => Ok(Expr::Identifier(
                        Box::new(ty.clone()),
                        name.to_string(),
                    )),
                    None => Err(RelError::FieldNotFound(name.to_string())),
                }
            }
            ref t => Err(RelError::FieldOnNonRecord(type_name(t))),
        }
    }

    /// Returns a boolean literal expression.
    pub fn literal_bool(&self, v: bool) -> Expr {
        Expr::Literal(Box::new(bool_type()), Val::Bool(v))
    }

    /// Returns an integer literal expression.
    pub fn literal_int(&self, v: i32) -> Expr {
        Expr::Literal(Box::new(int_type()), Val::Int(v))
    }

    /// Returns a string literal expression.
    pub fn literal_string(&self, v: impl Into<String>) -> Expr {
        Expr::Literal(Box::new(string_type()), Val::String(v.into()))
    }

    /// Returns a real (float) literal expression.
    pub fn literal_real(&self, v: f32) -> Expr {
        let ty = Type::Primitive(PrimitiveType::Real);
        Expr::Literal(Box::new(ty), Val::Real(v))
    }

    /// Wraps `expr` with a named alias.
    ///
    /// In Calcite, aliases are used only to rename projected columns.
    /// Here the alias is simply surfaced to [`project_named`], which
    /// accepts explicit names.
    ///
    /// [`project_named`]: RelBuilder::project_named
    pub fn alias_expr(&self, expr: Expr, name: &str) -> (Expr, String) {
        (expr, name.to_string())
    }

    // --- arithmetic operators -------------------------------------------

    /// Returns `a + b` (integer or real addition).
    pub fn plus(&self, a: Expr, b: Expr) -> Result<Expr, RelError> {
        let ta = *a.type_();
        let tb = *b.type_();
        if !is_numeric(&ta) || !is_numeric(&tb) {
            return Err(RelError::TypeMismatch {
                op: "+".to_string(),
                left: type_name(&ta),
                right: type_name(&tb),
            });
        }
        Ok(binary_op("+", ta, a, b))
    }

    /// Returns `a - b` (integer or real subtraction).
    pub fn minus_op(&self, a: Expr, b: Expr) -> Result<Expr, RelError> {
        let ta = *a.type_();
        let tb = *b.type_();
        if !is_numeric(&ta) || !is_numeric(&tb) {
            return Err(RelError::TypeMismatch {
                op: "-".to_string(),
                left: type_name(&ta),
                right: type_name(&tb),
            });
        }
        Ok(binary_op("-", ta, a, b))
    }

    /// Returns `a * b` (integer or real multiplication).
    pub fn times(&self, a: Expr, b: Expr) -> Result<Expr, RelError> {
        let ta = *a.type_();
        let tb = *b.type_();
        if !is_numeric(&ta) || !is_numeric(&tb) {
            return Err(RelError::TypeMismatch {
                op: "*".to_string(),
                left: type_name(&ta),
                right: type_name(&tb),
            });
        }
        Ok(binary_op("*", ta, a, b))
    }

    // --- binary comparison operators ------------------------------------

    /// Returns `a = b`.
    pub fn equals(&self, a: Expr, b: Expr) -> Expr {
        binary_op("=", bool_type(), a, b)
    }

    /// Returns `a <> b`.
    pub fn not_equals(&self, a: Expr, b: Expr) -> Expr {
        binary_op("<>", bool_type(), a, b)
    }

    /// Returns `a < b`.
    pub fn lt(&self, a: Expr, b: Expr) -> Expr {
        binary_op("<", bool_type(), a, b)
    }

    /// Returns `a <= b`.
    pub fn le(&self, a: Expr, b: Expr) -> Expr {
        binary_op("<=", bool_type(), a, b)
    }

    /// Returns `a > b`.
    pub fn gt(&self, a: Expr, b: Expr) -> Expr {
        binary_op(">", bool_type(), a, b)
    }

    /// Returns `a >= b`.
    pub fn ge(&self, a: Expr, b: Expr) -> Expr {
        binary_op(">=", bool_type(), a, b)
    }

    // --- boolean operators ----------------------------------------------

    /// Returns `a andalso b`, with constant folding:
    /// - `AND(_, false)` or `AND(false, _)` → `false`
    /// - `AND(x, true)` → `x`; `AND(true, x)` → `x`
    /// - `AND(x, x)` → `x` (structural duplicate)
    pub fn and(&self, a: Expr, b: Expr) -> Expr {
        if is_false(&a) || is_false(&b) {
            return Expr::Literal(Box::new(bool_type()), Val::Bool(false));
        }
        if is_true(&b) {
            return a;
        }
        if is_true(&a) {
            return b;
        }
        // Structural duplicate: compare debug representations.
        if format!("{:?}", a) == format!("{:?}", b) {
            return a;
        }
        binary_op("andalso", bool_type(), a, b)
    }

    /// Returns `a orelse b`, with constant folding:
    /// - `OR(x, true)` or `OR(true, x)` → `true`
    /// - `OR(x, false)` → `x`; `OR(false, x)` → `x`
    /// - `OR(x, x)` → `x` (structural duplicate)
    pub fn or(&self, a: Expr, b: Expr) -> Expr {
        if is_true(&a) || is_true(&b) {
            return Expr::Literal(Box::new(bool_type()), Val::Bool(true));
        }
        if is_false(&b) {
            return a;
        }
        if is_false(&a) {
            return b;
        }
        if format!("{:?}", a) == format!("{:?}", b) {
            return a;
        }
        binary_op("orelse", bool_type(), a, b)
    }

    /// Returns `not a`, with double-negation elimination:
    /// - `NOT(NOT(x))` → `x`
    pub fn not(&self, a: Expr) -> Expr {
        // Double-negation: NOT(NOT(x)) → x
        if let Expr::Apply(_, func, inner, _) = &a
            && let Expr::Identifier(_, op) = func.as_ref()
            && op == "not"
        {
            return *inner.clone();
        }
        unary_op("not", bool_type(), a)
    }

    // --- null tests -----------------------------------------------------

    /// Returns `is_null(a)`.
    pub fn is_null(&self, a: Expr) -> Expr {
        unary_op("is_null", bool_type(), a)
    }

    /// Returns `is_not_null(a)`.
    pub fn is_not_null(&self, a: Expr) -> Expr {
        unary_op("is_not_null", bool_type(), a)
    }

    // --- cast -----------------------------------------------------------

    /// Returns `CAST(a AS target)`.
    ///
    /// The returned expression has type `target`.
    pub fn cast(&self, a: Expr, target: Type) -> Expr {
        let a_ty = *a.type_();
        let op_ty = Type::Fn(Box::new(a_ty), Box::new(target.clone()));
        let op_expr = Expr::Identifier(Box::new(op_ty), "CAST".to_string());
        Expr::Apply(
            Box::new(target),
            Box::new(op_expr),
            Box::new(a),
            Span::new(""),
        )
    }

    // --- string predicates / BETWEEN ------------------------------------

    /// Returns `a BETWEEN low AND high`
    /// (equivalent to `a >= low AND a <= high`).
    pub fn between(&self, a: Expr, low: Expr, high: Expr) -> Expr {
        let ge = self.ge(a.clone(), low);
        let le = self.le(a, high);
        self.and(ge, le)
    }

    /// Returns `CASE WHEN cond THEN then_val ELSE else_val END`.
    ///
    /// The result type is the type of `then_val`.
    pub fn case_when(
        &self,
        cond: Expr,
        then_val: Expr,
        else_val: Expr,
    ) -> Expr {
        let result_type = *then_val.type_();
        let else_ty = *else_val.type_();
        let then_ty = result_type.clone();
        // CASE is a 3-arg curried function:
        // Apply(Apply(Apply(Identifier("CASE"), cond), then_val), else_val)
        let fn3_ty = Type::Fn(Box::new(else_ty), Box::new(result_type.clone()));
        let fn2_ty = Type::Fn(Box::new(then_ty), Box::new(fn3_ty.clone()));
        let fn1_ty = Type::Fn(Box::new(bool_type()), Box::new(fn2_ty.clone()));
        let case_id = Expr::Identifier(Box::new(fn1_ty), "CASE".to_string());
        let a1 = Expr::Apply(
            Box::new(fn2_ty),
            Box::new(case_id),
            Box::new(cond),
            Span::new(""),
        );
        let a2 = Expr::Apply(
            Box::new(fn3_ty),
            Box::new(a1),
            Box::new(then_val),
            Span::new(""),
        );
        Expr::Apply(
            Box::new(result_type),
            Box::new(a2),
            Box::new(else_val),
            Span::new(""),
        )
    }

    /// Returns `a ILIKE b` (case-insensitive LIKE).
    pub fn ilike(&self, a: Expr, b: Expr) -> Expr {
        binary_op("ILIKE", bool_type(), a, b)
    }

    /// Returns `a IS DISTINCT FROM b`.
    pub fn is_distinct_from(&self, a: Expr, b: Expr) -> Expr {
        binary_op("IS DISTINCT FROM", bool_type(), a, b)
    }

    /// Returns `a IS NOT DISTINCT FROM b`.
    pub fn is_not_distinct_from(&self, a: Expr, b: Expr) -> Expr {
        binary_op("IS NOT DISTINCT FROM", bool_type(), a, b)
    }

    /// Returns `a LIKE b`.
    pub fn like(&self, a: Expr, b: Expr) -> Expr {
        binary_op("LIKE", bool_type(), a, b)
    }

    /// Returns `a NOT ILIKE b`.
    pub fn not_ilike(&self, a: Expr, b: Expr) -> Expr {
        binary_op("NOT ILIKE", bool_type(), a, b)
    }

    /// Returns `a NOT LIKE b`.
    pub fn not_like(&self, a: Expr, b: Expr) -> Expr {
        binary_op("NOT LIKE", bool_type(), a, b)
    }

    /// Returns `a NOT SIMILAR TO b`.
    pub fn not_similar_to(&self, a: Expr, b: Expr) -> Expr {
        binary_op("NOT SIMILAR TO", bool_type(), a, b)
    }

    /// Returns `a SIMILAR TO b`.
    pub fn similar_to(&self, a: Expr, b: Expr) -> Expr {
        binary_op("SIMILAR TO", bool_type(), a, b)
    }

    // --- subquery expressions -------------------------------------------

    /// Wraps `rel` as a scalar subquery expression.
    ///
    /// Applies Morel's `Relational.only` to the [`Expr::Rel`], which
    /// extracts the single row from the subquery.  If `rel` has bag type
    /// `r bag`, the return type is `r` (the record type of that row).
    pub fn scalar_query(&self, rel: Rel) -> Expr {
        let record_type = columns_to_record_type(rel.row_type());
        let subq = Expr::Rel(Box::new(rel));
        unary_op("only", record_type, subq)
    }

    /// Returns `nonEmpty({rel})` — true iff the subquery produces at least
    /// one row.
    ///
    /// Uses Morel's `Relational.nonEmpty` function rather than SQL's
    /// `EXISTS`, so the inner [`Expr::Rel`] carries the natural bag type
    /// of `rel`.
    pub fn exists(&self, rel: Rel) -> Expr {
        let subq = Expr::Rel(Box::new(rel));
        unary_op("nonEmpty", bool_type(), subq)
    }

    /// Returns `UNIQUE({rel})` (true iff the subquery has no duplicate rows).
    pub fn unique(&self, rel: Rel) -> Expr {
        let subq = Expr::Rel(Box::new(rel));
        unary_op("UNIQUE", bool_type(), subq)
    }

    /// Returns `ARRAY({rel})`.
    pub fn array_query(&self, rel: Rel) -> Expr {
        let subq = Expr::Rel(Box::new(rel));
        unary_op("ARRAY", bool_type(), subq)
    }

    /// Returns `MULTISET({rel})`.
    pub fn multiset_query(&self, rel: Rel) -> Expr {
        let subq = Expr::Rel(Box::new(rel));
        unary_op("MULTISET", bool_type(), subq)
    }

    /// Returns `MAP({rel})`.
    pub fn map_query(&self, rel: Rel) -> Expr {
        let subq = Expr::Rel(Box::new(rel));
        unary_op("MAP", bool_type(), subq)
    }

    /// Returns `col IN ({rel})`.
    pub fn in_subquery(&self, col: Expr, rel: Rel) -> Expr {
        let subq = Expr::Rel(Box::new(rel));
        binary_op("IN", bool_type(), col, subq)
    }

    /// Returns `col cmp_op SOME ({rel})`.
    ///
    /// `cmp_op` is a comparison operator: `">"`, `"<"`, `">="`, `"<="`,
    /// `"="`, or `"<>"`.
    pub fn some_query(&self, cmp_op: &str, col: Expr, rel: Rel) -> Expr {
        let subq = Expr::Rel(Box::new(rel));
        let op = format!("SOME({})", cmp_op);
        binary_op(&op, bool_type(), col, subq)
    }

    /// Returns `col cmp_op ALL ({rel})`.
    pub fn all_query(&self, cmp_op: &str, col: Expr, rel: Rel) -> Expr {
        let subq = Expr::Rel(Box::new(rel));
        let op = format!("ALL({})", cmp_op);
        binary_op(&op, bool_type(), col, subq)
    }
}

// -----------------------------------------------------------------------
// Helper functions
// -----------------------------------------------------------------------

/// Returns a deduplication key for an [`AggCall`] based on its identity:
/// function, argument ordinals, DISTINCT flag, and optional filter.
/// Two calls with the same key produce the same result and can be merged.
fn agg_call_key(call: &AggCall) -> String {
    format!(
        "{:?}_{:?}_{}_{}",
        call.agg,
        call.args,
        call.distinct,
        call.filter
            .as_ref()
            .map_or("none".to_string(), |f| format!("{:?}", f))
    )
}

/// Returns the output type of an aggregate function.
///
/// `COUNT` and `COUNT(*)` return `int`; `AVG` returns `real`; all other
/// aggregates return the type of their first argument.
fn agg_return_type(
    agg: AggFunction,
    args: &[usize],
    row_type: &[(String, Type)],
) -> Type {
    match agg {
        // lint: sort until '#}' where '##[A-Z]'
        AggFunction::Avg => Type::Primitive(PrimitiveType::Real),
        AggFunction::Count | AggFunction::CountStar => int_type(),
        AggFunction::Grouping | AggFunction::GroupingId => int_type(),
        _ => {
            if let Some(&i) = args.first() {
                row_type[i].1.clone()
            } else {
                int_type()
            }
        }
    }
}

/// Returns `true` when `inner_coll` (on `inner_row_type`) already satisfies
/// `outer_coll` mapped through `project_exprs`.
///
/// Each outer key must correspond to a simple `Identifier` projection whose
/// column in the inner row type aligns — at the same position — with the
/// inner collation, with matching direction.
fn can_subsume_inner_sort(
    outer_coll: &[FieldCollation],
    project_exprs: &[Expr],
    inner_coll: &[FieldCollation],
    inner_row_type: &[(String, Type)],
) -> bool {
    if outer_coll.len() > inner_coll.len() {
        return false;
    }
    for (i, outer_fc) in outer_coll.iter().enumerate() {
        let proj_expr = &project_exprs[outer_fc.index];
        let col_name = match proj_expr {
            Expr::Identifier(_, name) => name.as_str(),
            _ => return false,
        };
        let inner_idx =
            match inner_row_type.iter().position(|(n, _)| n == col_name) {
                Some(idx) => idx,
                None => return false,
            };
        let ifc = &inner_coll[i];
        if ifc.index != inner_idx || ifc.direction != outer_fc.direction {
            return false;
        }
    }
    true
}

/// Converts `SortKey` list to `Vec<FieldCollation>`, resolving each
/// expression to a column ordinal in `row_type`. Duplicate keys (same
/// ordinal) are removed (first occurrence wins).
fn sort_keys_to_collation(
    keys: &[SortKey],
    row_type: &[(String, Type)],
) -> Vec<FieldCollation> {
    let mut seen = std::collections::HashSet::new();
    let mut result = Vec::new();
    for key in keys {
        let Expr::Identifier(_, name) = &key.expr else {
            continue;
        };
        let Some(index) = row_type.iter().position(|(n, _)| n == name) else {
            continue;
        };
        if seen.insert(index) {
            result.push(FieldCollation {
                index,
                direction: key.direction,
                null_direction: key.null_direction,
            });
        }
    }
    result
}

/// Constructs a curried binary-operator application:
/// `Apply(ret, Apply(fn_ty, Identifier(op), a), b)`.
fn binary_op(op: &str, ret: Type, a: Expr, b: Expr) -> Expr {
    let a_ty = *a.type_();
    let b_ty = *b.type_();
    // Type of the partially-applied function: a_ty → b_ty → ret
    let partial_ty = Type::Fn(Box::new(b_ty), Box::new(ret.clone()));
    // Type of the full operator: a_ty → (b_ty → ret)
    let op_ty = Type::Fn(Box::new(a_ty), Box::new(partial_ty.clone()));
    let op_expr = Expr::Identifier(Box::new(op_ty), op.to_string());
    let partial = Expr::Apply(
        Box::new(partial_ty),
        Box::new(op_expr),
        Box::new(a),
        Span::new(""),
    );
    Expr::Apply(Box::new(ret), Box::new(partial), Box::new(b), Span::new(""))
}

/// Constructs a unary-operator application: `Apply(ret, Identifier(op), a)`.
fn unary_op(op: &str, ret: Type, a: Expr) -> Expr {
    let a_ty = *a.type_();
    let op_ty = Type::Fn(Box::new(a_ty), Box::new(ret.clone()));
    let op_expr = Expr::Identifier(Box::new(op_ty), op.to_string());
    Expr::Apply(Box::new(ret), Box::new(op_expr), Box::new(a), Span::new(""))
}

/// Returns `true` if `expr` is the boolean literal `true`.
fn is_true(expr: &Expr) -> bool {
    matches!(expr, Expr::Literal(_, Val::Bool(true)))
}

/// Returns `true` if `expr` is the boolean literal `false`.
fn is_false(expr: &Expr) -> bool {
    matches!(expr, Expr::Literal(_, Val::Bool(false)))
}

/// Returns `true` if `t` is a numeric type (int or real).
fn is_numeric(t: &Type) -> bool {
    matches!(t, Type::Primitive(PrimitiveType::Int | PrimitiveType::Real))
}

/// Returns a short human-readable name for `t` (for error messages).
fn type_name(t: &Type) -> String {
    match t {
        Type::Primitive(p) => p.as_str().to_string(),
        Type::Record(_, _) => "record".to_string(),
        Type::Bag(_) => "bag".to_string(),
        _ => format!("{:?}", t),
    }
}

/// Returns a column name for `expr` if it is a simple field reference.
fn expr_name(expr: &Expr, row_type: &[(String, Type)]) -> Option<String> {
    let Expr::Identifier(_, name) = expr else {
        return None;
    };
    row_type
        .iter()
        .any(|(n, _)| n == name)
        .then(|| name.clone())
}

/// Tries to compose an outer projection on top of an inner projection.
///
/// Returns `Some(composed)` when every outer expression is a simple field
/// reference (`Identifier`) to one of the inner project's output columns;
/// the corresponding inner expression is substituted. Returns `None` if
/// any outer expression is not a simple field reference (e.g. computed).
fn try_compose_projects(
    outer_exprs: &[Expr],
    inner_exprs: &[Expr],
    inner_row_type: &[(String, Type)],
) -> Option<Vec<Expr>> {
    outer_exprs
        .iter()
        .map(|e| {
            if let Expr::Identifier(_, name) = e {
                let idx = inner_row_type.iter().position(|(n, _)| n == name)?;
                Some(inner_exprs[idx].clone())
            } else {
                None
            }
        })
        .collect()
}

/// Returns `true` if `exprs` is the identity projection for `row_type`:
/// each expression is `Identifier(_, col_name)` matching the column at
/// the same ordinal.
fn is_identity_project(exprs: &[Expr], row_type: &[(String, Type)]) -> bool {
    if exprs.len() != row_type.len() {
        return false;
    }
    exprs
        .iter()
        .zip(row_type.iter())
        .all(|(e, (name, _))| matches!(e, Expr::Identifier(_, n) if n == name))
}

/// Infers a [`Type`] from a [`Val`].
fn val_type(v: &Val) -> Type {
    match v {
        // lint: sort until '#}' where '##[A-Z]'
        Val::Bool(_) => bool_type(),
        Val::Int(_) => int_type(),
        Val::Real(_) => Type::Primitive(PrimitiveType::Real),
        Val::String(_) => string_type(),
        _ => string_type(), // safe default
    }
}

impl fmt::Display for RelBuilder {
    /// Formats the top-of-stack plan as a multi-line explain string.
    ///
    /// Produces the same output as [`crate::rel::display::explain`]
    /// applied to the current top node.  Useful for debugging.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::rel::display::explain;
        if let Some(frame) = self.stack.last() {
            write!(f, "{}", explain(&frame.rel))
        } else {
            write!(f, "(empty)")
        }
    }
}

// -----------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rel::display::explain;
    use crate::rel::schema::scott_schema;
    use indoc::{formatdoc, indoc};

    fn builder() -> RelBuilder {
        RelBuilder::new(Arc::new(scott_schema()))
    }

    // Asserts that the plan displayed by `explain` matches `expected`.
    macro_rules! assert_plan {
        ($rel:expr, $expected:expr) => {
            assert_eq!(explain(&$rel).trim(), $expected.trim())
        };
    }

    // ---------------------------------------------------------------
    // Scan
    // ---------------------------------------------------------------

    #[test]
    fn test_scan() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let plan = b.build().unwrap();
        assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
    }

    #[test]
    fn test_scan_qualified_table() {
        let mut b = builder();
        b.scan(&["scott", "DEPT"]);
        let plan = b.build().unwrap();
        assert_plan!(plan, "LogicalTableScan(table=[[scott, DEPT]])");
    }

    // ---------------------------------------------------------------
    // Values / Empty
    // ---------------------------------------------------------------

    #[test]
    fn test_empty() {
        let mut b = builder();
        let row_type = vec![
            ("A".to_string(), int_type()),
            ("B".to_string(), string_type()),
        ];
        b.empty(row_type);
        let plan = b.build().unwrap();
        assert_plan!(plan, "LogicalValues(tuples=[[]])");
    }

    #[test]
    fn test_values() {
        let mut b = builder();
        b.values(
            &["A", "B"],
            vec![
                vec![Val::Int(1), Val::String("x".into())],
                vec![Val::Int(2), Val::String("y".into())],
            ],
        );
        let plan = b.build().unwrap();
        assert_plan!(plan, "LogicalValues(tuples=[[{ 1, 'x' }, { 2, 'y' }]])");
    }

    // ---------------------------------------------------------------
    // Filter
    // ---------------------------------------------------------------

    #[test]
    fn test_scan_filter_true() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cond = b.literal_bool(true);
        b.filter(cond);
        let plan = b.build().unwrap();
        // simplification: Filter(true) is eliminated
        assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
    }

    #[test]
    fn test_scan_filter_trivially_false() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cond = b.literal_bool(false);
        b.filter(cond);
        let plan = b.build().unwrap();
        // simplification: Filter(false) → empty Values
        assert_plan!(plan, "LogicalValues(tuples=[[]])");
    }

    #[test]
    fn test_scan_filter_equals() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let lhs = b.field("DEPTNO").unwrap();
        let rhs = b.literal_int(20);
        let cond = b.equals(lhs, rhs);
        b.filter(cond);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalFilter(condition=[=($7, 20)])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_scan_filter_greater_than() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let lhs = b.field("SAL").unwrap();
        let rhs = b.literal_int(1000);
        let cond = b.gt(lhs, rhs);
        b.filter(cond);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalFilter(condition=[>($5, 1000)])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    // ---------------------------------------------------------------
    // Project
    // ---------------------------------------------------------------

    #[test]
    fn test_project() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let exprs = vec![b.field("EMPNO").unwrap(), b.field("ENAME").unwrap()];
        b.project(exprs);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalProject(EMPNO=[$0], ENAME=[$1])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_project_identity() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        // Identity projection: all columns in order.
        let exprs: Vec<Expr> =
            (0..8).map(|i| b.field_ordinal(i).unwrap()).collect();
        b.project(exprs);
        let plan = b.build().unwrap();
        // Simplification: identity project is removed.
        assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
    }

    #[test]
    fn test_project_named() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let exprs = vec![b.field("EMPNO").unwrap(), b.field("SAL").unwrap()];
        let names = vec!["employee_no".to_string(), "salary".to_string()];
        b.project_named(exprs, names);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalProject(employee_no=[$0], salary=[$5])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    // ---------------------------------------------------------------
    // Sort / limit
    // ---------------------------------------------------------------

    #[test]
    fn test_sort() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let key = b.field("SAL").unwrap();
        b.sort(&[SortKey {
            expr: key,
            direction: Direction::Ascending,
            null_direction: NullDirection::Unspecified,
        }]);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalSort(sort0=[$5], dir0=[ASC])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_sort_desc() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let key = b.desc(b.field("SAL").unwrap());
        b.sort(&[key]);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalSort(sort0=[$5], dir0=[DESC])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_trivial_sort() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        // Empty key list — no Sort node is pushed.
        b.sort(&[]);
        let plan = b.build().unwrap();
        assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
    }

    #[test]
    fn test_sort_duplicate() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        // Duplicate key: second reference to SAL is dropped.
        let k1 = SortKey {
            expr: b.field("SAL").unwrap(),
            direction: Direction::Ascending,
            null_direction: NullDirection::Unspecified,
        };
        let k2 = SortKey {
            expr: b.field("SAL").unwrap(),
            direction: Direction::Descending,
            null_direction: NullDirection::Unspecified,
        };
        b.sort(&[k1, k2]);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalSort(sort0=[$5], dir0=[ASC])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_limit() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        b.limit(None, Some(10));
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalSort(fetch=[10])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_sort_limit() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let key = b.desc(b.field("SAL").unwrap());
        b.sort_limit(Some(5), Some(3), &[key]);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalSort(sort0=[$5], dir0=[DESC], \
             offset=[5], fetch=[3])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_sort_limit0() {
        // fetch=0 → empty Values
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        b.sort_limit(None, Some(0), &[]);
        let plan = b.build().unwrap();
        assert_plan!(plan, "LogicalValues(tuples=[[]])");
    }

    #[test]
    fn test_sort_offset_limit() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        b.limit(Some(10), Some(5));
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalSort(offset=[10], fetch=[5])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_rename() {
        let mut b = builder();
        b.scan(&["scott", "DEPT"]);
        b.rename(vec![
            "department_no".to_string(),
            "department_name".to_string(),
            "location".to_string(),
        ]);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalProject(department_no=[$0], \
             department_name=[$1], location=[$2])\n  \
             LogicalTableScan(table=[[scott, DEPT]])"
        );
    }

    #[test]
    fn test_rename_no_change() {
        // rename with same names → no Project node
        let mut b = builder();
        b.scan(&["scott", "DEPT"]);
        b.rename(vec![
            "DEPTNO".to_string(),
            "DNAME".to_string(),
            "LOC".to_string(),
        ]);
        let plan = b.build().unwrap();
        assert_plan!(plan, "LogicalTableScan(table=[[scott, DEPT]])");
    }

    // ---------------------------------------------------------------
    // Aggregate
    // ---------------------------------------------------------------

    #[test]
    fn test_aggregate() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let gk = b.group_key(vec![b.field("DEPTNO").unwrap()]);
        let aggs = vec![b.count_star().alias("C")];
        b.aggregate(&gk, aggs);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalAggregate(group=[{7}], C=[COUNT(*)])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_aggregate2() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let gk = b.group_key(vec![
            b.field("DEPTNO").unwrap(),
            b.field("JOB").unwrap(),
        ]);
        let aggs =
            vec![b.count_star().alias("C"), b.sum("SAL").alias("TOTAL_SAL")];
        b.aggregate(&gk, aggs);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalAggregate(group=[{7, 2}], C=[COUNT(*)], \
             TOTAL_SAL=[SUM($5)])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_aggregate_no_group() {
        // No grouping key → single output row.
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let gk = b.group_key(vec![]);
        let aggs = vec![b.count_star().alias("C")];
        b.aggregate(&gk, aggs);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalAggregate(group=[{}], C=[COUNT(*)])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_aggregate_count_distinct() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let gk = b.group_key(vec![b.field("DEPTNO").unwrap()]);
        let aggs = vec![b.count("ENAME").distinct().alias("UNIQUE_EMPS")];
        b.aggregate(&gk, aggs);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalAggregate(group=[{7}], \
             UNIQUE_EMPS=[COUNT(DISTINCT $1)])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_distinct() {
        let mut b = builder();
        b.scan(&["scott", "DEPT"]);
        b.distinct();
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalAggregate(group=[{0, 1, 2}])\n  \
             LogicalTableScan(table=[[scott, DEPT]])"
        );
    }

    // ---------------------------------------------------------------
    // Join and alias
    // ---------------------------------------------------------------

    #[test]
    fn test_join() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        b.scan(&["scott", "DEPT"]);
        // EMP.DEPTNO ($7) = DEPT.DEPTNO ($0 offset by 8 = $8).
        let lhs = b.field2(1, "DEPTNO").unwrap(); // EMP.DEPTNO
        let rhs = b.field2(0, "DEPTNO").unwrap(); // DEPT.DEPTNO
        let cond = b.equals(lhs, rhs);
        b.join(JoinType::Inner, cond);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalJoin(condition=[=($7, $8)], \
             joinType=[inner])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n  \
             LogicalTableScan(table=[[scott, DEPT]])"
        );
    }

    #[test]
    fn test_join_using() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        b.scan(&["scott", "DEPT"]);
        b.join_using(JoinType::Inner, &["DEPTNO"]);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalJoin(condition=[=($7, $8)], \
             joinType=[inner])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n  \
             LogicalTableScan(table=[[scott, DEPT]])"
        );
    }

    #[test]
    fn test_join_left() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        b.scan(&["scott", "DEPT"]);
        b.join_using(JoinType::Left, &["DEPTNO"]);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalJoin(condition=[=($7, $8)], \
             joinType=[left])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n  \
             LogicalTableScan(table=[[scott, DEPT]])"
        );
    }

    #[test]
    fn test_alias() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        b.alias("e");
        b.scan(&["scott", "DEPT"]);
        b.alias("d");
        // Use field2 to reference columns from each aliased input.
        let lhs = b.field2(1, "DEPTNO").unwrap(); // e.DEPTNO
        let rhs = b.field2(0, "DEPTNO").unwrap(); // d.DEPTNO
        let cond = b.equals(lhs, rhs);
        b.join(JoinType::Inner, cond);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalJoin(condition=[=($7, $8)], \
             joinType=[inner])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n  \
             LogicalTableScan(table=[[scott, DEPT]])"
        );
    }

    // ---------------------------------------------------------------
    // Set operations
    // ---------------------------------------------------------------

    #[test]
    fn test_union() {
        let mut b = builder();
        b.values(
            &["A", "B"],
            vec![vec![Val::Int(1), Val::String("x".into())]],
        );
        b.values(
            &["A", "B"],
            vec![vec![Val::Int(2), Val::String("y".into())]],
        );
        b.union(false);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalUnion(all=[false])\n  \
             LogicalValues(tuples=[[{ 1, 'x' }]])\n  \
             LogicalValues(tuples=[[{ 2, 'y' }]])"
        );
    }

    #[test]
    fn test_union_all() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        b.scan(&["scott", "EMP"]);
        b.union(true);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalUnion(all=[true])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_union_3() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        b.scan(&["scott", "EMP"]);
        b.scan(&["scott", "EMP"]);
        b.union_n(false, 3);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalUnion(all=[false])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_intersect() {
        let mut b = builder();
        b.scan(&["scott", "DEPT"]);
        b.scan(&["scott", "DEPT"]);
        b.intersect(false);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalIntersect(all=[false])\n  \
             LogicalTableScan(table=[[scott, DEPT]])\n  \
             LogicalTableScan(table=[[scott, DEPT]])"
        );
    }

    #[test]
    fn test_minus() {
        let mut b = builder();
        b.scan(&["scott", "DEPT"]);
        b.scan(&["scott", "DEPT"]);
        b.minus(false);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            "LogicalMinus(all=[false])\n  \
             LogicalTableScan(table=[[scott, DEPT]])\n  \
             LogicalTableScan(table=[[scott, DEPT]])"
        );
    }

    // ---------------------------------------------------------------
    // Error handling
    // ---------------------------------------------------------------

    #[test]
    fn test_scan_invalid_table() {
        let mut b = builder();
        b.scan(&["scott", "NOSUCHtable"]);
        assert!(matches!(b.build(), Err(RelError::TableNotFound(_))));
    }

    #[test]
    fn test_scan_invalid_schema() {
        let mut b = builder();
        b.scan(&["noschema", "EMP"]);
        assert!(matches!(b.build(), Err(RelError::TableNotFound(_))));
    }

    #[test]
    fn test_bad_field_name() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        assert!(matches!(
            b.field("NOSUCHFIELD"),
            Err(RelError::FieldNotFound(_))
        ));
    }

    #[test]
    fn test_bad_field_ordinal() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        // EMP has 8 columns (ordinals 0–7); ordinal 99 is out of range.
        assert!(matches!(
            b.field_ordinal(99),
            Err(RelError::FieldOrdinalOutOfRange { .. })
        ));
    }

    #[test]
    fn test_filter_non_boolean_condition() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cond = b.literal_int(1); // int, not bool
        b.filter(cond);
        assert!(matches!(b.build(), Err(RelError::NonBooleanCondition(_))));
    }

    #[test]
    fn test_aggregate_group_key_out_of_range() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        // "NOSUCHCOL" does not exist in EMP.
        let bad_expr =
            Expr::Identifier(Box::new(int_type()), "NOSUCHCOL".to_string());
        let gk = b.group_key(vec![bad_expr]);
        b.aggregate(&gk, vec![]);
        assert!(matches!(b.build(), Err(RelError::InvalidGroupKey(_))));
    }

    // ---------------------------------------------------------------
    // AggregateRex: aggregate calls with expression arguments
    // ---------------------------------------------------------------

    #[test]
    fn test_aggregate_rex2() {
        // SUM(SAL + 2): non-trivial expression arg → pre-project inserted.
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let sal = b.field("SAL").unwrap();
        let expr = b.plus(sal, b.literal_int(2)).unwrap();
        let gk = b.group_key(vec![b.field("DEPTNO").unwrap()]);
        let agg = b.sum_expr(expr).alias("S");
        b.aggregate(&gk, vec![agg]);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            indoc! {"
                LogicalAggregate(group=[{7}], S=[SUM($8)])
                  LogicalProject(EMPNO=[$0], ENAME=[$1], JOB=[$2], MGR=[$3], \
                      HIREDATE=[$4], SAL=[$5], COMM=[$6], DEPTNO=[$7], \
                      $f8=[+($5, 2)])
                    LogicalTableScan(table=[[scott, EMP]])"
            }
        );
    }

    #[test]
    fn test_aggregate_rex3() {
        // SUM(2): constant expression arg.
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let gk = b.group_key(vec![b.field("DEPTNO").unwrap()]);
        let agg = b.sum_expr(b.literal_int(2)).alias("S");
        b.aggregate(&gk, vec![agg]);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            indoc! {"
                LogicalAggregate(group=[{7}], S=[SUM($8)])
                  LogicalProject(EMPNO=[$0], ENAME=[$1], JOB=[$2], MGR=[$3], \
                      HIREDATE=[$4], SAL=[$5], COMM=[$6], DEPTNO=[$7], $f8=[2])
                    LogicalTableScan(table=[[scott, EMP]])"
            }
        );
    }

    #[test]
    fn test_aggregate_rex4() {
        // SUM(CASE WHEN DEPTNO=20 THEN SAL ELSE 0): CASE expr arg.
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cond = b.equals(b.field("DEPTNO").unwrap(), b.literal_int(20));
        let then_val = b.field("SAL").unwrap();
        let else_val = b.literal_int(0);
        let case_expr = b.case_when(cond, then_val, else_val);
        let gk = b.group_key(vec![]);
        let agg = b.sum_expr(case_expr).alias("$f0");
        b.aggregate(&gk, vec![agg]);
        let plan = b.build().unwrap();
        assert_plan!(
            plan,
            indoc! {"
                LogicalAggregate(group=[{}], $f0=[SUM($8)])
                  LogicalProject(EMPNO=[$0], ENAME=[$1], JOB=[$2], MGR=[$3], \
                      HIREDATE=[$4], SAL=[$5], COMM=[$6], DEPTNO=[$7], \
                      $f8=[CASE(=($7, 20), $5, 0)])
                    LogicalTableScan(table=[[scott, EMP]])"
            }
        );
    }

    // ---------------------------------------------------------------
    // Correlate
    // ---------------------------------------------------------------

    fn correlate_plan_lines(join_type: &str) -> String {
        formatdoc! {"
            LogicalCorrelate(correlation=[$cor0], joinType=[{}], \
                requiredColumns=[{{7}}])
              LogicalTableScan(table=[[scott, EMP]])
              LogicalFilter(condition=[=($0, $cor0.DEPTNO)])
                LogicalTableScan(table=[[scott, DEPT]])",
            join_type
        }
    }

    #[test]
    fn test_correlate_anti_without_convert() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cor_id = b.declare_variable();
        b.scan(&["scott", "DEPT"]);
        let dept_deptno = b.field("DEPTNO").unwrap();
        let emp_deptno = b.cor_field(&cor_id, "DEPTNO").unwrap();
        let cond = b.equals(dept_deptno, emp_deptno);
        b.filter(cond);
        b.correlate(JoinType::Anti, &cor_id).unwrap();
        let plan = b.build().unwrap();
        assert_plan!(plan, correlate_plan_lines("anti"));
    }

    #[test]
    fn test_correlate_inner_without_convert() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cor_id = b.declare_variable();
        b.scan(&["scott", "DEPT"]);
        let dept_deptno = b.field("DEPTNO").unwrap();
        let emp_deptno = b.cor_field(&cor_id, "DEPTNO").unwrap();
        let cond = b.equals(dept_deptno, emp_deptno);
        b.filter(cond);
        b.correlate(JoinType::Inner, &cor_id).unwrap();
        let plan = b.build().unwrap();
        assert_plan!(plan, correlate_plan_lines("inner"));
    }

    #[test]
    fn test_correlate_left_without_convert() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cor_id = b.declare_variable();
        b.scan(&["scott", "DEPT"]);
        let dept_deptno = b.field("DEPTNO").unwrap();
        let emp_deptno = b.cor_field(&cor_id, "DEPTNO").unwrap();
        let cond = b.equals(dept_deptno, emp_deptno);
        b.filter(cond);
        b.correlate(JoinType::Left, &cor_id).unwrap();
        let plan = b.build().unwrap();
        assert_plan!(plan, correlate_plan_lines("left"));
    }

    #[test]
    fn test_correlate_semi_without_convert() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cor_id = b.declare_variable();
        b.scan(&["scott", "DEPT"]);
        let dept_deptno = b.field("DEPTNO").unwrap();
        let emp_deptno = b.cor_field(&cor_id, "DEPTNO").unwrap();
        let cond = b.equals(dept_deptno, emp_deptno);
        b.filter(cond);
        b.correlate(JoinType::Semi, &cor_id).unwrap();
        let plan = b.build().unwrap();
        assert_plan!(plan, correlate_plan_lines("semi"));
    }

    #[test]
    fn test_correlate_right_throws() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cor_id = b.declare_variable();
        b.scan(&["scott", "DEPT"]);
        assert!(matches!(
            b.correlate(JoinType::Right, &cor_id),
            Err(RelError::UnsupportedCorrelateJoinType(_))
        ));
    }

    #[test]
    fn test_correlate_full_throws() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cor_id = b.declare_variable();
        b.scan(&["scott", "DEPT"]);
        assert!(matches!(
            b.correlate(JoinType::Full, &cor_id),
            Err(RelError::UnsupportedCorrelateJoinType(_))
        ));
    }

    #[test]
    fn test_correlate_undeclared_throws() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        b.scan(&["scott", "DEPT"]);
        assert!(matches!(
            b.correlate(JoinType::Inner, "$cor99"),
            Err(RelError::UndeclaredCorrelationId(_))
        ));
    }
}
