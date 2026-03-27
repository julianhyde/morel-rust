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
//! let cond = b.gt(b.field("SAL"), b.literal_int(1000));
//! b.filter(cond);
//! let plan = b.build();
//! ```

use crate::compile::core::Expr;
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::code::Span;
use crate::eval::val::Val;
use crate::rel::schema::Schema;
use crate::rel::{bool_type, int_type, string_type, Rel};
use std::sync::Arc;

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
}

impl Default for BuilderConfig {
    fn default() -> Self {
        BuilderConfig {
            simplify_filter_true: true,
            simplify_filter_false: true,
            simplify_project_identity: true,
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
}

impl RelBuilder {
    /// Creates a new builder backed by the given schema.
    pub fn new(schema: Arc<dyn Schema>) -> Self {
        RelBuilder {
            schema,
            config: BuilderConfig::default(),
            stack: Vec::new(),
        }
    }

    /// Creates a new builder with a custom configuration.
    pub fn with_config(
        schema: Arc<dyn Schema>,
        config: BuilderConfig,
    ) -> Self {
        RelBuilder {
            schema,
            config,
            stack: Vec::new(),
        }
    }

    // -------------------------------------------------------------------
    // Stack operations
    // -------------------------------------------------------------------

    /// Pushes an arbitrary [`Rel`] node onto the stack and returns
    /// `&mut self` for chaining.
    pub fn push(&mut self, rel: Rel) -> &mut Self {
        self.stack.push(Frame { rel });
        self
    }

    /// Pops the top node from the stack and returns it.
    ///
    /// # Panics
    ///
    /// Panics if the stack is empty.
    pub fn build(&mut self) -> Rel {
        self.stack
            .pop()
            .expect("RelBuilder stack is empty")
            .rel
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
        let entry = self
            .schema
            .table(name)
            .unwrap_or_else(|| {
                panic!("table not found: {:?}", name)
            });
        let rel = Rel::TableScan {
            table_name: entry.name.clone(),
            row_type: entry.columns.clone(),
        };
        self.push(rel)
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
    pub fn values(
        &mut self,
        names: &[&str],
        rows: Vec<Vec<Val>>,
    ) -> &mut Self {
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
                    .map(|(v, t)| {
                        Expr::Literal(Box::new(t.clone()), v)
                    })
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
        if self.config.simplify_filter_true && is_true(&condition) {
            return self; // identity
        }
        if self.config.simplify_filter_false && is_false(&condition) {
            let row_type = self.peek_row_type().to_vec();
            let input = self.build();
            drop(input);
            return self.empty(row_type);
        }
        let input = Box::new(self.build());
        self.push(Rel::Filter { input, condition })
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
        let input = Box::new(self.build());
        self.push(Rel::Project {
            input,
            exprs,
            row_type,
        })
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
        let input = Box::new(self.build());
        self.push(Rel::Project {
            input,
            exprs,
            row_type,
        })
    }

    // -------------------------------------------------------------------
    // Expression builders
    // -------------------------------------------------------------------

    /// Returns a field-reference expression for the named column in the
    /// top-of-stack row type.
    ///
    /// # Panics
    ///
    /// Panics if no column with that name exists.
    pub fn field(&self, name: &str) -> Expr {
        let row = self.peek_row_type();
        let (_, ty) = row
            .iter()
            .find(|(n, _)| n == name)
            .unwrap_or_else(|| {
                panic!("field '{}' not found in row type", name)
            });
        Expr::Identifier(Box::new(ty.clone()), name.to_string())
    }

    /// Returns a field-reference expression for the column at `ordinal`
    /// in the top-of-stack row type.
    ///
    /// # Panics
    ///
    /// Panics if the ordinal is out of range.
    pub fn field_ordinal(&self, ordinal: usize) -> Expr {
        let row = self.peek_row_type();
        let (name, ty) = row.get(ordinal).unwrap_or_else(|| {
            panic!(
                "field ordinal {} out of range (row has {} columns)",
                ordinal,
                row.len()
            )
        });
        Expr::Identifier(Box::new(ty.clone()), name.clone())
    }

    /// Returns a boolean literal expression.
    pub fn literal_bool(&self, v: bool) -> Expr {
        Expr::Literal(
            Box::new(bool_type()),
            Val::Bool(v),
        )
    }

    /// Returns an integer literal expression.
    pub fn literal_int(&self, v: i32) -> Expr {
        Expr::Literal(Box::new(int_type()), Val::Int(v))
    }

    /// Returns a string literal expression.
    pub fn literal_string(&self, v: impl Into<String>) -> Expr {
        Expr::Literal(
            Box::new(string_type()),
            Val::String(v.into()),
        )
    }

    /// Returns a real (float) literal expression.
    pub fn literal_real(&self, v: f32) -> Expr {
        let ty =
            Type::Primitive(PrimitiveType::Real);
        Expr::Literal(Box::new(ty), Val::Real(v))
    }

    /// Wraps `expr` with a named alias.
    ///
    /// In Calcite, aliases are used only to rename projected columns.
    /// Here the alias is simply surfaced to [`project_named`], which
    /// accepts explicit names.
    ///
    /// [`project_named`]: RelBuilder::project_named
    pub fn alias_expr(
        &self,
        expr: Expr,
        name: &str,
    ) -> (Expr, String) {
        (expr, name.to_string())
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

    /// Returns `a andalso b`.
    pub fn and(&self, a: Expr, b: Expr) -> Expr {
        binary_op("andalso", bool_type(), a, b)
    }

    /// Returns `a orelse b`.
    pub fn or(&self, a: Expr, b: Expr) -> Expr {
        binary_op("orelse", bool_type(), a, b)
    }

    /// Returns `not a`.
    pub fn not(&self, a: Expr) -> Expr {
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
}

// -----------------------------------------------------------------------
// Helper functions
// -----------------------------------------------------------------------

/// Constructs a curried binary-operator application:
/// `Apply(ret, Apply(fn_ty, Identifier(op), a), b)`.
fn binary_op(
    op: &str,
    ret: Type,
    a: Expr,
    b: Expr,
) -> Expr {
    let a_ty = *a.type_();
    let b_ty = *b.type_();
    // Type of the partially-applied function: a_ty → b_ty → ret
    let partial_ty =
        Type::Fn(Box::new(b_ty), Box::new(ret.clone()));
    // Type of the full operator: a_ty → (b_ty → ret)
    let op_ty = Type::Fn(
        Box::new(a_ty),
        Box::new(partial_ty.clone()),
    );
    let op_expr =
        Expr::Identifier(Box::new(op_ty), op.to_string());
    let partial = Expr::Apply(
        Box::new(partial_ty),
        Box::new(op_expr),
        Box::new(a),
        Span::new(""),
    );
    Expr::Apply(
        Box::new(ret),
        Box::new(partial),
        Box::new(b),
        Span::new(""),
    )
}

/// Constructs a unary-operator application: `Apply(ret, Identifier(op), a)`.
fn unary_op(op: &str, ret: Type, a: Expr) -> Expr {
    let a_ty = *a.type_();
    let op_ty =
        Type::Fn(Box::new(a_ty), Box::new(ret.clone()));
    let op_expr =
        Expr::Identifier(Box::new(op_ty), op.to_string());
    Expr::Apply(
        Box::new(ret),
        Box::new(op_expr),
        Box::new(a),
        Span::new(""),
    )
}

/// Returns `true` if `expr` is the boolean literal `true`.
fn is_true(expr: &Expr) -> bool {
    matches!(expr, Expr::Literal(_, Val::Bool(true)))
}

/// Returns `true` if `expr` is the boolean literal `false`.
fn is_false(expr: &Expr) -> bool {
    matches!(expr, Expr::Literal(_, Val::Bool(false)))
}

/// Returns a column name for `expr` if it is a simple field reference.
fn expr_name(
    expr: &Expr,
    row_type: &[(String, Type)],
) -> Option<String> {
    if let Expr::Identifier(_, name) = expr {
        if row_type.iter().any(|(n, _)| n == name) {
            return Some(name.clone());
        }
    }
    None
}

/// Returns `true` if `exprs` is the identity projection for `row_type`:
/// each expression is `Identifier(_, col_name)` matching the column at
/// the same ordinal.
fn is_identity_project(
    exprs: &[Expr],
    row_type: &[(String, Type)],
) -> bool {
    if exprs.len() != row_type.len() {
        return false;
    }
    exprs.iter().zip(row_type.iter()).all(|(e, (name, _))| {
        matches!(e, Expr::Identifier(_, n) if n == name)
    })
}

/// Infers a [`Type`] from a [`Val`].
fn val_type(v: &Val) -> Type {
    match v {
        Val::Bool(_) => bool_type(),
        Val::Int(_) => int_type(),
        Val::Real(_) => {
            Type::Primitive(PrimitiveType::Real)
        }
        Val::String(_) => string_type(),
        _ => string_type(), // safe default
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
        let plan = b.build();
        assert_plan!(
            plan,
            "LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_scan_qualified_table() {
        let mut b = builder();
        b.scan(&["scott", "DEPT"]);
        let plan = b.build();
        assert_plan!(
            plan,
            "LogicalTableScan(table=[[scott, DEPT]])"
        );
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
        let plan = b.build();
        assert_plan!(
            plan,
            "LogicalValues(tuples=[[]])"
        );
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
        let plan = b.build();
        assert_plan!(
            plan,
            "LogicalValues(tuples=[[{ 1, 'x' }, { 2, 'y' }]])"
        );
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
        let plan = b.build();
        // simplification: Filter(true) is eliminated
        assert_plan!(
            plan,
            "LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_scan_filter_trivially_false() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let cond = b.literal_bool(false);
        b.filter(cond);
        let plan = b.build();
        // simplification: Filter(false) → empty Values
        assert_plan!(plan, "LogicalValues(tuples=[[]])");
    }

    #[test]
    fn test_scan_filter_equals() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let lhs = b.field("DEPTNO");
        let rhs = b.literal_int(20);
        let cond = b.equals(lhs, rhs);
        b.filter(cond);
        let plan = b.build();
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
        let lhs = b.field("SAL");
        let rhs = b.literal_int(1000);
        let cond = b.gt(lhs, rhs);
        b.filter(cond);
        let plan = b.build();
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
        let exprs = vec![b.field("EMPNO"), b.field("ENAME")];
        b.project(exprs);
        let plan = b.build();
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
        let exprs: Vec<Expr> = (0..8)
            .map(|i| b.field_ordinal(i))
            .collect();
        b.project(exprs);
        let plan = b.build();
        // Simplification: identity project is removed.
        assert_plan!(
            plan,
            "LogicalTableScan(table=[[scott, EMP]])"
        );
    }

    #[test]
    fn test_project_named() {
        let mut b = builder();
        b.scan(&["scott", "EMP"]);
        let exprs = vec![b.field("EMPNO"), b.field("SAL")];
        let names =
            vec!["employee_no".to_string(), "salary".to_string()];
        b.project_named(exprs, names);
        let plan = b.build();
        assert_plan!(
            plan,
            "LogicalProject(employee_no=[$0], salary=[$5])\n  \
             LogicalTableScan(table=[[scott, EMP]])"
        );
    }
}
