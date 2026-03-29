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

//! Plan display in Apache Calcite's explain format.
//!
//! The entry point is [`explain`], which converts a [`Rel`] tree to a
//! human-readable, indented string matching Calcite's `RelNode.explain`
//! output. This format is used by `assert_plan!` in tests.
//!
//! Scalar expressions are printed in Calcite's prefix notation:
//! `>($5, 1000)`, `AND($0, $1)`. Field references are printed as `$N`
//! where N is the zero-based ordinal in the concatenated input row type.

use crate::compile::core::Expr;
use crate::compile::types::Type;
use crate::eval::val::Val;
use crate::rel::{
    AggCall, AggFunction, Direction, FieldCollation, JoinType, NullDirection,
    Rel,
};
use std::fmt::{self, Write as FmtWrite};

// -----------------------------------------------------------------------
// Public API
// -----------------------------------------------------------------------

/// Returns a Calcite-style explain string for `rel`.
///
/// Each node is on its own line. Child nodes are indented by 2 spaces
/// relative to their parent.
///
/// # Example
/// ```text
/// LogicalFilter(condition=[>($5, 1000)])
///   LogicalTableScan(table=[[scott, EMP]])
/// ```
pub fn explain(rel: &Rel) -> String {
    let mut buf = String::new();
    write_rel(&mut buf, rel, 0).expect("write to String cannot fail");
    buf
}

// -----------------------------------------------------------------------
// Internal writer
// -----------------------------------------------------------------------

/// Writes one `Rel` node and its children at the given `indent` level.
fn write_rel(f: &mut String, rel: &Rel, indent: usize) -> fmt::Result {
    let pad = "  ".repeat(indent);
    match rel {
        // lint: sort until '^$' where '##Rel::'
        Rel::Aggregate {
            input,
            group_set,
            group_sets,
            agg_calls,
            ..
        } => {
            write!(f, "{}LogicalAggregate(group=[{{", pad)?;
            for (i, g) in group_set.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", g)?;
            }
            write!(f, "}}]")?;
            // Show groups=[...] only when there are multiple grouping sets.
            if group_sets.len() > 1 {
                write!(f, ", groups=[[")?;
                for (si, set) in group_sets.iter().enumerate() {
                    if si > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{{")?;
                    for (gi, g) in set.iter().enumerate() {
                        if gi > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", g)?;
                    }
                    write!(f, "}}")?;
                }
                write!(f, "]]")?;
            }
            for agg in agg_calls {
                write!(f, ", ")?;
                write_agg_call(f, agg, input.row_type())?;
            }
            writeln!(f, ")")?;
            write_rel(f, input, indent + 1)
        }
        Rel::Correlate {
            left,
            right,
            correlation_id,
            join_type,
            required_columns,
            ..
        } => {
            write!(
                f,
                "{}LogicalCorrelate(correlation=[{}],",
                pad, correlation_id
            )?;
            write!(
                f,
                " joinType=[{}], requiredColumns=[{{",
                join_type_str(*join_type)
            )?;
            for (i, col) in required_columns.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", col)?;
            }
            writeln!(f, "}}])")?;
            write_rel(f, left, indent + 1)?;
            write_rel(f, right, indent + 1)
        }
        Rel::Filter { input, condition } => {
            write!(f, "{}LogicalFilter(condition=[", pad)?;
            write_expr(f, condition, &[input.row_type()])?;
            writeln!(f, "])")?;
            write_rel(f, input, indent + 1)
        }
        Rel::Intersect { inputs, all, .. } => {
            writeln!(f, "{}LogicalIntersect(all=[{}])", pad, all)?;
            for input in inputs {
                write_rel(f, input, indent + 1)?;
            }
            Ok(())
        }
        Rel::Join {
            left,
            right,
            join_type,
            condition,
            ..
        } => {
            let left_rt = left.row_type();
            let right_rt = right.row_type();
            write!(f, "{}LogicalJoin(condition=[", pad)?;
            write_expr(f, condition, &[left_rt, right_rt])?;
            writeln!(f, "], joinType=[{}])", join_type_str(*join_type))?;
            write_rel(f, left, indent + 1)?;
            write_rel(f, right, indent + 1)
        }
        Rel::Minus { inputs, all, .. } => {
            writeln!(f, "{}LogicalMinus(all=[{}])", pad, all)?;
            for input in inputs {
                write_rel(f, input, indent + 1)?;
            }
            Ok(())
        }
        Rel::Project {
            input,
            exprs,
            row_type,
        } => {
            write!(f, "{}LogicalProject(", pad)?;
            for (i, (col_name, _)) in row_type.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}=[", col_name)?;
                write_expr(f, &exprs[i], &[input.row_type()])?;
                write!(f, "]")?;
            }
            writeln!(f, ")")?;
            write_rel(f, input, indent + 1)
        }
        Rel::RepeatUnion {
            seed,
            iterative,
            all,
            iteration_limit,
            ..
        } => {
            write!(f, "{}LogicalRepeatUnion(all=[{}]", pad, all)?;
            if let Some(limit) = iteration_limit {
                write!(f, ", iterationLimit=[{}]", limit)?;
            }
            writeln!(f, ")")?;
            write_rel(f, seed, indent + 1)?;
            write_rel(f, iterative, indent + 1)
        }
        Rel::Sort {
            input,
            collation,
            offset,
            fetch,
        } => {
            write!(f, "{}LogicalSort(", pad)?;
            let mut first = true;
            for (i, key) in collation.iter().enumerate() {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                write!(f, "sort{}=[${}]", i, key.index)?;
                write!(f, ", dir{}=[{}]", i, collation_dir_str(key))?;
            }
            if let Some(off) = offset {
                if !first {
                    write!(f, ", ")?;
                }
                first = false;
                write!(f, "offset=[{}]", off)?;
            }
            if let Some(fetch) = fetch {
                if !first {
                    write!(f, ", ")?;
                }
                write!(f, "fetch=[{}]", fetch)?;
            }
            writeln!(f, ")")?;
            write_rel(f, input, indent + 1)
        }
        Rel::TableScan { table_name, .. } => {
            write!(f, "{}LogicalTableScan(table=[[", pad)?;
            for (i, part) in table_name.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", part)?;
            }
            writeln!(f, "]])")
        }
        Rel::Union { inputs, all, .. } => {
            writeln!(f, "{}LogicalUnion(all=[{}])", pad, all)?;
            for input in inputs {
                write_rel(f, input, indent + 1)?;
            }
            Ok(())
        }
        Rel::Values { row_type, rows } => {
            write!(f, "{}LogicalValues(tuples=[[", pad)?;
            for (r, row) in rows.iter().enumerate() {
                if r > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{{ ")?;
                for (c, expr) in row.iter().enumerate() {
                    if c > 0 {
                        write!(f, ", ")?;
                    }
                    write_expr(f, expr, &[row_type])?;
                }
                write!(f, " }}")?;
            }
            writeln!(f, "]])")
        }
    }
}

// -----------------------------------------------------------------------
// Expression display in relational context
// -----------------------------------------------------------------------

/// Writes `expr` in Calcite's prefix notation.
///
/// `inputs` is a slice of input row types (one per input, left to right).
/// Field references are printed as `$N` where N is the zero-based ordinal
/// in the concatenated input row types.
///
/// Recognised patterns:
/// * Leaf `Identifier(name)` — field reference → `$N`
/// * `Literal(val)` — constant → `1000`, `'hello'`, `true`, `null`
/// * Binary op: `Apply(Apply(Identifier(op), a), b)` → `op(a, b)`
/// * Unary op:  `Apply(Identifier(op), a)`           → `op(a)`
pub(crate) fn write_expr(
    f: &mut String,
    expr: &Expr,
    inputs: &[&[(String, Type)]],
) -> fmt::Result {
    match expr {
        // lint: sort until '#}' where '##[A-Z]'
        Expr::Apply(ret_ty, func, arg, _) => {
            // Try to match CAST: Apply(target_type, Identifier("CAST"), a)
            if let Expr::Identifier(_, op) = func.as_ref()
                && op == "CAST"
            {
                write!(f, "CAST(")?;
                write_expr(f, arg, inputs)?;
                return write!(f, "):{}", type_to_sql(ret_ty));
            }
            // Subquery unary operators wrapping a relational subquery.
            // Internal Morel names are mapped to Calcite-compatible display
            // names: "only" → "$SCALAR_QUERY", "nonEmpty" → "EXISTS".
            if let Expr::Identifier(_, op) = func.as_ref()
                && let Expr::Rel(rel) = arg.as_ref()
            {
                let disp = match op.as_str() {
                    "only" => Some("$SCALAR_QUERY"),
                    "nonEmpty" => Some("EXISTS"),
                    "ARRAY" | "MAP" | "MULTISET" | "UNIQUE" => {
                        Some(op.as_str())
                    }
                    _ => None,
                };
                if let Some(disp) = disp {
                    write!(f, "{}(", disp)?;
                    write_subquery_plan(f, rel)?;
                    return write!(f, ")");
                }
            }
            // IN subquery: Apply(Apply(Identifier("IN"), col), Rel(rel))
            if let Expr::Apply(_, inner_f, col, _) = func.as_ref()
                && let Expr::Identifier(_, op) = inner_f.as_ref()
                && op == "IN"
                && let Expr::Rel(rel) = arg.as_ref()
            {
                write!(f, "IN(")?;
                write_expr(f, col, inputs)?;
                write!(f, ", ")?;
                write_subquery_plan(f, rel)?;
                return write!(f, ")");
            }
            // SOME(op)/ALL(op) subquery.
            if let Expr::Apply(_, inner_f, col, _) = func.as_ref()
                && let Expr::Identifier(_, op_name) = inner_f.as_ref()
                && (op_name.starts_with("SOME(") || op_name.starts_with("ALL("))
                && let Expr::Rel(rel) = arg.as_ref()
            {
                write!(f, "{}(", op_name)?;
                write_expr(f, col, inputs)?;
                write!(f, ", ")?;
                write_subquery_plan(f, rel)?;
                return write!(f, ")");
            }
            // CASE(cond, then_val, else_val):
            // Apply(Apply(Apply(Identifier("CASE"), cond), then_val), else_val)
            if let Expr::Apply(_, inner_f, then_val, _) = func.as_ref()
                && let Expr::Apply(_, case_id, cond, _) = inner_f.as_ref()
                && let Expr::Identifier(_, op) = case_id.as_ref()
                && op == "CASE"
            {
                write!(f, "CASE(")?;
                write_expr(f, cond, inputs)?;
                write!(f, ", ")?;
                write_expr(f, then_val, inputs)?;
                write!(f, ", ")?;
                write_expr(f, arg, inputs)?;
                return write!(f, ")");
            }
            // Try to match binary op: Apply(Apply(Identifier(op),a),b)
            if let Expr::Apply(_, inner_f, left, _) = func.as_ref()
                && let Expr::Identifier(_, op) = inner_f.as_ref()
                && let Some(disp) = binary_op_display(op)
            {
                write!(f, "{}(", disp)?;
                write_expr(f, left, inputs)?;
                write!(f, ", ")?;
                write_expr(f, arg, inputs)?;
                return write!(f, ")");
            }
            // Try to match unary op: Apply(Identifier(op), a)
            if let Expr::Identifier(_, op) = func.as_ref()
                && let Some(disp) = unary_op_display(op)
            {
                write_expr_unary(f, disp, arg, inputs)?;
                return Ok(());
            }
            // Generic function application.
            write_expr(f, func, inputs)?;
            write!(f, "(")?;
            write_expr(f, arg, inputs)?;
            write!(f, ")")
        }
        Expr::Identifier(_, name) => {
            // Correlation variable references: "$cor0::FIELD" → "$cor0.FIELD"
            if let Some(sep) = name.find("::") {
                let cor_part = &name[..sep];
                let field_part = &name[sep + 2..];
                if cor_part.starts_with("$cor") {
                    return write!(f, "{}.{}", cor_part, field_part);
                }
            }
            // Resolve field name to a concatenated ordinal.
            let mut base = 0usize;
            for input in inputs {
                for (i, (col, _)) in input.iter().enumerate() {
                    if col == name {
                        return write!(f, "${}", base + i);
                    }
                }
                base += input.len();
            }
            // Not found in any input — emit as-is (e.g. an operator
            // name that appeared in a non-function position).
            write!(f, "{}", name)
        }
        Expr::Literal(_, val) => write_val(f, val),
        Expr::Rel(rel) => {
            // Relational subquery: $SCALAR_QUERY({<plan>})
            write!(f, "$SCALAR_QUERY(")?;
            write_subquery_plan(f, rel)?;
            write!(f, ")")
        }
        // Other Expr variants are not produced by RelBuilder; emit ?
        _ => write!(f, "?"),
    }
}

/// Writes the inner relation of a subquery as `{\n<plan>}`.
fn write_subquery_plan(f: &mut String, rel: &Rel) -> fmt::Result {
    writeln!(f, "{{")?;
    write_rel(f, rel, 0)?;
    write!(f, "}}")
}

/// Writes a [`Val`] as a SQL literal.
fn write_expr_unary(
    f: &mut String,
    disp: &str,
    arg: &Expr,
    inputs: &[&[(String, Type)]],
) -> fmt::Result {
    write!(f, "{}(", disp)?;
    write_expr(f, arg, inputs)?;
    write!(f, ")")
}

/// Returns the SQL type name for display in CAST expressions.
fn type_to_sql(ty: &Type) -> &'static str {
    use crate::compile::types::PrimitiveType;
    match ty {
        Type::Primitive(PrimitiveType::Bool) => "BOOLEAN",
        Type::Primitive(PrimitiveType::Int) => "INTEGER",
        Type::Primitive(PrimitiveType::Real) => "DOUBLE",
        Type::Primitive(PrimitiveType::String) => "VARCHAR",
        _ => "?",
    }
}

fn write_val(f: &mut String, val: &Val) -> fmt::Result {
    match val {
        // lint: sort until '#}' where '##[A-Z]'
        Val::Bool(b) => write!(f, "{}", b),
        Val::Char(c) => write!(f, "'{}'", c),
        Val::Int(i) => write!(f, "{}", i),
        Val::Real(r) => write!(f, "{}", r),
        Val::String(s) => write!(f, "'{}'", s),
        Val::Unit => write!(f, "null"),
        _ => write!(f, "{}", val),
    }
}

/// Returns the Calcite display name for a binary operator, or `None`.
fn binary_op_display(op: &str) -> Option<&'static str> {
    match op {
        // lint: sort until '#}' where '##"'
        "*" => Some("*"),
        "+" => Some("+"),
        "-" => Some("-"),
        "/" => Some("/"),
        "<" => Some("<"),
        "<=" => Some("<="),
        "<>" => Some("<>"),
        "=" => Some("="),
        ">" => Some(">"),
        ">=" => Some(">="),
        "ILIKE" => Some("ILIKE"),
        "IS DISTINCT FROM" => Some("IS DISTINCT FROM"),
        "IS NOT DISTINCT FROM" => Some("IS NOT DISTINCT FROM"),
        "LIKE" => Some("LIKE"),
        "NOT ILIKE" => Some("NOT ILIKE"),
        "NOT LIKE" => Some("NOT LIKE"),
        "NOT SIMILAR TO" => Some("NOT SIMILAR TO"),
        "SIMILAR TO" => Some("SIMILAR TO"),
        "andalso" => Some("AND"),
        "orelse" => Some("OR"),
        _ => None,
    }
}

/// Returns the Calcite display name for a unary operator, or `None`.
fn unary_op_display(op: &str) -> Option<&'static str> {
    match op {
        "is_not_null" => Some("IS NOT NULL"),
        "is_null" => Some("IS NULL"),
        "not" => Some("NOT"),
        _ => None,
    }
}

// -----------------------------------------------------------------------
// Aggregate-call display
// -----------------------------------------------------------------------

fn write_agg_call(
    f: &mut String,
    agg: &AggCall,
    input_row_type: &[(String, Type)],
) -> fmt::Result {
    // Output column name.
    let name = agg.name.as_deref().unwrap_or("?");
    write!(f, "{}=[", name)?;

    // Function name.
    let fn_name = match agg.agg {
        // lint: sort until '#}' where '##[A-Z]'
        AggFunction::Avg => "AVG",
        AggFunction::Count | AggFunction::CountStar => "COUNT",
        AggFunction::Grouping => "GROUPING",
        AggFunction::GroupingId => "GROUPING_ID",
        AggFunction::Max => "MAX",
        AggFunction::Min => "MIN",
        AggFunction::Sum => "SUM",
    };
    write!(f, "{}(", fn_name)?;

    if agg.agg == AggFunction::CountStar {
        // COUNT(*) — star instead of an argument.
        write!(f, "*")?;
    } else {
        if agg.distinct {
            write!(f, "DISTINCT ")?;
        }
        for (i, &arg) in agg.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "${}", arg)?;
        }
    }
    write!(f, ")")?;
    if !agg.within_distinct.is_empty() {
        write!(f, " WITHIN DISTINCT (")?;
        for (i, &ord) in agg.within_distinct.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "${}", ord)?;
        }
        write!(f, ")")?;
    }
    if let Some(filter) = &agg.filter {
        write!(f, " FILTER [")?;
        write_expr(f, filter, &[input_row_type])?;
        write!(f, "]")?;
    }
    write!(f, "]")
}

// -----------------------------------------------------------------------
// Helpers
// -----------------------------------------------------------------------

fn join_type_str(jt: JoinType) -> &'static str {
    match jt {
        JoinType::Anti => "anti",
        JoinType::Full => "full",
        JoinType::Inner => "inner",
        JoinType::Left => "left",
        JoinType::Right => "right",
        JoinType::Semi => "semi",
    }
}

fn collation_dir_str(key: &FieldCollation) -> String {
    let dir = match key.direction {
        Direction::Ascending => "ASC",
        Direction::Descending => "DESC",
    };
    let nulls = match (key.direction, key.null_direction) {
        (_, NullDirection::First) => "-nullsFirst",
        (_, NullDirection::Last) => "-nullsLast",
        (_, NullDirection::Unspecified) => "",
    };
    format!("{}{}", dir, nulls)
}

// -----------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::types::PrimitiveType;
    use crate::eval::val::Val;
    use crate::rel::schema::Schema;
    use crate::rel::schema::scott_schema;
    use crate::rel::{Direction, FieldCollation, NullDirection};

    fn int() -> Type {
        Type::Primitive(PrimitiveType::Int)
    }
    fn str_() -> Type {
        Type::Primitive(PrimitiveType::String)
    }
    fn bool_() -> Type {
        Type::Primitive(PrimitiveType::Bool)
    }
    fn lit_int(i: i32) -> Expr {
        Expr::Literal(Box::new(int()), Val::Int(i))
    }
    fn lit_bool(b: bool) -> Expr {
        Expr::Literal(Box::new(bool_()), Val::Bool(b))
    }

    fn emp_row_type() -> Vec<(String, Type)> {
        let s = scott_schema();
        let t = s.table(&["scott", "EMP"]).unwrap();
        t.columns.clone()
    }

    #[test]
    fn test_explain_table_scan() {
        let rel = Rel::TableScan {
            table_name: vec!["scott".into(), "EMP".into()],
            row_type: emp_row_type(),
        };
        assert_eq!(explain(&rel), "LogicalTableScan(table=[[scott, EMP]])\n");
    }

    #[test]
    fn test_explain_filter() {
        let scan = Rel::TableScan {
            table_name: vec!["scott".into(), "EMP".into()],
            row_type: emp_row_type(),
        };
        let rel = Rel::Filter {
            condition: lit_bool(true),
            input: Box::new(scan),
        };
        assert_eq!(
            explain(&rel),
            "LogicalFilter(condition=[true])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n"
        );
    }

    #[test]
    fn test_explain_project() {
        let scan = Rel::TableScan {
            table_name: vec!["scott".into(), "EMP".into()],
            row_type: emp_row_type(),
        };
        let row_type =
            vec![("ENAME".to_string(), str_()), ("EMPNO".to_string(), int())];
        let rel = Rel::Project {
            exprs: vec![
                Expr::Identifier(Box::new(str_()), "ENAME".into()),
                Expr::Identifier(Box::new(int()), "EMPNO".into()),
            ],
            row_type,
            input: Box::new(scan),
        };
        assert_eq!(
            explain(&rel),
            "LogicalProject(ENAME=[$1], EMPNO=[$0])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n"
        );
    }

    #[test]
    fn test_explain_empty_values() {
        let rel = Rel::Values {
            row_type: vec![("X".to_string(), int())],
            rows: vec![],
        };
        assert_eq!(explain(&rel), "LogicalValues(tuples=[[]])\n");
    }

    #[test]
    fn test_explain_values() {
        let rel = Rel::Values {
            row_type: vec![("A".to_string(), int()), ("B".to_string(), str_())],
            rows: vec![vec![
                lit_int(1),
                Expr::Literal(Box::new(str_()), Val::String("hello".into())),
            ]],
        };
        assert_eq!(explain(&rel), "LogicalValues(tuples=[[{ 1, 'hello' }]])\n");
    }

    #[test]
    fn test_explain_sort() {
        let scan = Rel::TableScan {
            table_name: vec!["scott".into(), "EMP".into()],
            row_type: emp_row_type(),
        };
        let rel = Rel::Sort {
            collation: vec![FieldCollation {
                index: 5,
                direction: Direction::Descending,
                null_direction: NullDirection::Last,
            }],
            offset: None,
            fetch: None,
            input: Box::new(scan),
        };
        assert_eq!(
            explain(&rel),
            "LogicalSort(sort0=[$5], dir0=[DESC-nullsLast])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n"
        );
    }

    #[test]
    fn test_explain_limit() {
        let scan = Rel::TableScan {
            table_name: vec!["scott".into(), "EMP".into()],
            row_type: emp_row_type(),
        };
        let rel = Rel::Sort {
            collation: vec![],
            offset: None,
            fetch: Some(10),
            input: Box::new(scan),
        };
        assert_eq!(
            explain(&rel),
            "LogicalSort(fetch=[10])\n  \
             LogicalTableScan(table=[[scott, EMP]])\n"
        );
    }

    #[test]
    fn test_explain_union() {
        let rt = vec![("X".to_string(), int())];
        let v1 = Rel::Values {
            row_type: rt.clone(),
            rows: vec![vec![lit_int(1)]],
        };
        let v2 = Rel::Values {
            row_type: rt.clone(),
            rows: vec![vec![lit_int(2)]],
        };
        let rel = Rel::Union {
            inputs: vec![v1, v2],
            all: true,
            row_type: rt,
        };
        assert_eq!(
            explain(&rel),
            "LogicalUnion(all=[true])\n  \
             LogicalValues(tuples=[[{ 1 }]])\n  \
             LogicalValues(tuples=[[{ 2 }]])\n"
        );
    }

    #[test]
    fn test_rel_type() {
        let rel = Rel::TableScan {
            table_name: vec!["scott".into(), "EMP".into()],
            row_type: emp_row_type(),
        };
        match rel.type_() {
            Type::Bag(_) => {}
            other => panic!("expected Bag, got {:?}", other),
        }
    }

    #[test]
    fn test_rel_inputs_leaf() {
        let rel = Rel::TableScan {
            table_name: vec!["scott".into(), "EMP".into()],
            row_type: emp_row_type(),
        };
        assert!(rel.inputs().is_empty());
    }

    #[test]
    fn test_rel_inputs_unary() {
        let scan = Rel::TableScan {
            table_name: vec!["scott".into(), "EMP".into()],
            row_type: emp_row_type(),
        };
        let rel = Rel::Filter {
            condition: lit_bool(true),
            input: Box::new(scan),
        };
        assert_eq!(rel.inputs().len(), 1);
    }
}
