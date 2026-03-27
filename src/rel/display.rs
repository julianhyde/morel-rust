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
            for agg in agg_calls {
                write!(f, ", ")?;
                write_agg_call(f, agg, rel.row_type())?;
            }
            writeln!(f, ")")?;
            write_rel(f, input, indent + 1)
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
        Expr::Apply(_, func, arg, _) => {
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
        // Other Expr variants are not produced by RelBuilder; emit ?
        _ => write!(f, "?"),
    }
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
        "LIKE" => Some("LIKE"),
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
    row_type: &[(String, Type)],
) -> fmt::Result {
    // Output column name.
    let name = agg.name.as_deref().unwrap_or("?");
    write!(f, "{}=[", name)?;

    // Function name.
    let fn_name = match agg.agg {
        // lint: sort until '#}' where '##[A-Z]'
        AggFunction::Avg => "AVG",
        AggFunction::Count | AggFunction::CountStar => "COUNT",
        AggFunction::Max => "MAX",
        AggFunction::Min => "MIN",
        AggFunction::Sum => "SUM",
    };
    write!(f, "{}(", fn_name)?;
    let _ = row_type; // args are input ordinals, not output

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
    write!(f, ")]")
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
