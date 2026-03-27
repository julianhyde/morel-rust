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

//! Port of Calcite's `RelBuilderTest` for the Morel `RelBuilder`.
//!
//! Each test is named after its Calcite counterpart (camelCase → snake_case).
//! Expected plan strings are Calcite-style indented text produced by
//! [`morel::rel::display::explain`].

use indoc::indoc;
use morel::eval::val::Val;
use morel::rel::builder::{BuilderConfig, RelBuilder, RelError, SortKey};
use morel::rel::display::explain;
use morel::rel::schema::scott_schema;
use morel::rel::{Direction, JoinType, NullDirection, bool_type, int_type};
use std::sync::Arc;

// -----------------------------------------------------------------------
// Helper
// -----------------------------------------------------------------------

fn builder() -> RelBuilder {
    RelBuilder::new(Arc::new(scott_schema()))
}

macro_rules! assert_plan {
    ($rel:expr, $expected:expr) => {
        assert_eq!(explain(&$rel).trim(), $expected.trim())
    };
}

// -----------------------------------------------------------------------
// Scan
// -----------------------------------------------------------------------

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

// -----------------------------------------------------------------------
// Filter
// -----------------------------------------------------------------------

#[test]
fn test_scan_filter_true() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let cond = b.literal_bool(true);
    b.filter(cond);
    let plan = b.build().unwrap();
    // Filter(true) is simplified away.
    assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
}

#[test]
fn test_scan_filter_trivially_false() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let cond = b.literal_bool(false);
    b.filter(cond);
    let plan = b.build().unwrap();
    // Filter(false) becomes empty Values.
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
        indoc! {"
            LogicalFilter(condition=[=($7, 20)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
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
        indoc! {"
            LogicalFilter(condition=[>($5, 1000)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

#[test]
fn test_scan_filter_or() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let lhs = b.gt(b.field("SAL").unwrap(), b.literal_int(1000));
    let rhs = b.equals(b.field("DEPTNO").unwrap(), b.literal_int(20));
    let cond = b.or(lhs, rhs);
    b.filter(cond);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[OR(>($5, 1000), =($7, 20))])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

// -----------------------------------------------------------------------
// Project
// -----------------------------------------------------------------------

#[test]
fn test_project() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let exprs = vec![b.field("EMPNO").unwrap(), b.field("ENAME").unwrap()];
    b.project(exprs);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(EMPNO=[$0], ENAME=[$1])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

#[test]
fn test_project_identity() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    // Identity project over all 8 columns — should be eliminated.
    let exprs: Vec<_> = (0..8).map(|i| b.field_ordinal(i).unwrap()).collect();
    b.project(exprs);
    let plan = b.build().unwrap();
    assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
}

#[test]
fn test_project_identity_with_fields_rename() {
    // A project that keeps all columns but renames one is NOT
    // an identity project; it must be preserved.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let exprs: Vec<_> = (0..8).map(|i| b.field_ordinal(i).unwrap()).collect();
    let names: Vec<String> = vec![
        "EMPNO".into(),
        "NAME".into(), // renamed from ENAME
        "JOB".into(),
        "MGR".into(),
        "HIREDATE".into(),
        "SAL".into(),
        "COMM".into(),
        "DEPTNO".into(),
    ];
    b.project_named(exprs, names);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(EMPNO=[$0], NAME=[$1], JOB=[$2], MGR=[$3], \
                           HIREDATE=[$4], SAL=[$5], COMM=[$6], DEPTNO=[$7])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

// -----------------------------------------------------------------------
// Values / Empty
// -----------------------------------------------------------------------

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

#[test]
fn test_empty() {
    let mut b = builder();
    let row_type = vec![
        ("A".to_string(), int_type()),
        ("B".to_string(), bool_type()),
    ];
    b.empty(row_type);
    let plan = b.build().unwrap();
    assert_plan!(plan, "LogicalValues(tuples=[[]])");
}

// -----------------------------------------------------------------------
// Sort / Limit
// -----------------------------------------------------------------------

#[test]
fn test_sort() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let key = SortKey {
        expr: b.field("SAL").unwrap(),
        direction: Direction::Ascending,
        null_direction: NullDirection::Unspecified,
    };
    b.sort(&[key]);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[ASC])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

#[test]
fn test_trivial_sort() {
    // Empty collation → no Sort node.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.sort(&[]);
    let plan = b.build().unwrap();
    assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
}

#[test]
fn test_sort_duplicate() {
    // Duplicate key: second reference is dropped.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
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
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[ASC])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

#[test]
fn test_sort_by_expression() {
    // Sort by NULLS LAST.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let key = b.nulls_last(b.field("SAL").unwrap());
    b.sort(&[key]);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[ASC-nullsLast])
              LogicalTableScan(table=[[scott, EMP]])
        "}
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
        indoc! {"
            LogicalSort(fetch=[10])
              LogicalTableScan(table=[[scott, EMP]])
        "}
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
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[DESC], offset=[5], fetch=[3])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

#[test]
fn test_sort_limit0() {
    // fetch=0 → empty Values.
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
        indoc! {"
            LogicalSort(offset=[10], fetch=[5])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

// -----------------------------------------------------------------------
// Rename
// -----------------------------------------------------------------------

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
        indoc! {"
            LogicalProject(department_no=[$0], \
                           department_name=[$1], location=[$2])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
}

#[test]
fn test_rename_values() {
    // rename() applied to a Values node.
    let mut b = builder();
    b.values(
        &["A", "B"],
        vec![vec![Val::Int(1), Val::String("x".into())]],
    );
    b.rename(vec!["col1".to_string(), "col2".to_string()]);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(col1=[$0], col2=[$1])
              LogicalValues(tuples=[[{ 1, 'x' }]])
        "}
    );
}

#[test]
fn test_asc_with_default_null_direction() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let key = SortKey {
        expr: b.field("SAL").unwrap(),
        direction: Direction::Ascending,
        null_direction: NullDirection::Unspecified,
    };
    b.sort(&[key]);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[ASC])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

#[test]
fn test_desc_with_default_null_direction() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let key = b.desc(b.field("SAL").unwrap());
    b.sort(&[key]);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[DESC])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

// -----------------------------------------------------------------------
// Aggregate
// -----------------------------------------------------------------------

#[test]
fn test_aggregate() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk = b.group_key(vec![b.field("DEPTNO").unwrap()]);
    let aggs = vec![b.count_star().as_("C")];
    b.aggregate(&gk, aggs);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{7}], C=[COUNT(*)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

#[test]
fn test_aggregate2() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk =
        b.group_key(vec![b.field("DEPTNO").unwrap(), b.field("JOB").unwrap()]);
    let aggs = vec![b.count_star().as_("C"), b.sum("SAL").as_("TOTAL_SAL")];
    b.aggregate(&gk, aggs);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{7, 2}], C=[COUNT(*)], TOTAL_SAL=[SUM($5)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

#[test]
fn test_aggregate5() {
    // aggregate with no group key → one output row.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk = b.group_key(vec![]);
    let aggs = vec![b.count_star().as_("C"), b.sum("SAL").as_("S")];
    b.aggregate(&gk, aggs);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{}], C=[COUNT(*)], S=[SUM($5)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

#[test]
fn test_aggregate_filter() {
    // aggregate with a FILTER clause (simulated by pre-filtering).
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let cond = b.gt(b.field("SAL").unwrap(), b.literal_int(1000));
    b.filter(cond);
    let gk = b.group_key(vec![b.field("DEPTNO").unwrap()]);
    let aggs = vec![b.count_star().as_("C")];
    b.aggregate(&gk, aggs);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{7}], C=[COUNT(*)])
              LogicalFilter(condition=[>($5, 1000)])
                LogicalTableScan(table=[[scott, EMP]])
        "}
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
        indoc! {"
            LogicalAggregate(group=[{0, 1, 2}])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
}

// -----------------------------------------------------------------------
// Join
// -----------------------------------------------------------------------

#[test]
fn test_project_join() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.scan(&["scott", "DEPT"]);
    let lhs = b.field2(1, "DEPTNO").unwrap();
    let rhs = b.field2(0, "DEPTNO").unwrap();
    let cond = b.equals(lhs, rhs);
    b.join(JoinType::Inner, cond);
    let exprs = vec![b.field("ENAME").unwrap(), b.field("DNAME").unwrap()];
    b.project(exprs);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(ENAME=[$1], DNAME=[$9])
              LogicalJoin(condition=[=($7, $8)], joinType=[inner])
                LogicalTableScan(table=[[scott, EMP]])
                LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
}

#[test]
fn test_alias() {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.as_("e");
    b.scan(&["scott", "DEPT"]);
    b.as_("d");
    let lhs = b.field2(1, "DEPTNO").unwrap();
    let rhs = b.field2(0, "DEPTNO").unwrap();
    let cond = b.equals(lhs, rhs);
    b.join(JoinType::Inner, cond);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalJoin(condition=[=($7, $8)], joinType=[inner])
              LogicalTableScan(table=[[scott, EMP]])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
}

// -----------------------------------------------------------------------
// Set operations
// -----------------------------------------------------------------------

#[test]
fn test_union_project_values() {
    let mut b = builder();
    b.values(&["X", "Y"], vec![vec![Val::Int(1), Val::Int(2)]]);
    b.values(&["X", "Y"], vec![vec![Val::Int(3), Val::Int(4)]]);
    b.union(false);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalUnion(all=[false])
              LogicalValues(tuples=[[{ 1, 2 }]])
              LogicalValues(tuples=[[{ 3, 4 }]])
        "}
    );
}

#[test]
fn test_union_alias() {
    // union with aliased inputs.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.scan(&["scott", "EMP"]);
    b.union(true);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalUnion(all=[true])
              LogicalTableScan(table=[[scott, EMP]])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

// -----------------------------------------------------------------------
// Config (simplification flags)
// -----------------------------------------------------------------------

#[test]
fn test_filter_no_simplify() {
    // With simplify_filter_true=false, Filter(true) is NOT eliminated.
    let config = BuilderConfig {
        simplify_filter_true: false,
        ..Default::default()
    };
    let mut b = RelBuilder::with_config(Arc::new(scott_schema()), config);
    b.scan(&["scott", "EMP"]);
    let cond = b.literal_bool(true);
    b.filter(cond);
    let plan = b.build().unwrap();
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[true])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
}

// -----------------------------------------------------------------------
// Error handling (Task 9)
// -----------------------------------------------------------------------

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
    let gk = b.group_key(vec![b.field("NOSUCHCOL").unwrap_or_else(|_| {
        // Supply a syntactically valid but semantically invalid expr.
        morel::compile::core::Expr::Identifier(
            Box::new(int_type()),
            "NOSUCHCOL".to_string(),
        )
    })]);
    b.aggregate(&gk, vec![]);
    assert!(matches!(b.build(), Err(RelError::InvalidGroupKey(_))));
}
