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
fn test_scan() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let plan = b.build()?;
    assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
    Ok(())
}

#[test]
fn test_scan_qualified_table() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "DEPT"]);
    let plan = b.build()?;
    assert_plan!(plan, "LogicalTableScan(table=[[scott, DEPT]])");
    Ok(())
}

// -----------------------------------------------------------------------
// Filter
// -----------------------------------------------------------------------

#[test]
fn test_scan_filter_true() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let cond = b.literal_bool(true);
    b.filter(cond);
    let plan = b.build()?;
    // Filter(true) is simplified away.
    assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
    Ok(())
}

#[test]
fn test_scan_filter_trivially_false() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let cond = b.literal_bool(false);
    b.filter(cond);
    let plan = b.build()?;
    // Filter(false) becomes empty Values.
    assert_plan!(plan, "LogicalValues(tuples=[[]])");
    Ok(())
}

#[test]
fn test_scan_filter_equals() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let lhs = b.field("DEPTNO")?;
    let rhs = b.literal_int(20);
    let cond = b.equals(lhs, rhs);
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[=($7, 20)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_scan_filter_greater_than() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let lhs = b.field("SAL")?;
    let rhs = b.literal_int(1000);
    let cond = b.gt(lhs, rhs);
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[>($5, 1000)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_scan_filter_or() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let lhs = b.gt(b.field("SAL")?, b.literal_int(1000));
    let rhs = b.equals(b.field("DEPTNO")?, b.literal_int(20));
    let cond = b.or(lhs, rhs);
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[OR(>($5, 1000), =($7, 20))])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Project
// -----------------------------------------------------------------------

#[test]
fn test_project() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let exprs = vec![b.field("EMPNO")?, b.field("ENAME")?];
    b.project(exprs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(EMPNO=[$0], ENAME=[$1])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_project_identity() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    // Identity project over all 8 columns — should be eliminated.
    let exprs: Vec<_> = (0..8)
        .map(|i| b.field_ordinal(i))
        .collect::<Result<Vec<_>, _>>()?;
    b.project(exprs);
    let plan = b.build()?;
    assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
    Ok(())
}

#[test]
fn test_project_identity_with_fields_rename() -> Result<(), RelError> {
    // A project that keeps all columns but renames one is NOT
    // an identity project; it must be preserved.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let exprs: Vec<_> = (0..8)
        .map(|i| b.field_ordinal(i))
        .collect::<Result<Vec<_>, _>>()?;
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
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(EMPNO=[$0], NAME=[$1], JOB=[$2], MGR=[$3], \
                           HIREDATE=[$4], SAL=[$5], COMM=[$6], DEPTNO=[$7])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Project variants (Task 14)
// -----------------------------------------------------------------------

#[test]
fn test_project2() -> Result<(), RelError> {
    // Project with a computed expression: EMPNO and EMPNO+1.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let empno = b.field("EMPNO")?;
    let empno2 = b.field("EMPNO")?;
    let one = b.literal_int(1);
    let exprs = vec![empno, b.plus(empno2, one)];
    b.project(exprs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(EMPNO=[$0], $1=[+($0, 1)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_project_leading_edge() -> Result<(), RelError> {
    // Project the first 3 columns of EMP (a leading subset).
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let exprs = vec![b.field("EMPNO")?, b.field("ENAME")?, b.field("JOB")?];
    b.project(exprs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(EMPNO=[$0], ENAME=[$1], JOB=[$2])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_project_mapping() -> Result<(), RelError> {
    // Project reordering two columns: [ENAME, EMPNO].
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let exprs = vec![b.field("ENAME")?, b.field("EMPNO")?];
    b.project(exprs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(ENAME=[$1], EMPNO=[$0])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_permute() -> Result<(), RelError> {
    // Full permutation of DEPT columns: LOC, DNAME, DEPTNO.
    // DEPT: (DEPTNO=$0, DNAME=$1, LOC=$2)
    let mut b = builder();
    b.scan(&["scott", "DEPT"]);
    let exprs = vec![b.field("LOC")?, b.field("DNAME")?, b.field("DEPTNO")?];
    b.project(exprs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(LOC=[$2], DNAME=[$1], DEPTNO=[$0])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

#[test]
fn test_project_bloat() -> Result<(), RelError> {
    // project-over-project where outer has a computed expression
    // → merge is suppressed; two Project nodes remain.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.project(vec![b.field("EMPNO")?, b.field("ENAME")?]);
    let empno = b.field("EMPNO")?;
    let one = b.literal_int(1);
    let exprs = vec![b.plus(empno, one), b.field("ENAME")?];
    b.project(exprs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject($0=[+($0, 1)], ENAME=[$1])
              LogicalProject(EMPNO=[$0], ENAME=[$1])
                LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_project_identity_with_fields_rename_filter() -> Result<(), RelError> {
    // Rename one column, then filter, then project a subset.
    // The outer Project is not over another Project, so no merge.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.rename(vec![
        "EMPNO".into(),
        "NAME".into(), // ENAME → NAME
        "JOB".into(),
        "MGR".into(),
        "HIREDATE".into(),
        "SAL".into(),
        "COMM".into(),
        "DEPTNO".into(),
    ]);
    let cond = b.equals(b.field("JOB")?, b.literal_string("CLERK"));
    b.filter(cond);
    let exprs = vec![b.field("EMPNO")?, b.field("NAME")?];
    b.project(exprs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(EMPNO=[$0], NAME=[$1])
              LogicalFilter(condition=[=($2, 'CLERK')])
                LogicalProject(EMPNO=[$0], NAME=[$1], JOB=[$2], MGR=[$3], \
                               HIREDATE=[$4], SAL=[$5], COMM=[$6], DEPTNO=[$7])
                  LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Values / Empty
// -----------------------------------------------------------------------

#[test]
fn test_values() -> Result<(), RelError> {
    let mut b = builder();
    b.values(
        &["A", "B"],
        vec![
            vec![Val::Int(1), Val::String("x".into())],
            vec![Val::Int(2), Val::String("y".into())],
        ],
    );
    let plan = b.build()?;
    assert_plan!(plan, "LogicalValues(tuples=[[{ 1, 'x' }, { 2, 'y' }]])");
    Ok(())
}

#[test]
fn test_empty() -> Result<(), RelError> {
    let mut b = builder();
    let row_type = vec![
        ("A".to_string(), int_type()),
        ("B".to_string(), bool_type()),
    ];
    b.empty(row_type);
    let plan = b.build()?;
    assert_plan!(plan, "LogicalValues(tuples=[[]])");
    Ok(())
}

// -----------------------------------------------------------------------
// Sort / Limit
// -----------------------------------------------------------------------

#[test]
fn test_sort() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let key = SortKey {
        expr: b.field("SAL")?,
        direction: Direction::Ascending,
        null_direction: NullDirection::Unspecified,
    };
    b.sort(&[key]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[ASC])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_trivial_sort() -> Result<(), RelError> {
    // Empty collation → no Sort node.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.sort(&[]);
    let plan = b.build()?;
    assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
    Ok(())
}

#[test]
fn test_sort_duplicate() -> Result<(), RelError> {
    // Duplicate key: second reference is dropped.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let k1 = SortKey {
        expr: b.field("SAL")?,
        direction: Direction::Ascending,
        null_direction: NullDirection::Unspecified,
    };
    let k2 = SortKey {
        expr: b.field("SAL")?,
        direction: Direction::Descending,
        null_direction: NullDirection::Unspecified,
    };
    b.sort(&[k1, k2]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[ASC])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_sort_by_expression() -> Result<(), RelError> {
    // Sort by NULLS LAST.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let key = b.nulls_last(b.field("SAL")?);
    b.sort(&[key]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[ASC-nullsLast])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_limit() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.limit(None, Some(10));
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(fetch=[10])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_sort_limit() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let key = b.desc(b.field("SAL")?);
    b.sort_limit(Some(5), Some(3), &[key]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[DESC], offset=[5], fetch=[3])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_sort_limit0() -> Result<(), RelError> {
    // fetch=0 → empty Values.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.sort_limit(None, Some(0), &[]);
    let plan = b.build()?;
    assert_plan!(plan, "LogicalValues(tuples=[[]])");
    Ok(())
}

#[test]
fn test_sort_offset_limit() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.limit(Some(10), Some(5));
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(offset=[10], fetch=[5])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Rename
// -----------------------------------------------------------------------

#[test]
fn test_rename() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "DEPT"]);
    b.rename(vec![
        "department_no".to_string(),
        "department_name".to_string(),
        "location".to_string(),
    ]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(department_no=[$0], \
                           department_name=[$1], location=[$2])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

#[test]
fn test_rename_values() -> Result<(), RelError> {
    // rename() applied to a Values node.
    let mut b = builder();
    b.values(
        &["A", "B"],
        vec![vec![Val::Int(1), Val::String("x".into())]],
    );
    b.rename(vec!["col1".to_string(), "col2".to_string()]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(col1=[$0], col2=[$1])
              LogicalValues(tuples=[[{ 1, 'x' }]])
        "}
    );
    Ok(())
}

#[test]
fn test_asc_with_default_null_direction() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let key = SortKey {
        expr: b.field("SAL")?,
        direction: Direction::Ascending,
        null_direction: NullDirection::Unspecified,
    };
    b.sort(&[key]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[ASC])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_desc_with_default_null_direction() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let key = b.desc(b.field("SAL")?);
    b.sort(&[key]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[DESC])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Aggregate
// -----------------------------------------------------------------------

#[test]
fn test_aggregate() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk = b.group_key(vec![b.field("DEPTNO")?]);
    let aggs = vec![b.count_star().as_("C")];
    b.aggregate(&gk, aggs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{7}], C=[COUNT(*)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_aggregate2() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk = b.group_key(vec![b.field("DEPTNO")?, b.field("JOB")?]);
    let aggs = vec![b.count_star().as_("C"), b.sum("SAL").as_("TOTAL_SAL")];
    b.aggregate(&gk, aggs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{7, 2}], C=[COUNT(*)], TOTAL_SAL=[SUM($5)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_aggregate5() -> Result<(), RelError> {
    // aggregate with no group key → one output row.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk = b.group_key(vec![]);
    let aggs = vec![b.count_star().as_("C"), b.sum("SAL").as_("S")];
    b.aggregate(&gk, aggs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{}], C=[COUNT(*)], S=[SUM($5)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_aggregate_filter() -> Result<(), RelError> {
    // aggregate with a FILTER clause (simulated by pre-filtering).
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let cond = b.gt(b.field("SAL")?, b.literal_int(1000));
    b.filter(cond);
    let gk = b.group_key(vec![b.field("DEPTNO")?]);
    let aggs = vec![b.count_star().as_("C")];
    b.aggregate(&gk, aggs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{7}], C=[COUNT(*)])
              LogicalFilter(condition=[>($5, 1000)])
                LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_distinct() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "DEPT"]);
    b.distinct();
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{0, 1, 2}])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

#[test]
fn test_distinct_already() -> Result<(), RelError> {
    // distinct() on an Aggregate is a no-op.
    let mut b = builder();
    b.scan(&["scott", "DEPT"]);
    let gk = b.group_key(vec![b.field("DEPTNO")?]);
    b.aggregate(&gk, vec![]);
    b.distinct();
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{0}])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

#[test]
fn test_distinct_empty() -> Result<(), RelError> {
    // distinct() on empty Values is a no-op (stays empty).
    let mut b = builder();
    b.values(&["X", "Y"], vec![]);
    b.distinct();
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalValues(tuples=[[]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Join
// -----------------------------------------------------------------------

#[test]
fn test_project_join() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.scan(&["scott", "DEPT"]);
    let lhs = b.field2(1, "DEPTNO")?;
    let rhs = b.field2(0, "DEPTNO")?;
    let cond = b.equals(lhs, rhs);
    b.join(JoinType::Inner, cond);
    let exprs = vec![b.field("ENAME")?, b.field("DNAME")?];
    b.project(exprs);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(ENAME=[$1], DNAME=[$9])
              LogicalJoin(condition=[=($7, $8)], joinType=[inner])
                LogicalTableScan(table=[[scott, EMP]])
                LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

#[test]
fn test_alias() -> Result<(), RelError> {
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.as_("e");
    b.scan(&["scott", "DEPT"]);
    b.as_("d");
    let lhs = b.field2(1, "DEPTNO")?;
    let rhs = b.field2(0, "DEPTNO")?;
    let cond = b.equals(lhs, rhs);
    b.join(JoinType::Inner, cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalJoin(condition=[=($7, $8)], joinType=[inner])
              LogicalTableScan(table=[[scott, EMP]])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Alias variants (Task 15)
// -----------------------------------------------------------------------

#[test]
fn test_alias2() -> Result<(), RelError> {
    // Two aliased scans; join condition resolved via field_from(alias, col).
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.as_("e");
    b.scan(&["scott", "DEPT"]);
    b.as_("d");
    // field_from searches by alias rather than frame offset.
    let lhs = b.field_from("e", "DEPTNO")?; // EMP.DEPTNO = $7
    let rhs = b.field_from("d", "DEPTNO")?; // DEPT.DEPTNO = $8
    let cond = b.equals(lhs, rhs);
    b.join(JoinType::Inner, cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalJoin(condition=[=($7, $8)], joinType=[inner])
              LogicalTableScan(table=[[scott, EMP]])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

#[test]
fn test_alias_project() -> Result<(), RelError> {
    // Alias propagates through project; field_from works after project.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.as_("e");
    b.project(vec![b.field("EMPNO")?, b.field("ENAME")?]);
    // "e" alias now on the project frame; field_from resolves it.
    let cond = b.gt(b.field_from("e", "EMPNO")?, b.literal_int(7000));
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[>($0, 7000)])
              LogicalProject(EMPNO=[$0], ENAME=[$1])
                LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_alias_filter() -> Result<(), RelError> {
    // Alias propagates through filter; field_from works after filter.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.as_("e");
    let cond1 = b.gt(b.field("SAL")?, b.literal_int(1000));
    b.filter(cond1);
    // "e" alias now on the filter frame.
    let cond2 = b.gt(b.field_from("e", "SAL")?, b.literal_int(2000));
    b.filter(cond2);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[>($5, 2000)])
              LogicalFilter(condition=[>($5, 1000)])
                LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_alias_aggregate() -> Result<(), RelError> {
    // Alias propagates through aggregate; field_from resolves output cols.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.as_("e");
    let gk = b.group_key(vec![b.field("DEPTNO")?]);
    b.aggregate(&gk, vec![b.count_star().as_("C")]);
    // "e" alias now on the aggregate frame (row_type: DEPTNO, C).
    let cond = b.gt(b.field_from("e", "C")?, b.literal_int(1));
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[>($1, 1)])
              LogicalAggregate(group=[{7}], C=[COUNT(*)])
                LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_alias_past_top() -> Result<(), RelError> {
    // "e" alias is on the bottom frame (EMP); DEPT is the top frame (no
    // alias). field_from("e", ...) finds EMP even though it is buried.
    // EMP has 8 cols (base 0–7); DEPT is at base 8.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.as_("e");
    b.scan(&["scott", "DEPT"]);
    let lhs = b.field_from("e", "DEPTNO")?; // absolute $7
    let rhs = b.field2(0, "DEPTNO")?; // top frame (DEPT) → absolute $8
    let cond = b.equals(lhs, rhs);
    b.join(JoinType::Inner, cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalJoin(condition=[=($7, $8)], joinType=[inner])
              LogicalTableScan(table=[[scott, EMP]])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

#[test]
fn test_alias_sort() -> Result<(), RelError> {
    // Alias propagates through sort; field_from resolves cols after sort.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.as_("e");
    let key = b.desc(b.field("SAL")?);
    b.sort(&[key]);
    // "e" alias now on the sort frame.
    let cond = b.gt(b.field_from("e", "SAL")?, b.literal_int(500));
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[>($5, 500)])
              LogicalSort(sort0=[$5], dir0=[DESC])
                LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_alias_limit() -> Result<(), RelError> {
    // Alias propagates through limit; field_from resolves cols after limit.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.as_("e");
    b.limit(None, Some(5));
    // "e" alias now on the limit (Sort with empty collation) frame.
    let cond = b.gt(b.field_from("e", "SAL")?, b.literal_int(500));
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[>($5, 500)])
              LogicalSort(fetch=[5])
                LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_multi_level_alias() -> Result<(), RelError> {
    // Self-join: EMP aliased as "emp1" and "emp2".
    // field_from finds the correct frame for each alias.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.as_("emp1");
    b.scan(&["scott", "EMP"]);
    b.as_("emp2");
    let lhs = b.field_from("emp1", "EMPNO")?; // $0
    // MGR ordinal 3 in emp2: base=8 → $11
    let rhs = b.field_from("emp2", "MGR")?;
    let cond = b.equals(lhs, rhs);
    b.join(JoinType::Inner, cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalJoin(condition=[=($0, $11)], joinType=[inner])
              LogicalTableScan(table=[[scott, EMP]])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Set operations
// -----------------------------------------------------------------------

#[test]
fn test_union_project_values() -> Result<(), RelError> {
    let mut b = builder();
    b.values(&["X", "Y"], vec![vec![Val::Int(1), Val::Int(2)]]);
    b.values(&["X", "Y"], vec![vec![Val::Int(3), Val::Int(4)]]);
    b.union(false)?;
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalUnion(all=[false])
              LogicalValues(tuples=[[{ 1, 2 }]])
              LogicalValues(tuples=[[{ 3, 4 }]])
        "}
    );
    Ok(())
}

#[test]
fn test_union_alias() -> Result<(), RelError> {
    // union with aliased inputs.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.scan(&["scott", "EMP"]);
    b.union(true)?;
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalUnion(all=[true])
              LogicalTableScan(table=[[scott, EMP]])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_union() -> Result<(), RelError> {
    // UNION ALL of two EMP scans.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.scan(&["scott", "EMP"]);
    b.union(true)?;
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalUnion(all=[true])
              LogicalTableScan(table=[[scott, EMP]])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_union1() -> Result<(), RelError> {
    // union_n with n=1 is identity: no Union node is created.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.union_n(false, 1)?;
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_bad_union_args_error_message() {
    // union of inputs with different column counts → SetOpColumnMismatch.
    let mut b = builder();
    b.scan(&["scott", "EMP"]); // 8 columns
    b.scan(&["scott", "DEPT"]); // 3 columns
    let result = b.union(false);
    assert!(
        matches!(
            result,
            Err(RelError::SetOpColumnMismatch {
                expected: 8,
                got: 3
            })
        ),
        "expected SetOpColumnMismatch"
    );
}

#[test]
fn test_intersect() -> Result<(), RelError> {
    // INTERSECT of two DEPT scans.
    let mut b = builder();
    b.scan(&["scott", "DEPT"]);
    b.scan(&["scott", "DEPT"]);
    b.intersect(false)?;
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalIntersect(all=[false])
              LogicalTableScan(table=[[scott, DEPT]])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

#[test]
fn test_intersect3() -> Result<(), RelError> {
    // Three-way INTERSECT using intersect_n.
    let mut b = builder();
    b.scan(&["scott", "DEPT"]);
    b.scan(&["scott", "DEPT"]);
    b.scan(&["scott", "DEPT"]);
    b.intersect_n(false, 3)?;
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalIntersect(all=[false])
              LogicalTableScan(table=[[scott, DEPT]])
              LogicalTableScan(table=[[scott, DEPT]])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

#[test]
fn test_except() -> Result<(), RelError> {
    // EXCEPT of two DEPT scans.
    let mut b = builder();
    b.scan(&["scott", "DEPT"]);
    b.scan(&["scott", "DEPT"]);
    b.minus(false)?;
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalMinus(all=[false])
              LogicalTableScan(table=[[scott, DEPT]])
              LogicalTableScan(table=[[scott, DEPT]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Config (simplification flags)
// -----------------------------------------------------------------------

#[test]
fn test_filter_no_simplify() -> Result<(), RelError> {
    // With simplify_filter_true=false, Filter(true) is NOT eliminated.
    let config = BuilderConfig {
        simplify_filter_true: false,
        ..Default::default()
    };
    let mut b = RelBuilder::with_config(Arc::new(scott_schema()), config);
    b.scan(&["scott", "EMP"]);
    let cond = b.literal_bool(true);
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[true])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Filter AND/OR constant folding (Task 13)
// -----------------------------------------------------------------------

#[test]
fn test_scan_filter_and_false() -> Result<(), RelError> {
    // AND(cond, false) → false → empty Values.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let cond = b.and(
        b.gt(b.field("SAL")?, b.literal_int(1000)),
        b.literal_bool(false),
    );
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(plan, "LogicalValues(tuples=[[]])");
    Ok(())
}

#[test]
fn test_scan_filter_and_true() -> Result<(), RelError> {
    // AND(cond, true) → cond.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let cond = b.and(
        b.gt(b.field("SAL")?, b.literal_int(1000)),
        b.literal_bool(true),
    );
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[>($5, 1000)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_scan_filter_duplicate_and() -> Result<(), RelError> {
    // AND(cond, cond) → cond (structural duplicate removed).
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let lhs = b.gt(b.field("SAL")?, b.literal_int(1000));
    let rhs = b.gt(b.field("SAL")?, b.literal_int(1000));
    let cond = b.and(lhs, rhs);
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalFilter(condition=[>($5, 1000)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_filter_empty() -> Result<(), RelError> {
    // filter() on an empty Values is a no-op: stays empty.
    let mut b = builder();
    let row_type = vec![
        ("A".to_string(), int_type()),
        ("B".to_string(), bool_type()),
    ];
    b.empty(row_type);
    let cond = b.literal_bool(true);
    b.filter(cond);
    let plan = b.build()?;
    assert_plan!(plan, "LogicalValues(tuples=[[]])");
    Ok(())
}

// -----------------------------------------------------------------------
// Values variants (Task 12)
// -----------------------------------------------------------------------

#[test]
fn test_empty_with_alias() -> Result<(), RelError> {
    // empty() followed by as_() — alias has no effect on the plan string.
    let mut b = builder();
    let row_type = vec![
        ("A".to_string(), int_type()),
        ("B".to_string(), bool_type()),
    ];
    b.empty(row_type);
    b.as_("e");
    let plan = b.build()?;
    assert_plan!(plan, "LogicalValues(tuples=[[]])");
    Ok(())
}

#[test]
fn test_different_type_values() -> Result<(), RelError> {
    // Values with int, string, and real columns — types inferred per column.
    let mut b = builder();
    b.values(
        &["I", "S", "R"],
        vec![vec![
            Val::Int(1),
            Val::String("hello".into()),
            Val::Real(3.14),
        ]],
    );
    let plan = b.build()?;
    assert_plan!(plan, "LogicalValues(tuples=[[{ 1, 'hello', 3.14 }]])");
    Ok(())
}

#[test]
fn test_values_rename() -> Result<(), RelError> {
    // values() followed by rename() renames the output columns.
    let mut b = builder();
    b.values(&["A", "B"], vec![vec![Val::Int(1), Val::Int(2)]]);
    b.rename(vec!["X".to_string(), "Y".to_string()]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(X=[$0], Y=[$1])
              LogicalValues(tuples=[[{ 1, 2 }]])
        "}
    );
    Ok(())
}

#[test]
fn test_values_bad_no_fields() {
    let mut b = builder();
    b.values(&[], vec![vec![Val::Int(1), Val::Int(2)]]);
    assert!(matches!(b.build(), Err(RelError::NoFieldNames)));
}

#[test]
fn test_values_bad_no_values() {
    // A row with zero values when one column name was declared.
    let mut b = builder();
    b.values(&["A"], vec![vec![]]);
    assert!(matches!(b.build(), Err(RelError::RowLengthMismatch { .. })));
}

#[test]
fn test_values_bad_odd_multiple() {
    // A row with 1 value when 2 column names were declared.
    let mut b = builder();
    b.values(&["A", "B"], vec![vec![Val::Int(1)]]);
    assert!(matches!(b.build(), Err(RelError::RowLengthMismatch { .. })));
}

// -----------------------------------------------------------------------
// Simplifications (Task 10)
// -----------------------------------------------------------------------

#[test]
fn test_project_project() -> Result<(), RelError> {
    // Project over project → merged into a single project.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    b.project(vec![b.field("EMPNO")?, b.field("ENAME")?]);
    b.project(vec![b.field("ENAME")?]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(ENAME=[$1])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_sort_then_limit() -> Result<(), RelError> {
    // sort() then limit() → merged into a single Sort with collation + fetch.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let key = b.desc(b.field("SAL")?);
    b.sort(&[key]);
    b.limit(Some(2), Some(10));
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalSort(sort0=[$5], dir0=[DESC], offset=[2], fetch=[10])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_aggregate4() -> Result<(), RelError> {
    // distinct() after aggregate() is eliminated (aggregate already
    // produces at most one row per group key).
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk = b.group_key(vec![b.field("DEPTNO")?]);
    b.aggregate(&gk, vec![b.count_star().as_("C")]);
    b.distinct();
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{7}], C=[COUNT(*)])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

// -----------------------------------------------------------------------
// Aggregate variants (Task 16)
// -----------------------------------------------------------------------

#[test]
fn test_aggregate3() -> Result<(), RelError> {
    // GROUP BY two cols with no agg calls, then distinct() — no-op.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk = b.group_key(vec![b.field("DEPTNO")?, b.field("JOB")?]);
    b.aggregate(&gk, vec![]);
    b.distinct(); // already grouped → no-op
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalAggregate(group=[{7, 2}])
              LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_aggregate_and_then_project_named_field() -> Result<(), RelError> {
    // Aggregate, then project just the named agg-output column.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk = b.group_key(vec![b.field("DEPTNO")?]);
    b.aggregate(&gk, vec![b.count_star().as_("C")]);
    // Project only the count; DEPTNO is dropped.
    b.project(vec![b.field("C")?]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(C=[$1])
              LogicalAggregate(group=[{7}], C=[COUNT(*)])
                LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_aggregate_project_with_aliases() -> Result<(), RelError> {
    // Aggregate, then project-with-rename: rename the agg output columns.
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk = b.group_key(vec![b.field("DEPTNO")?]);
    b.aggregate(&gk, vec![b.count_star().as_("C")]);
    let exprs = vec![b.field("DEPTNO")?, b.field("C")?];
    b.project_named(exprs, vec!["DEPT_NUM".into(), "COUNT_ROWS".into()]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(DEPT_NUM=[$0], COUNT_ROWS=[$1])
              LogicalAggregate(group=[{7}], C=[COUNT(*)])
                LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
}

#[test]
fn test_aggregate_project_with_expression() -> Result<(), RelError> {
    // Aggregate, then project through an arithmetic expression on the
    // agg output (total SAL + 1).
    let mut b = builder();
    b.scan(&["scott", "EMP"]);
    let gk = b.group_key(vec![b.field("DEPTNO")?]);
    b.aggregate(&gk, vec![b.sum("SAL").as_("TOTAL_SAL")]);
    let total = b.field("TOTAL_SAL")?;
    let one = b.literal_int(1);
    let expr = b.plus(total, one);
    b.project(vec![b.field("DEPTNO")?, expr]);
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalProject(DEPTNO=[$0], $1=[+($1, 1)])
              LogicalAggregate(group=[{7}], TOTAL_SAL=[SUM($5)])
                LogicalTableScan(table=[[scott, EMP]])
        "}
    );
    Ok(())
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

// -----------------------------------------------------------------------
// Misc and remaining (Task 17)
// -----------------------------------------------------------------------

#[test]
fn test_scan_valid_table_wrong_case() -> Result<(), RelError> {
    // MapSchema lookup is case-insensitive; canonical name is used in the plan.
    let mut b = builder();
    b.scan(&["SCOTT", "emp"]); // wrong case
    let plan = b.build()?;
    assert_plan!(plan, "LogicalTableScan(table=[[scott, EMP]])");
    Ok(())
}

#[test]
fn test_union_project_values2() -> Result<(), RelError> {
    // Three-way UNION DISTINCT using union_n.
    let mut b = builder();
    b.values(&["X", "Y"], vec![vec![Val::Int(1), Val::Int(2)]]);
    b.values(&["X", "Y"], vec![vec![Val::Int(3), Val::Int(4)]]);
    b.values(&["X", "Y"], vec![vec![Val::Int(5), Val::Int(6)]]);
    b.union_n(false, 3)?;
    let plan = b.build()?;
    assert_plan!(
        plan,
        indoc! {"
            LogicalUnion(all=[false])
              LogicalValues(tuples=[[{ 1, 2 }]])
              LogicalValues(tuples=[[{ 3, 4 }]])
              LogicalValues(tuples=[[{ 5, 6 }]])
        "}
    );
    Ok(())
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
