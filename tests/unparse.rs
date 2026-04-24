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

//! Round-trip tests for AST pretty-printing: parse an expression, unparse
//! it, and check that the result matches the expected string. These verify
//! that the unparser uses parentheses iff they are required by the
//! precedence of surrounding operators.

use morel::syntax::ast::StatementKind;
use morel::syntax::parser::parse_unadorned_statement;

/// Parses `input` as a single expression statement and returns its unparsed
/// form.
fn unparse(input: &str) -> String {
    let stmt = parse_unadorned_statement(input).expect("parse should succeed");
    match stmt.kind {
        StatementKind::Expr(e) => format!("{}", e),
        other => panic!("expected an expression, got {:?}", other),
    }
}

/// Asserts that `input` parses and unparses to `expected`.
#[track_caller]
fn check(input: &str, expected: &str) {
    let actual = unparse(input);
    assert_eq!(
        actual, expected,
        "\n  input    = {:?}\n  expected = {:?}\n  actual   = {:?}",
        input, expected, actual
    );
}

#[test]
fn test_redundant_outer_parens_stripped() {
    check("((1 + 2)) * 3", "(1 + 2) * 3");
    check("((1 * 2)) + 3", "1 * 2 + 3");
}

#[test]
fn test_precedence_parens_preserved() {
    check("(1 + 2) * 3", "(1 + 2) * 3");
    check("1 + 2 * 3", "1 + 2 * 3");
    check("1 * 2 + 3", "1 * 2 + 3");
    check("(1 + 2) * (3 + 4)", "(1 + 2) * (3 + 4)");
}

#[test]
fn test_left_associative_no_extra_parens() {
    check("1 + 2 + 3", "1 + 2 + 3");
    check("1 - 2 - 3", "1 - 2 - 3");
    check("1 * 2 * 3", "1 * 2 * 3");
}

#[test]
fn test_right_associative_cons() {
    check("1 :: 2 :: [3]", "1 :: 2 :: [3]");
    check("(1 :: [2]) :: [[3]]", "(1 :: [2]) :: [[3]]");
}

#[test]
fn test_list_is_atomic() {
    check("hd [1, 2, 3]", "hd [1, 2, 3]");
    check("hd ([1, 2, 3])", "hd [1, 2, 3]");
    check("length [1, 2, 3]", "length [1, 2, 3]");
}

#[test]
fn test_tuple_is_atomic() {
    check("f (1, 2)", "f (1, 2)");
}

#[test]
fn test_record_is_atomic() {
    check("f {a = 1, b = 2}", "f {a = 1, b = 2}");
}

#[test]
fn test_comparison_vs_arithmetic() {
    check("1 + 2 = 3", "1 + 2 = 3");
    check("(1 + 2) = 3", "1 + 2 = 3");
    check("1 = 2 + 3", "1 = 2 + 3");
}

#[test]
fn test_andalso_orelse() {
    check(
        "true andalso false orelse true",
        "true andalso false orelse true",
    );
    check(
        "true orelse false andalso true",
        "true orelse false andalso true",
    );
    check(
        "(true orelse false) andalso true",
        "(true orelse false) andalso true",
    );
}

#[test]
fn test_if_then_else() {
    check("if x then 1 else 2", "if x then 1 else 2");
    check(
        "if x > 0 then y + 1 else y - 1",
        "if x > 0 then y + 1 else y - 1",
    );
}

#[test]
fn test_fn() {
    check("fn x => x + 1", "fn x => x + 1");
    check("fn x => fn y => x + y", "fn x => fn y => x + y");
}

#[test]
fn test_case() {
    check(
        "case x of 1 => \"a\" | _ => \"b\"",
        "case x of 1 => \"a\" | _ => \"b\"",
    );
}

#[test]
fn test_let() {
    check("let val x = 1 in x + 2 end", "let val x = 1; in x + 2 end");
}

#[test]
fn test_record_with() {
    check("{r with a = 1}", "{r with a = 1}");
}

#[test]
fn test_from_basic() {
    check("from e in emps", "from e in emps");
    check(
        "from i in [1, 2, 3] where i > 1",
        "from i in [1, 2, 3] where i > 1",
    );
    check(
        "from i in [1, 2, 3] where i > 1 yield i",
        "from i in [1, 2, 3] where i > 1 yield i",
    );
}

#[test]
fn test_from_multi_scan() {
    // Consecutive scans are separated by comma (canonical).
    check("from x in xs, y in ys", "from x in xs, y in ys");
    // An explicit `join` between adjacent scans is canonicalized to comma.
    check(
        "from x in xs join y in ys on x = y",
        "from x in xs, y in ys on x = y",
    );
    // After a non-scan step, a subsequent scan must use `join`.
    check(
        "from x in xs where x > 0 join y in ys on x = y",
        "from x in xs where x > 0 join y in ys on x = y",
    );
}

#[test]
fn test_from_order_group_compute() {
    check("from i in [3, 1, 2] order i", "from i in [3, 1, 2] order i");
    check(
        "from e in emps group e.deptno compute count",
        "from e in emps group #deptno e compute count",
    );
}

#[test]
fn test_from_distinct_skip_take() {
    check(
        "from i in [1, 2, 3] distinct",
        "from i in [1, 2, 3] distinct",
    );
    check(
        "from i in [1, 2, 3, 4, 5] skip 1 take 3",
        "from i in [1, 2, 3, 4, 5] skip 1 take 3",
    );
}

#[test]
fn test_from_set_operations() {
    check(
        "from i in [1, 2, 3] union [4, 5]",
        "from i in [1, 2, 3] union [4, 5]",
    );
    check(
        "from i in [1, 2, 3] union distinct [4, 5]",
        "from i in [1, 2, 3] union distinct [4, 5]",
    );
    check(
        "from i in [1, 2, 3] intersect [2, 3]",
        "from i in [1, 2, 3] intersect [2, 3]",
    );
    check(
        "from i in [1, 2, 3] except [2]",
        "from i in [1, 2, 3] except [2]",
    );
}

#[test]
fn test_exists_forall() {
    check(
        "exists e in emps where e.name = \"X\"",
        "exists e in emps where #name e = \"X\"",
    );
    check(
        "forall e in emps require e.age > 0",
        "forall e in emps require #age e > 0",
    );
}

#[test]
fn test_subquery_wrapped() {
    // A `from` appearing as the source of another `from` must be
    // parenthesized; otherwise the inner query's steps would be attributed
    // to the outer query.
    check(
        "from e in (from x in xs yield x)",
        "from e in (from x in xs yield x)",
    );
}
