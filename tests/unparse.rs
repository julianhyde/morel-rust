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
