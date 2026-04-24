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

use morel::syntax::ast::{Expr, StatementKind};
use morel::syntax::parser::parse_unadorned_statement;

/// Parses `input` as a single expression statement and returns the
/// expression.
fn parse_expr(input: &str) -> Expr {
    let stmt = parse_unadorned_statement(input).expect("parse should succeed");
    match stmt.kind {
        StatementKind::Expr(kind) => Expr {
            kind,
            span: stmt.span,
            id: stmt.id,
        },
        other => panic!("expected an expression, got {:?}", other),
    }
}

/// Parses `input` as a single expression statement and returns its unparsed
/// form.
fn unparse(input: &str) -> String {
    format!("{}", parse_expr(input).kind)
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

/// Asserts that `input` parses and unparses back to itself unchanged.
#[track_caller]
fn check_same(input: &str) {
    check(input, input);
}

#[test]
fn test_redundant_outer_parens_stripped() {
    check("((1 + 2)) * 3", "(1 + 2) * 3");
    check("((1 * 2)) + 3", "1 * 2 + 3");
}

#[test]
fn test_precedence_parens_preserved() {
    check_same("(1 + 2) * 3");
    check_same("1 + 2 * 3");
    check_same("1 * 2 + 3");
    check_same("(1 + 2) * (3 + 4)");
}

#[test]
fn test_left_associative_no_extra_parens() {
    check_same("1 + 2 + 3");
    check_same("1 - 2 - 3");
    check_same("1 * 2 * 3");
}

#[test]
fn test_right_associative_cons() {
    check_same("1 :: 2 :: [3]");
    check_same("(1 :: [2]) :: [[3]]");
}

#[test]
fn test_list_is_atomic() {
    check_same("hd [1, 2, 3]");
    check("hd ([1, 2, 3])", "hd [1, 2, 3]");
    check_same("length [1, 2, 3]");
}

#[test]
fn test_tuple_is_atomic() {
    check_same("f (1, 2)");
}

#[test]
fn test_record_is_atomic() {
    check_same("f {a = 1, b = 2}");
}

#[test]
fn test_comparison_vs_arithmetic() {
    check_same("1 + 2 = 3");
    check("(1 + 2) = 3", "1 + 2 = 3");
    check_same("1 = 2 + 3");
}

#[test]
fn test_andalso_orelse() {
    check_same("true andalso false orelse true");
    check_same("true orelse false andalso true");
    check_same("(true orelse false) andalso true");
}

#[test]
fn test_if_then_else() {
    check_same("if x then 1 else 2");
    check_same("if x > 0 then y + 1 else y - 1");
}

#[test]
fn test_fn() {
    check_same("fn x => x + 1");
    check_same("fn x => fn y => x + y");
}

#[test]
fn test_case() {
    check_same("case x of 1 => \"a\" | _ => \"b\"");
}

#[test]
fn test_let() {
    check_same("let val x = 1 in x + 2 end");
}

#[test]
fn test_record_with() {
    check_same("{r with a = 1}");
}

#[test]
fn test_from_basic() {
    check_same("from e in emps");
    check_same("from i in [1, 2, 3] where i > 1");
    check_same("from i in [1, 2, 3] where i > 1 yield i");
}

#[test]
fn test_from_multi_scan() {
    // Consecutive scans are separated by comma (canonical).
    check_same("from x in xs, y in ys");
    // An explicit `join` between adjacent scans is canonicalized to comma.
    check(
        "from x in xs join y in ys on x = y",
        "from x in xs, y in ys on x = y",
    );
    // After a non-scan step, a subsequent scan must use `join`.
    check_same("from x in xs where x > 0 join y in ys on x = y");
}

#[test]
fn test_from_order_group_compute() {
    check_same("from i in [3, 1, 2] order i");
    check(
        "from e in emps group e.deptno compute count",
        "from e in emps group #deptno e compute count",
    );
}

#[test]
fn test_from_distinct_skip_take() {
    check_same("from i in [1, 2, 3] distinct");
    check_same("from i in [1, 2, 3, 4, 5] skip 1 take 3");
}

#[test]
fn test_from_set_operations() {
    check_same("from i in [1, 2, 3] union [4, 5]");
    check_same("from i in [1, 2, 3] union distinct [4, 5]");
    check_same("from i in [1, 2, 3] intersect [2, 3]");
    check_same("from i in [1, 2, 3] except [2]");
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
    check_same("from e in (from x in xs yield x)");
}

use morel::syntax::ast::ExprKindTag;
use std::collections::HashSet;
use strum::IntoEnumIterator;

/// Coverage tracker for `ExprKind` variants. Seeded with every variant
/// via `ExprKindTag::iter()` (generated from `ExprKind` by
/// `strum::EnumDiscriminants`). [`Self::check_kind`] removes the parsed
/// variant's tag as each canonical input is exercised;
/// [`Self::assert_complete`] fails the test if anything remains.
struct KindCoverage {
    remaining: HashSet<ExprKindTag>,
}

impl KindCoverage {
    fn new() -> Self {
        Self {
            remaining: ExprKindTag::iter().collect(),
        }
    }

    /// Round-trips `input` (must be canonical) and marks the parsed
    /// variant as covered.
    #[track_caller]
    fn check_kind(&mut self, input: &str) {
        check_same(input);
        let expr = parse_expr(input);
        self.remaining.remove(&ExprKindTag::from(&expr.kind));
    }

    /// Fails the test if any declared variant is still uncovered.
    #[track_caller]
    fn assert_complete(&self) {
        assert!(
            self.remaining.is_empty(),
            "ExprKind variants not exercised by any check_kind call: {:?}",
            self.remaining
        );
    }
}

/// One round-trip per `ExprKind` variant.
///
/// `ExprKindTag` (auto-derived by `strum::EnumDiscriminants` from
/// `ExprKind`) tracks coverage. Adding a new variant to `ExprKind`
/// automatically adds it to `ExprKindTag::iter()`, so a canonical input
/// for it is required for this test to pass; the failure message names
/// any variant that was never exercised.
#[test]
fn test_each_expr_kind() {
    let mut k = KindCoverage::new();

    // Atoms: literal, identifier, op section, record selector, current,
    // ordinal, elements
    k.check_kind("1");
    k.check_kind("x");
    k.check_kind("op +");
    k.check_kind("#name");
    k.check_kind("current");
    k.check_kind("ordinal");
    k.check_kind("elements");

    // Arithmetic ops: +, -, *, /, div, mod, ~
    k.check_kind("1 + 2");
    k.check_kind("1 - 2");
    k.check_kind("1 * 2");
    k.check_kind("1 / 2.0");
    k.check_kind("1 div 2");
    k.check_kind("1 mod 2");
    k.check_kind("~x");

    // String concat: ^
    k.check_kind("\"a\" ^ \"b\"");

    // Comparison ops: =, <>, <, <=, >, >=, elem, notelem
    k.check_kind("1 = 2");
    k.check_kind("1 <> 2");
    k.check_kind("1 < 2");
    k.check_kind("1 <= 2");
    k.check_kind("1 > 2");
    k.check_kind("1 >= 2");
    k.check_kind("1 elem [1, 2]");
    k.check_kind("1 notelem [1, 2]");

    // Boolean ops: andalso, orelse, implies
    k.check_kind("true andalso false");
    k.check_kind("true orelse false");
    k.check_kind("true implies false");

    // Function: apply, compose
    k.check_kind("f x");
    k.check_kind("f o g");

    // List ops: ::, @
    k.check_kind("1 :: [2]");
    k.check_kind("[1] @ [2]");

    // Data constructors: [...], (...), {...}
    k.check_kind("[1, 2]");
    k.check_kind("(1, 2)");
    k.check_kind("{a = 1}");

    // Type annotation: :
    k.check_kind("1 : int");

    // Control flow: if, case, let, fn
    k.check_kind("if x then 1 else 2");
    k.check_kind("case x of 1 => \"a\" | _ => \"b\"");
    k.check_kind("let val x = 1 in x end");
    k.check_kind("fn x => x");

    // Queries: from, exists, forall, over (aggregate)
    k.check_kind("from x in xs");
    k.check_kind("exists x in xs where true");
    k.check_kind("forall x in xs require true");
    k.check_kind("count over xs");

    k.assert_complete();
}
