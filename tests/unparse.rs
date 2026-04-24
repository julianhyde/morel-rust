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

use morel::syntax::ast::{Expr, ExprKind, StatementKind};
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
    check("let val x = 1 in x + 2 end", "let val x = 1; in x + 2 end");
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

use std::collections::HashSet;

/// Declares one round-trip case per `ExprKind` variant. Each line names
/// the variant, optionally with `(..)` for variants with payload, and
/// gives its canonical `(input, expected)` pair.
///
/// The macro expands to three items:
///  - `fn variant_name(&ExprKind<Expr>) -> &'static str` — an exhaustive
///    match that returns the variant's string name.
///  - `const VARIANT_CASES: &[(&str, &str)]` — the `(input, expected)`
///    pairs in declaration order.
///  - `const VARIANT_NAMES: &[&str]` — the variant names in declaration
///    order.
///
/// Compile-time safety: adding a new `ExprKind` variant breaks the
/// `variant_name` match (non-exhaustive). Removing a line here does the
/// same — the variant is no longer covered. Either way, the build fails.
///
/// Runtime safety: the test seeds a `HashSet` from `VARIANT_NAMES` and
/// removes each variant as its case runs; if the set is non-empty at
/// the end, some variant was declared but not actually exercised.
macro_rules! every_variant {
    ( $(
        $variant:ident $( ( $($args:tt)* ) )?
            => ( $input:expr, $expected:expr )
    ),+ $(,)? ) => {
        fn variant_name(k: &ExprKind<Expr>) -> &'static str {
            match k {
                $(
                    ExprKind::$variant $( ( $($args)* ) )?
                        => stringify!($variant),
                )+
            }
        }
        const VARIANT_CASES: &[(&str, &str)] =
            &[ $( ($input, $expected) ),+ ];
        const VARIANT_NAMES: &[&str] =
            &[ $( stringify!($variant) ),+ ];
    };
}

every_variant! {
    // lint: sort until '#}' where '^\s*[A-Z]'
    Aggregate(..)          => ("count over xs", "count over xs"),
    AndAlso(..)            => ("true andalso false",
                               "true andalso false"),
    Annotated(..)          => ("1 : int", "1 : int"),
    Append(..)             => ("[1] @ [2]", "[1] @ [2]"),
    Apply(..)              => ("f x", "f x"),
    Caret(..)              => ("\"a\" ^ \"b\"", "\"a\" ^ \"b\""),
    Case(..)               => ("case x of 1 => \"a\" | _ => \"b\"",
                               "case x of 1 => \"a\" | _ => \"b\""),
    Compose(..)            => ("f o g", "f o g"),
    Cons(..)               => ("1 :: [2]", "1 :: [2]"),
    Current                => ("current", "current"),
    Div(..)                => ("1 div 2", "1 div 2"),
    Divide(..)             => ("1 / 2.0", "1 / 2.0"),
    Elem(..)               => ("1 elem [1, 2]", "1 elem [1, 2]"),
    Elements               => ("elements", "elements"),
    Equal(..)              => ("1 = 2", "1 = 2"),
    Exists(..)             => ("exists x in xs where true",
                               "exists x in xs where true"),
    Fn(..)                 => ("fn x => x", "fn x => x"),
    Forall(..)             => ("forall x in xs require true",
                               "forall x in xs require true"),
    From(..)               => ("from x in xs", "from x in xs"),
    GreaterThan(..)        => ("1 > 2", "1 > 2"),
    GreaterThanOrEqual(..) => ("1 >= 2", "1 >= 2"),
    Identifier(..)         => ("x", "x"),
    If(..)                 => ("if x then 1 else 2",
                               "if x then 1 else 2"),
    Implies(..)            => ("true implies false",
                               "true implies false"),
    LessThan(..)           => ("1 < 2", "1 < 2"),
    LessThanOrEqual(..)    => ("1 <= 2", "1 <= 2"),
    // `let` currently emits an extra `;` after each decl.
    Let(..)                => ("let val x = 1 in x end",
                               "let val x = 1; in x end"),
    List(..)               => ("[1, 2]", "[1, 2]"),
    Literal(..)            => ("1", "1"),
    Minus(..)              => ("1 - 2", "1 - 2"),
    Mod(..)                => ("1 mod 2", "1 mod 2"),
    Negate(..)             => ("~x", "~x"),
    NotElem(..)            => ("1 notelem [1, 2]",
                               "1 notelem [1, 2]"),
    NotEqual(..)           => ("1 <> 2", "1 <> 2"),
    OpSection(..)          => ("op +", "op +"),
    OrElse(..)             => ("true orelse false",
                               "true orelse false"),
    Ordinal                => ("ordinal", "ordinal"),
    Plus(..)               => ("1 + 2", "1 + 2"),
    Record(..)             => ("{a = 1}", "{a = 1}"),
    RecordSelector(..)     => ("#name", "#name"),
    Times(..)              => ("1 * 2", "1 * 2"),
    Tuple(..)              => ("(1, 2)", "(1, 2)"),
}

/// One round-trip per `ExprKind` variant.
///
/// Compile-time: adding a new `ExprKind` variant or removing a line from
/// the `every_variant!` invocation above breaks the build, because the
/// generated `variant_name` match is no longer exhaustive.
///
/// Runtime: if the generated `VARIANT_NAMES` list contains a variant for
/// which no case's input actually produces that variant, the test panics
/// with the list of variants left in the set.
#[test]
fn test_every_variant() {
    let mut remaining: HashSet<&str> = VARIANT_NAMES.iter().copied().collect();
    for (input, expected) in VARIANT_CASES {
        check(input, expected);
        let expr = parse_expr(input);
        remaining.remove(variant_name(&expr.kind));
    }
    assert!(
        remaining.is_empty(),
        "variants declared in every_variant! but not exercised by any \
         canonical input: {:?}",
        remaining
    );
}
