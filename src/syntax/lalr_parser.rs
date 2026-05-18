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
//
// Phase 2 of the pest→lalrpop migration. See issue.md.

//! Lalrpop-based parser entry points. Parallel to `parser.rs`
//! (which is pest-based) during the migration. Phase 4 swaps callers
//! over; Phase 5 deletes the pest path.

use crate::syntax::ast::{
    Expr, ExprKind, Span, Statement,
};
use crate::syntax::lexer::{LexError, MorelLexer};
use lalrpop_util::ParseError as LParseError;
use std::rc::Rc;

#[allow(clippy::all, dead_code, unused_imports)]
pub mod grammar {
    include!(concat!(env!("OUT_DIR"), "/syntax/morel.rs"));
}

// =================================================================
// Helpers used by grammar actions
// =================================================================

/// Constructs a [`Span`] from byte offsets and the shared `Rc<str>`
/// input. Called once per AST node from the lalrpop action blocks.
pub(crate) fn mk_span(input: &Rc<str>, start: usize, end: usize) -> Span {
    Span::new(input.clone(), start, end)
}

/// Builds the [`ExprKind`] for a precedence-4 comparison operator
/// (`=`, `<>`, `<`, `<=`, `>`, `>=`, `elem`, `notelem`). The action
/// blocks pass the matched operator string verbatim.
pub(crate) fn mk_comp(op: &'static str, a: Expr, b: Expr) -> ExprKind<Expr> {
    let l = Box::new(a);
    let r = Box::new(b);
    match op {
        "="       => ExprKind::Equal(l, r),
        "<>"      => ExprKind::NotEqual(l, r),
        "<"       => ExprKind::LessThan(l, r),
        "<="     => ExprKind::LessThanOrEqual(l, r),
        ">"       => ExprKind::GreaterThan(l, r),
        ">="      => ExprKind::GreaterThanOrEqual(l, r),
        "elem"    => ExprKind::Elem(l, r),
        "notelem" => ExprKind::NotElem(l, r),
        _ => unreachable!("comparison op {}", op),
    }
}

/// Builds the [`ExprKind`] for `::` or `@` (right-associative cons /
/// append at precedence 5).
pub(crate) fn mk_cons(op: &'static str, a: Expr, b: Expr) -> ExprKind<Expr> {
    let l = Box::new(a);
    let r = Box::new(b);
    match op {
        "::" => ExprKind::Cons(l, r),
        "@"  => ExprKind::Append(l, r),
        _ => unreachable!("cons op {}", op),
    }
}

/// Builds the [`ExprKind`] for an additive operator (`+`, `-`, `^`).
pub(crate) fn mk_add(op: &'static str, a: Expr, b: Expr) -> ExprKind<Expr> {
    let l = Box::new(a);
    let r = Box::new(b);
    match op {
        "+" => ExprKind::Plus(l, r),
        "-" => ExprKind::Minus(l, r),
        "^" => ExprKind::Caret(l, r),
        _ => unreachable!("additive op {}", op),
    }
}

/// Builds the [`ExprKind`] for a multiplicative operator (`*`, `/`,
/// `div`, `mod`).
pub(crate) fn mk_mult(op: &'static str, a: Expr, b: Expr) -> ExprKind<Expr> {
    let l = Box::new(a);
    let r = Box::new(b);
    match op {
        "*"   => ExprKind::Times(l, r),
        "/"   => ExprKind::Divide(l, r),
        "div" => ExprKind::Div(l, r),
        "mod" => ExprKind::Mod(l, r),
        _ => unreachable!("multiplicative op {}", op),
    }
}

/// Strips backticks from a quoted identifier and unescapes any
/// internal `` `` `` doubles to single backticks. Mirrors
/// `quoted_inner` in morel.pest:562-564.
pub(crate) fn unquote_backtick(s: &str) -> String {
    // s looks like `` `...`. ``
    let inner = &s[1..s.len() - 1];
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '`' {
            // `` becomes `; pest guarantees only doubled backticks
            // make it past the lexer.
            chars.next();
            out.push('`');
        } else {
            out.push(c);
        }
    }
    out
}

// =================================================================
// Public API
// =================================================================

/// Error returned by the lalrpop-based parser.
#[derive(Debug)]
pub enum ParseError {
    /// Lexer-level error (unterminated comment, invalid token, ...).
    Lex(LexError, usize, usize),
    /// Parser-level error (unexpected token, EOF, ...).
    Parse(String),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::Lex(e, s, _) => write!(f, "lex error at byte {}: {}", s, e),
            ParseError::Parse(m) => write!(f, "parse error: {}", m),
        }
    }
}

impl<T: std::fmt::Debug> From<LParseError<usize, T, LexError>> for ParseError {
    fn from(e: LParseError<usize, T, LexError>) -> Self {
        match e {
            LParseError::User { error } => ParseError::Lex(error, 0, 0),
            other => ParseError::Parse(format!("{:?}", other)),
        }
    }
}

pub type ParseResult<T> = Result<T, ParseError>;

/// Parses a Morel statement followed by a `;`.
pub fn parse_statement(input: &str) -> ParseResult<Statement> {
    let rc_input: Rc<str> = input.to_string().into();
    let lex = MorelLexer::new(input);
    grammar::StatementSemiParser::new()
        .parse(&rc_input, lex)
        .map_err(ParseError::from)
}

/// Parses a Morel statement with no trailing `;`, suitable for
/// fixture inputs.
pub fn parse_unadorned_statement(input: &str) -> ParseResult<Statement> {
    let rc_input: Rc<str> = input.to_string().into();
    let lex = MorelLexer::new(input);
    grammar::StatementParser::new()
        .parse(&rc_input, lex)
        .map_err(ParseError::from)
}

// NOTE: type-scheme entry point is part of the full grammar (see
// /tmp/morel.full.lalrpop.draft). Phase 4 wires it back in.

#[cfg(test)]
mod test {
    use super::*;
    use crate::syntax::ast::StatementKind;

    fn ast_str(s: &str) -> String {
        let st = parse_unadorned_statement(s).expect("parse");
        format!("{}", st.kind)
    }

    // Smoke tests — Phase 4 will extend to full .smli corpus.

    #[test] fn int_literal() {
        assert_eq!(ast_str("42"), "42");
    }

    #[test] fn negative_int() {
        assert_eq!(ast_str("~5"), "~5");
    }

    #[test] fn add_left_assoc() {
        assert_eq!(ast_str("1 + 2 + 3"), "1 + 2 + 3");
    }

    #[test] fn mult_binds_tighter_than_add() {
        assert_eq!(ast_str("1 + 2 * 3"), "1 + 2 * 3");
        assert_eq!(ast_str("1 * 2 + 3"), "1 * 2 + 3");
    }

    #[test] fn parens_strip() {
        assert_eq!(ast_str("(1 + 2)"), "1 + 2");
    }

    #[test] fn tuple_two() {
        assert_eq!(ast_str("(1, 2)"), "(1, 2)");
    }

    #[test] fn tuple_three() {
        assert_eq!(ast_str("(1, 2, 3)"), "(1, 2, 3)");
    }

    #[test] fn unit() {
        assert_eq!(ast_str("()"), "()");
    }

    #[test] fn list_basic() {
        assert_eq!(ast_str("[1, 2, 3]"), "[1, 2, 3]");
    }

    #[test] fn empty_list() {
        assert_eq!(ast_str("[]"), "[]");
    }

    #[test] fn cons_right_assoc() {
        assert_eq!(ast_str("1 :: 2 :: 3"), "1 :: 2 :: 3");
    }

    #[test] fn if_expr() {
        let s = ast_str("if true then 1 else 2");
        assert_eq!(s, "if true then 1 else 2");
    }

    #[test] fn let_expr() {
        let s = ast_str("let val x = 1 in x end");
        assert!(s.starts_with("let "), "got: {}", s);
        assert!(s.contains("val x = 1"));
        assert!(s.contains("in x end"));
    }

    #[test] fn application() {
        assert_eq!(ast_str("f x"), "f x");
        assert_eq!(ast_str("f x y"), "f x y");
    }

    #[test] fn val_decl() {
        let s = ast_str("val x = 1");
        assert_eq!(s, "val x = 1");
    }

    #[test] fn bool_literal() {
        assert_eq!(ast_str("true"), "true");
        assert_eq!(ast_str("false"), "false");
    }

    #[test] fn string_literal() {
        let s = ast_str("\"hello\"");
        assert_eq!(s, "\"hello\"");
    }

    #[test] fn negation() {
        // `~ x` parses; pretty-prints as `~x`.
        let s = ast_str("~ x");
        assert_eq!(s, "~x");
    }

    // --- Phase 3 step 1: records, case, fn -----------------------

    #[test] fn empty_record() {
        assert_eq!(ast_str("{}"), "{}");
    }

    #[test] fn record_with_labels() {
        let s = ast_str("{x = 1, y = 2}");
        assert!(s.starts_with("{") && s.ends_with("}"));
        assert!(s.contains("x = 1"));
        assert!(s.contains("y = 2"));
    }

    #[test] fn case_simple() {
        let s = ast_str("case x of 0 => 1 | _ => 2");
        assert!(s.starts_with("case x of "), "got: {}", s);
        assert!(s.contains("0 => 1"));
        assert!(s.contains("_ => 2"));
    }

    #[test] fn fn_simple() {
        let s = ast_str("fn x => x + 1");
        assert!(s.starts_with("fn "), "got: {}", s);
        assert!(s.contains("x + 1"));
    }

    #[test] fn fn_multi_match() {
        let s = ast_str("fn 0 => 1 | _ => 2");
        assert!(s.contains("0 => 1"));
        assert!(s.contains("_ => 2"));
    }

    #[test] fn case_inside_if() {
        // case must be parenthesized inside an if-else clause
        let s = ast_str("if true then 1 else (case x of _ => 2)");
        assert!(s.contains("if true"));
        assert!(s.contains("case x"));
    }

    // --- Phase 3 step 2: type annotations + Type cascade ---------

    #[test] fn annotated_simple() {
        let s = ast_str("x : int");
        assert!(s.contains("x"));
        assert!(s.contains("int"));
    }

    #[test] fn annotated_fn_type() {
        let s = ast_str("f : int -> int");
        assert!(s.contains("int"));
        assert!(s.contains("->"));
    }

    #[test] fn annotated_tuple_type() {
        let s = ast_str("p : int * string");
        assert!(s.contains("int"));
        assert!(s.contains("string"));
    }

    #[test] fn annotated_app_type() {
        let s = ast_str("xs : int list");
        assert!(s.contains("int"));
        assert!(s.contains("list"));
    }

    #[test] fn annotated_type_var() {
        // 'a is a polymorphic type variable
        let s = ast_str("x : 'a");
        assert!(s.contains("'a"));
    }

    #[test] fn annotated_paren_type() {
        let s = ast_str("f : (int -> int)");
        assert!(s.contains("int"));
    }

    #[test] fn fn_type_right_assoc() {
        // int -> int -> int parses as int -> (int -> int)
        let s = ast_str("f : int -> int -> int");
        assert!(s.contains("int"));
    }

    // Parity check: parse `simple` example through both parsers and
    // compare the kind string. Quick sanity that the two grammars
    // construct the same AST shape.
    #[test] fn parity_simple_expressions() {
        for src in &[
            "42",
            "1 + 2",
            "f x",
            "(1, 2, 3)",
            "if true then 1 else 2",
            "let val x = 1 in x end",
            "[1, 2, 3]",
        ] {
            let lalr = parse_unadorned_statement(src).expect(src);
            let pest_st =
                crate::syntax::parser::parse_unadorned_statement(src).expect(src);
            assert_eq!(
                format!("{}", lalr.kind),
                format!("{}", pest_st.kind),
                "input: {:?}",
                src,
            );
        }
    }

    // Suppress unused-import warning when no test refers to ExprKind
    // directly.
    #[allow(dead_code)]
    fn _refs() -> ExprKind<Expr> {
        ExprKind::Ordinal
    }
    #[allow(dead_code)]
    fn _refs2() -> StatementKind {
        StatementKind::Expr(ExprKind::Ordinal)
    }
}
