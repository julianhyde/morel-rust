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
// Phase 1 of the pest→lalrpop migration. See issue.md.

//! Lexer for the Morel surface language. Mirrors the token set of
//! `src/syntax/morel.pest`. Used as a custom `extern` lexer by the
//! lalrpop grammar (Phase 2).
//!
//! Notable behaviors:
//!
//! * Line comments `(*) ... \n` and **nested** block comments
//!   `(* ... (* ... *) ... *)` are skipped. Nesting is handled by a
//!   logos callback that scans the remainder manually — regex alone
//!   cannot recognize balanced delimiters.
//!
//! * `~` followed by digits (no whitespace) lexes as part of a
//!   negative numeric literal (`~5` is one token). `~ 5` is the
//!   tilde unary operator followed by `5`. Mirrors morel.pest:243
//!   (`expr_unary_op = { !literal ~ "~" }`).
//!
//! * Keywords win over identifiers via logos's longest-match +
//!   token-vs-regex priority. `andx` lexes as `Ident("andx")`, not
//!   `And` followed by `Ident("x")`.

use logos::{Filter, Lexer, Logos};
use std::fmt::{Display, Formatter, Result as FmtResult};

/// Errors produced by the lexer.
#[derive(Debug, Clone, PartialEq, Default)]
pub enum LexError {
    /// Default for logos's `Error` slot — produced when no rule matches.
    #[default]
    InvalidToken,
    /// `(* ... ` reached end-of-input without a matching `*)`.
    UnterminatedBlockComment,
    /// `" ... ` reached end-of-input without a closing quote.
    UnterminatedString,
}

impl Display for LexError {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            LexError::InvalidToken => write!(f, "invalid token"),
            LexError::UnterminatedBlockComment => {
                write!(f, "unterminated block comment")
            }
            LexError::UnterminatedString => write!(f, "unterminated string"),
        }
    }
}

/// Skip whitespace, line comments, and nested block comments.
///
/// Logos's regex engine cannot match nested delimiters; this callback
/// runs after the `(*` opener and walks the remainder manually,
/// counting nesting depth.
fn skip_block_comment(lex: &mut Lexer<Tok>) -> Filter<()> {
    // The trigger pattern `(*` has already been consumed; we now scan
    // `lex.remainder()` and bump past the matching `*)`.
    let rem = lex.remainder().as_bytes();
    let mut depth: usize = 1;
    let mut i = 0;
    while i + 1 < rem.len() {
        let a = rem[i];
        let b = rem[i + 1];
        if a == b'(' && b == b'*' {
            depth += 1;
            i += 2;
        } else if a == b'*' && b == b')' {
            depth -= 1;
            i += 2;
            if depth == 0 {
                lex.bump(i);
                return Filter::Skip;
            }
        } else {
            i += 1;
        }
    }
    // Unterminated. Consume the rest so the lexer doesn't loop, then
    // surface as an error on the next token.
    lex.bump(rem.len());
    Filter::Emit(())
}

/// The set of tokens produced by the Morel lexer. Variants carry the
/// raw lexeme as a `String` for content tokens (identifiers,
/// literals); keyword/punctuation variants are unit because their
/// content is fixed.
#[derive(Logos, Debug, Clone, PartialEq)]
#[logos(error = LexError)]
// Whitespace and `(*) ... ` line comments — silently skipped. The
// line-comment match is greedy by design (it consumes to end-of-line
// or end-of-input); the `allow_greedy` flag suppresses logos's
// well-meaning warning.
#[logos(skip r"[ \t\r\n]+")]
#[logos(skip(r"\(\*\)[^\r\n]*", allow_greedy = true))]
pub enum Tok {
    // --- Keywords (sorted; see morel.pest:26-82) -----------------
    #[token("and")] And,
    #[token("andalso")] AndAlso,
    #[token("as")] As,
    #[token("case")] Case,
    #[token("compute")] Compute,
    #[token("current")] Current,
    #[token("datatype")] Datatype,
    #[token("distinct")] Distinct,
    #[token("div")] Div,
    #[token("elem")] Elem,
    #[token("elements")] Elements,
    #[token("else")] Else,
    #[token("end")] End,
    #[token("except")] Except,
    #[token("exception")] Exception,
    #[token("exists")] Exists,
    #[token("fn")] Fn,
    #[token("forall")] Forall,
    #[token("from")] From,
    #[token("fun")] Fun,
    #[token("group")] Group,
    #[token("if")] If,
    #[token("implies")] Implies,
    #[token("in")] In,
    #[token("inst")] Inst,
    #[token("intersect")] Intersect,
    #[token("into")] Into,
    #[token("join")] Join,
    #[token("let")] Let,
    #[token("mod")] Mod,
    #[token("notelem")] NotElem,
    #[token("o")] O,
    #[token("of")] Of,
    #[token("on")] On,
    #[token("op")] Op,
    #[token("order")] Order,
    #[token("ordinal")] Ordinal,
    #[token("orelse")] OrElse,
    #[token("over")] Over,
    #[token("rec")] Rec,
    #[token("require")] Require,
    #[token("sig")] Sig,
    #[token("signature")] Signature,
    #[token("skip")] Skip,
    #[token("take")] Take,
    #[token("then")] Then,
    #[token("through")] Through,
    #[token("type")] Type,
    #[token("typeof")] Typeof,
    #[token("union")] Union,
    #[token("unorder")] Unorder,
    #[token("val")] Val,
    #[token("where")] Where,
    #[token("with")] With,
    #[token("yield")] Yield,

    // --- Bool literals -------------------------------------------
    //
    // morel.pest treats `true`/`false` as a `bool_literal` (not a
    // keyword) but for grammar clarity we lex them as dedicated
    // tokens.
    #[token("true")] True,
    #[token("false")] False,

    // --- Punctuation ---------------------------------------------
    //
    // Multi-char tokens come first so logos's longest-match selects
    // them over their single-char prefixes.
    #[token("...")] Ellipsis,
    #[token("=>")] FatArrow,
    #[token("->")] Arrow,
    #[token("::")] DoubleColon,
    #[token("<=")] Le,
    #[token(">=")] Ge,
    #[token("<>")] Ne,

    #[token("(")] LParen,
    #[token(")")] RParen,
    #[token("[")] LBracket,
    #[token("]")] RBracket,
    #[token("{")] LBrace,
    #[token("}")] RBrace,
    #[token(",")] Comma,
    #[token(";")] Semicolon,
    #[token(":")] Colon,
    #[token("|")] Pipe,
    #[token("~")] Tilde,
    #[token("_")] Underscore,
    #[token("=")] Eq,
    #[token("<")] Lt,
    #[token(">")] Gt,
    #[token("@")] At,
    #[token("+")] Plus,
    #[token("-")] Minus,
    #[token("^")] Caret,
    #[token("*")] Star,
    #[token("/")] Slash,
    #[token(".")] Dot,

    // --- Block comment trigger -----------------------------------
    //
    // The `(*` opener doesn't match `(*)` (which falls to the
    // line-comment skip above because it's a strictly longer match).
    // The callback consumes through the matching `*)`. On EOF
    // mid-comment we emit (), and the iterator wrapper converts to
    // LexError::UnterminatedBlockComment.
    #[token("(*", skip_block_comment)]
    BlockCommentSentinel,

    // --- Numeric literals ----------------------------------------
    //
    // `~`-prefix variants are preferred over the prefixless ones via
    // logos's longest-match rule. Scientific must come before Real
    // (priority) so `1.5e2` doesn't lex as Real(1.5) then Ident(e2).
    //
    // The original lexeme (including any leading `~`) is preserved
    // verbatim in the token, mirroring how
    // `LiteralKind::Int(String)` and `LiteralKind::Real(String)`
    // are populated in parser.rs:1593-1611.
    #[regex(r"~?[0-9]+(\.[0-9]+)?[eE]~?[0-9]+", |lex| lex.slice().to_string(), priority = 4)]
    SciLit(String),

    #[regex(r"~?[0-9]+\.[0-9]+", |lex| lex.slice().to_string(), priority = 3)]
    RealLit(String),

    #[regex(r"~?[0-9]+", |lex| lex.slice().to_string(), priority = 2)]
    IntLit(String),

    // --- String and char literals --------------------------------
    //
    // The regex matches the outer quotes and the body permissively;
    // the parser is responsible for re-validating individual escape
    // sequences (parser.rs:2068-2146) and for stripping the quotes.
    // The leading lexer position is preserved as part of the span.
    #[regex(r#""(?:[^"\\]|\\.)*""#, |lex| lex.slice().to_string())]
    StringLit(String),

    #[regex(r##"#"(?:[^"\\]|\\.)*""##, |lex| lex.slice().to_string())]
    CharLit(String),

    // --- Identifier-shaped tokens --------------------------------
    //
    // `priority = 1` makes Ident lose every same-length tie with a
    // keyword #[token]. Without this, single-letter keywords like
    // `o` (morel.pest:116) collide with the regex at logos's
    // default priority.
    #[regex(r"[A-Za-z][A-Za-z0-9_']*", |lex| lex.slice().to_string(), priority = 1)]
    Ident(String),

    #[regex(r"`(?:[^`]|``)*`", |lex| lex.slice().to_string())]
    QuotedIdent(String),

    // Record selector: `#foo`, `#1`, `#x_y'`. Note: includes digits
    // so `#1` (tuple-index selector) is one token, not `#` + `1`.
    #[regex(r"#[A-Za-z0-9_']+", |lex| lex.slice().to_string())]
    RecordSelector(String),

    // Type variable: `'a`, `'foo'_'`. Differs from quoted-ident
    // (which uses backticks) and from char literal (which starts
    // with `#"`).
    #[regex(r"'[A-Za-z][A-Za-z0-9_']*", |lex| lex.slice().to_string())]
    TyVar(String),
}

impl Tok {
    /// Returns the variant name as a static string. Useful for
    /// reporting expected/found tokens.
    pub fn name(&self) -> &'static str {
        match self {
            Tok::And => "and",
            Tok::AndAlso => "andalso",
            Tok::As => "as",
            Tok::Case => "case",
            Tok::Compute => "compute",
            Tok::Current => "current",
            Tok::Datatype => "datatype",
            Tok::Distinct => "distinct",
            Tok::Div => "div",
            Tok::Elem => "elem",
            Tok::Elements => "elements",
            Tok::Else => "else",
            Tok::End => "end",
            Tok::Except => "except",
            Tok::Exception => "exception",
            Tok::Exists => "exists",
            Tok::Fn => "fn",
            Tok::Forall => "forall",
            Tok::From => "from",
            Tok::Fun => "fun",
            Tok::Group => "group",
            Tok::If => "if",
            Tok::Implies => "implies",
            Tok::In => "in",
            Tok::Inst => "inst",
            Tok::Intersect => "intersect",
            Tok::Into => "into",
            Tok::Join => "join",
            Tok::Let => "let",
            Tok::Mod => "mod",
            Tok::NotElem => "notelem",
            Tok::O => "o",
            Tok::Of => "of",
            Tok::On => "on",
            Tok::Op => "op",
            Tok::Order => "order",
            Tok::Ordinal => "ordinal",
            Tok::OrElse => "orelse",
            Tok::Over => "over",
            Tok::Rec => "rec",
            Tok::Require => "require",
            Tok::Sig => "sig",
            Tok::Signature => "signature",
            Tok::Skip => "skip",
            Tok::Take => "take",
            Tok::Then => "then",
            Tok::Through => "through",
            Tok::Type => "type",
            Tok::Typeof => "typeof",
            Tok::Union => "union",
            Tok::Unorder => "unorder",
            Tok::Val => "val",
            Tok::Where => "where",
            Tok::With => "with",
            Tok::Yield => "yield",
            Tok::True => "true",
            Tok::False => "false",
            Tok::Ellipsis => "...",
            Tok::FatArrow => "=>",
            Tok::Arrow => "->",
            Tok::DoubleColon => "::",
            Tok::Le => "<=",
            Tok::Ge => ">=",
            Tok::Ne => "<>",
            Tok::LParen => "(",
            Tok::RParen => ")",
            Tok::LBracket => "[",
            Tok::RBracket => "]",
            Tok::LBrace => "{",
            Tok::RBrace => "}",
            Tok::Comma => ",",
            Tok::Semicolon => ";",
            Tok::Colon => ":",
            Tok::Pipe => "|",
            Tok::Tilde => "~",
            Tok::Underscore => "_",
            Tok::Eq => "=",
            Tok::Lt => "<",
            Tok::Gt => ">",
            Tok::At => "@",
            Tok::Plus => "+",
            Tok::Minus => "-",
            Tok::Caret => "^",
            Tok::Star => "*",
            Tok::Slash => "/",
            Tok::Dot => ".",
            Tok::BlockCommentSentinel => "<block-comment>",
            Tok::SciLit(_) => "<scientific-literal>",
            Tok::RealLit(_) => "<real-literal>",
            Tok::IntLit(_) => "<int-literal>",
            Tok::StringLit(_) => "<string-literal>",
            Tok::CharLit(_) => "<char-literal>",
            Tok::Ident(_) => "<identifier>",
            Tok::QuotedIdent(_) => "<quoted-identifier>",
            Tok::RecordSelector(_) => "<record-selector>",
            Tok::TyVar(_) => "<type-variable>",
        }
    }
}

impl Display for Tok {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}", self.name())
    }
}

/// Wrap logos's `Lexer` into the `(usize, Tok, usize)` triple
/// iterator expected by lalrpop. Translates the
/// `BlockCommentSentinel` (emitted on unterminated `(* ...`) into a
/// proper lex error.
pub struct MorelLexer<'input> {
    inner: logos::Lexer<'input, Tok>,
}

impl<'input> MorelLexer<'input> {
    pub fn new(input: &'input str) -> Self {
        MorelLexer { inner: Tok::lexer(input) }
    }
}

/// Token triple used by lalrpop: `(start, tok, end)`.
pub type Spanned = (usize, Tok, usize);

impl Iterator for MorelLexer<'_> {
    type Item = Result<Spanned, LexError>;
    fn next(&mut self) -> Option<Self::Item> {
        let tok = self.inner.next()?;
        let span = self.inner.span();
        match tok {
            Err(e) => Some(Err(e)),
            // Sentinel only escapes the lexer when EOF was hit before
            // a matching `*)` was found.
            Ok(Tok::BlockCommentSentinel) => {
                Some(Err(LexError::UnterminatedBlockComment))
            }
            Ok(t) => Some(Ok((span.start, t, span.end))),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn lex(input: &str) -> Vec<Tok> {
        MorelLexer::new(input).map(|r| r.unwrap().1).collect()
    }

    fn lex_err(input: &str) -> LexError {
        for r in MorelLexer::new(input) {
            if let Err(e) = r {
                return e;
            }
        }
        panic!("expected lex error in {:?}", input);
    }

    // --- Whitespace and comments --------------------------------

    #[test] fn skips_whitespace() {
        assert_eq!(lex("   \t \n  "), vec![]);
    }

    #[test] fn skips_line_comment() {
        assert_eq!(lex("(*) hello\nx"), vec![Tok::Ident("x".into())]);
    }

    #[test] fn skips_simple_block_comment() {
        assert_eq!(lex("(* hi *) x"), vec![Tok::Ident("x".into())]);
    }

    #[test] fn skips_nested_block_comment() {
        let toks = lex("(* a (* b *) c *) x");
        assert_eq!(toks, vec![Tok::Ident("x".into())]);
    }

    #[test] fn skips_deeply_nested_block_comment() {
        let toks = lex("(* (* (* deep *) *) *) y");
        assert_eq!(toks, vec![Tok::Ident("y".into())]);
    }

    #[test] fn unterminated_block_comment_errors() {
        assert_eq!(lex_err("(* unterminated"), LexError::UnterminatedBlockComment);
    }

    // --- Keywords vs identifiers --------------------------------

    #[test] fn keywords_lex_as_keywords() {
        assert_eq!(lex("and andalso let"), vec![Tok::And, Tok::AndAlso, Tok::Let]);
    }

    #[test] fn keyword_prefix_is_identifier() {
        // `andx` is one identifier, not `and` + `x`.
        assert_eq!(lex("andx"), vec![Tok::Ident("andx".into())]);
    }

    #[test] fn identifier_with_apostrophe_and_underscore() {
        assert_eq!(lex("foo_bar'"), vec![Tok::Ident("foo_bar'".into())]);
    }

    #[test] fn quoted_identifier() {
        assert_eq!(lex("`a b c`"), vec![Tok::QuotedIdent("`a b c`".into())]);
    }

    #[test] fn quoted_identifier_with_escaped_backtick() {
        assert_eq!(lex("`a``b`"), vec![Tok::QuotedIdent("`a``b`".into())]);
    }

    #[test] fn type_variable() {
        assert_eq!(lex("'a"), vec![Tok::TyVar("'a".into())]);
    }

    #[test] fn record_selector() {
        assert_eq!(lex("#foo"), vec![Tok::RecordSelector("#foo".into())]);
        assert_eq!(lex("#1"), vec![Tok::RecordSelector("#1".into())]);
    }

    // --- Punctuation --------------------------------------------

    #[test] fn multi_char_punct_wins_over_single() {
        assert_eq!(lex("<= >= <> :: => -> ..."), vec![
            Tok::Le, Tok::Ge, Tok::Ne, Tok::DoubleColon,
            Tok::FatArrow, Tok::Arrow, Tok::Ellipsis,
        ]);
    }

    #[test] fn underscore_is_distinct_from_identifier() {
        assert_eq!(lex("_"), vec![Tok::Underscore]);
        // pest's identifier rejects leading `_`, so `_x` lexes as
        // `_` + `x`.
        assert_eq!(lex("_x"), vec![Tok::Underscore, Tok::Ident("x".into())]);
    }

    // --- Numerics -----------------------------------------------

    #[test] fn integer_literal() {
        assert_eq!(lex("0 42"), vec![
            Tok::IntLit("0".into()), Tok::IntLit("42".into()),
        ]);
    }

    #[test] fn negative_integer_no_space_is_one_token() {
        assert_eq!(lex("~5"), vec![Tok::IntLit("~5".into())]);
    }

    #[test] fn tilde_with_space_then_integer_is_two_tokens() {
        assert_eq!(lex("~ 5"), vec![
            Tok::Tilde, Tok::IntLit("5".into()),
        ]);
    }

    #[test] fn real_literal() {
        assert_eq!(lex("3.14 ~2.71"), vec![
            Tok::RealLit("3.14".into()),
            Tok::RealLit("~2.71".into()),
        ]);
    }

    #[test] fn scientific_literal() {
        assert_eq!(lex("6.02e23 ~6.02e~23 1e10"), vec![
            Tok::SciLit("6.02e23".into()),
            Tok::SciLit("~6.02e~23".into()),
            Tok::SciLit("1e10".into()),
        ]);
    }

    #[test] fn record_index_via_dot_is_int_not_real() {
        // `t.1` is field access; the `1` is an IntLit, not part of
        // a real literal.
        assert_eq!(lex("t.1"), vec![
            Tok::Ident("t".into()), Tok::Dot, Tok::IntLit("1".into()),
        ]);
    }

    #[test] fn dot_after_real_is_dot() {
        // `1.5.toString` is RealLit(1.5) then `.` then Ident.
        assert_eq!(lex("1.5.toString"), vec![
            Tok::RealLit("1.5".into()),
            Tok::Dot,
            Tok::Ident("toString".into()),
        ]);
    }

    // --- Strings and chars --------------------------------------

    #[test] fn string_literal_simple() {
        assert_eq!(lex(r#""hi""#), vec![Tok::StringLit(r#""hi""#.into())]);
    }

    #[test] fn string_literal_with_escapes() {
        assert_eq!(
            lex(r#""a\nb\"c""#),
            vec![Tok::StringLit(r#""a\nb\"c""#.into())],
        );
    }

    #[test] fn char_literal() {
        assert_eq!(lex(r##"#"a""##), vec![Tok::CharLit(r##"#"a""##.into())]);
    }

    #[test] fn char_literal_vs_record_selector() {
        // `#"a"` is a char literal (length 4); `#a` is a record
        // selector. They don't overlap.
        assert_eq!(lex(r##"#"a""##), vec![Tok::CharLit(r##"#"a""##.into())]);
        assert_eq!(lex("#a"), vec![Tok::RecordSelector("#a".into())]);
    }

    // --- Booleans -----------------------------------------------

    #[test] fn bool_literals() {
        assert_eq!(lex("true false"), vec![Tok::True, Tok::False]);
    }

    // --- Span correctness ---------------------------------------

    #[test] fn spans_track_positions() {
        let mut lx = MorelLexer::new("let x = 1");
        let toks: Vec<_> = (&mut lx).collect::<Result<_, _>>().unwrap();
        assert_eq!(toks, vec![
            (0, Tok::Let, 3),
            (4, Tok::Ident("x".into()), 5),
            (6, Tok::Eq, 7),
            (8, Tok::IntLit("1".into()), 9),
        ]);
    }

    // --- Larger smoke test --------------------------------------

    #[test] fn small_let_program_smoke() {
        let src = "let val x = 1 + ~5 in x end";
        let toks = lex(src);
        assert_eq!(
            toks,
            vec![
                Tok::Let,
                Tok::Val,
                Tok::Ident("x".into()),
                Tok::Eq,
                Tok::IntLit("1".into()),
                Tok::Plus,
                Tok::IntLit("~5".into()),
                Tok::In,
                Tok::Ident("x".into()),
                Tok::End,
            ],
        );
    }
}
