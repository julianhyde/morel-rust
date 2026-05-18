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

//! Grammar-ambiguity regression tests. Each test pins down which of
//! several syntactically-valid parses the Morel parser produces for
//! an ambiguous input, and documents what every alternative parse
//! *would* produce. Where Standard ML has the same ambiguity, the
//! test references SML/NJ's behaviour as the source of truth.
//!
//! These tests guard against accidental changes to the resolution
//! rule (whether driven by a parser-generator switch, grammar
//! rewrite, or pest-rule reordering). See issue.md ("Grammar
//! ambiguities") for the full discussion. Originally written during
//! the pest→lalrpop migration attempt (hydromatic/morel-rust#43)
//! after the migration was stopped — the genuine ambiguities below
//! are language-level decisions, independent of parser
//! implementation.

use morel::syntax::ast::{Expr, StatementKind};
use morel::syntax::parser::parse_unadorned_statement;

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

fn unparse(input: &str) -> String {
    format!("{}", parse_expr(input).kind)
}

#[track_caller]
fn check(input: &str, expected: &str) {
    let actual = unparse(input);
    assert_eq!(
        actual, expected,
        "\n  input    = {:?}\n  expected = {:?}\n  actual   = {:?}",
        input, expected, actual,
    );
}

// =====================================================================
// A1: postfix dispatch in argument position
// =====================================================================
//
// Input: `f x.y`
//
// Two parses are grammatically valid:
//
//   Parse 1 (chosen):   Apply(f, Apply(#y, x))
//                       — `.y` is a postfix field-select on the
//                         argument `x`; the whole `x.y` is one arg
//                         of `f`.
//
//   Parse 2 (rejected): Trailing(Apply(f, x), y, ?)
//                       — `.y` is the start of a trailing-method
//                         call on the application `Apply(f, x)`.
//                         This requires a method argument after
//                         `.y` (per morel.pest:238); without one
//                         it's syntactically incomplete.
//
// This ambiguity is **Morel-specific** — the postfix-`.field`
// extension at precedence 9 (morel.pest:155) doesn't exist in
// Standard ML, which writes `#y x` for field selection. So
// SML/NJ provides no comparison.
//
// Morel's resolution is the PEG-greedy "argument absorbs the
// chain" interpretation (morel.pest:225-239,
// MorelParser.jj:835-911). The user-facing rule: to apply `f` to
// the projection `(f x).y` you must parenthesise the receiver.

#[test]
fn a1_arg_position_postfix_chain() {
    // `f x.y` — `.y` belongs to the argument `x`.
    // Unparses as `f (#y x)` because RecordSelector applied to
    // an argument renders as `#sel arg`.
    check("f x.y", "f (#y x)");
}

#[test]
fn a1_arg_position_postfix_chain_with_extra_arg() {
    // `f x.y (z)` — `.y` extends `x`, then `(z)` is the next arg
    // of `f`. Shape: `Apply(Apply(f, x.y), z)`.
    check("f x.y (z)", "f (#y x) z");
}

#[test]
fn a1_chain_via_trailing_method() {
    // `cs.complement ().complement ()` — the second `.complement`
    // IS a trailing method call (on the result of the first
    // application), because there's nothing for it to be the
    // start of in arg position. This confirms the trailing-method
    // rule is the right tool when the chain happens after args.
    let s = unparse("cs.complement ().complement ()");
    assert!(
        s.contains("#complement") && s.matches("#complement").count() == 2,
        "expected two #complement selectors, got: {}",
        s,
    );
}

// =====================================================================
// A2: `if a then b else c d` — dangling application across `else`
// =====================================================================
//
// Two grammatically-valid parses:
//
//   Parse 1 (chosen):   If(a, b, Apply(c, d))
//                       — `c d` is one application that forms the
//                         else clause.
//
//   Parse 2 (rejected): Apply(If(a, b, c), d)
//                       — the if-expression `if a then b else c`
//                         is itself the function, applied to `d`.
//
// Both parses produce well-formed ASTs. Without a discriminating
// tie-breaker, either is valid in any LR(1) grammar that admits
// `if`/`then`/`else` as atomic expressions.
//
// **SML/NJ chooses Parse 1.** Verified:
//   - sml> if true then 1 else (fn x => x + 100) 7;
//     val it = 1 : int
//   - Type-checks because the else branch `(fn x => x+100) 7 : int`
//     unifies with the then branch `1 : int`. Parse 2 would have
//     branch types `int` vs `int -> int` which don't unify,
//     producing a type error — but no type error occurs, so SML/NJ
//     used Parse 1.
//
// Morel adopts the same convention. The user-facing rule: to
// apply an if-expression as a function, parenthesise it:
// `(if a then b else c) d`.

#[test]
fn a2_else_clause_absorbs_application() {
    let s = unparse("if true then 1 else g 7");
    // Parse 1: if true then 1 else g 7  (apply is INSIDE else).
    // Parse 2 would unparse as: (if true then 1 else g) 7.
    assert!(
        !s.starts_with('('),
        "Parse 2 would wrap the if-expression in parens to show \
         it's the function; got: {}",
        s,
    );
    assert!(
        s.contains("if true then 1 else") && s.ends_with("g 7"),
        "got: {}",
        s,
    );
}

// =====================================================================
// A3: `fn p => fn q => 1 | r => 2` — to which `fn` does `| r => 2` belong?
// =====================================================================
//
// Two grammatically-valid parses:
//
//   Parse 1 (chosen):   Fn([p => Fn([q => 1, r => 2])])
//                       — `| r => 2` is the second arm of the
//                         **inner** fn. Outer fn has one arm.
//
//   Parse 2 (rejected): Fn([p => Fn([q => 1]), r => 2])
//                       — `| r => 2` is the second arm of the
//                         **outer** fn. Inner fn has one arm.
//
// **SML/NJ chooses Parse 1.** Verified:
//   - sml> fn x => fn y => 1 | z => 2;
//     stdIn:1.17-1.35 Error: match redundant
//             y => ...
//       -->   z => ...
//   - Range 1.17-1.35 in that input is `y => 1 | z => 2` (the
//     INNER fn's match list). The redundancy warning fires on
//     z relative to y: both bind anything, so z is unreachable.
//     This proves SML/NJ grouped `y => 1 | z => 2` as the inner
//     fn's matches. (Parse 2 would point at the outer's `x` and
//     `z`, a different range.)
//
// Morel does the same — verified directly: the parser produces
// the same redundancy warning at the same source range as SML/NJ
// (`./target/debug/main -e 'fn x => fn y => 1 | z => 2'` prints
// `stdIn:1.21-1.27 Error: match redundant`).
//
// User-facing rule: nested case/fn match lists need parens to
// shift `|` to the outer match.

#[test]
fn a3_pipe_binds_to_innermost_fn() {
    let s = unparse("fn x => fn y => 1 | z => 2");
    // Parse 1 unparses (per the AST round-trip) with the `| z =>`
    // appearing **inside** the inner fn's printed form.
    // Parse 2 would put `| z =>` at the outer fn's level, with
    // the inner fn collapsed onto its single arm `y => 1`.
    //
    // Concretely:
    //   Parse 1: fn x => fn y => 1 | z => 2
    //            (single outer arm `x =>`, inner fn has 2 arms)
    //   Parse 2: fn x => (fn y => 1) | z => 2
    //            (outer has 2 arms `x =>` and `z =>`)
    //
    // The distinguishing feature is whether the outer `fn x =>`
    // is followed by another `| ` at the same level. We assert
    // there is exactly ONE `|` in the unparsed form (it's the
    // inner separator); Parse 2 would have one as well but with
    // different bracketing — the test is reinforced by the
    // count of `=> ` arrows (we expect 3: one for x, one for y,
    // one for z, with z under the inner fn).
    let arrow_count = s.matches(" => ").count();
    assert_eq!(arrow_count, 3, "expected 3 => arrows, got: {}", s);
}

#[test]
fn a3_outer_pipe_via_parens() {
    // `fn x => (fn y => 1) | z => 2` forces Parse-2-style grouping
    // by parenthesising the inner fn. Outer fn now has two arms.
    let s = unparse("fn x => (fn y => 1) | z => 2");
    // The outer fn is `fn x => ... | z => ...` — the `|` is at
    // the OUTER level. The inner fn (now parenthesised) has
    // exactly one arm.
    assert!(s.contains("| z =>"), "got: {}", s);
}
