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

//! Phase 0 spike — see issue.md / hydromatic/morel-rust#43.
//!
//! Throwaway lalrpop grammar (`spike.lalrpop`) and a marker AST used
//! only to assert the *shape* of the parse, not its semantics.
//! Verifies that the LR(1)-hostile parts of Morel's grammar — the
//! 13-level precedence cascade with `over` at 7.5, and the postfix-
//! dispatch lookahead from morel.pest:225-239 — translate cleanly.
//!
//! Will be deleted in Phase 5.

#![allow(dead_code)]

use std::fmt::{Display, Formatter, Result as FmtResult};

// Generated from `src/syntax/spike.lalrpop`.
#[allow(clippy::all, dead_code, unused_imports)]
pub mod grammar {
    include!(concat!(env!("OUT_DIR"), "/syntax/spike.rs"));
}

/// Spike-AST node. Prints in a S-expression-ish form so tests can
/// assert against the shape directly.
#[derive(Debug, Clone, PartialEq)]
pub enum SE {
    Int(i64),
    Var(String),
    Unit,
    Tuple(Vec<SE>),
    /// `f x` — single arg apply.
    Apply(Box<SE>, Box<SE>),
    /// `e op e`.
    Bin(&'static str, Box<SE>, Box<SE>),
    /// `~e`.
    Neg(Box<SE>),
    /// `e.label` (record projection).
    Dot(Box<SE>, String),
    /// `e.label arg` (trailing method call on application).
    Trailing(Box<SE>, String, Box<SE>),
    /// `(a, b, c)` as a method-arg group (kept distinct so we can
    /// observe how the rule wraps the args).
    ParenArgs(Vec<SE>),
}

impl SE {
    pub fn int(n: i64) -> SE { SE::Int(n) }
    pub fn var(s: impl Into<String>) -> SE { SE::Var(s.into()) }
    pub fn unit() -> SE { SE::Unit }
    pub fn tuple(es: Vec<SE>) -> SE { SE::Tuple(es) }
    pub fn paren_args(es: Vec<SE>) -> SE { SE::ParenArgs(es) }
    pub fn apply(h: SE, a: SE) -> SE { SE::Apply(Box::new(h), Box::new(a)) }
    pub fn bin(op: &'static str, l: SE, r: SE) -> SE {
        SE::Bin(op, Box::new(l), Box::new(r))
    }
    pub fn neg(e: SE) -> SE { SE::Neg(Box::new(e)) }
    pub fn dot(e: SE, l: String) -> SE { SE::Dot(Box::new(e), l) }
    pub fn trailing(h: SE, l: String, a: SE) -> SE {
        SE::Trailing(Box::new(h), l, Box::new(a))
    }
    /// Lower an `IdChain` into nested `Dot` nodes left-to-right.
    pub fn id_chain(head: &str, tails: Vec<String>) -> SE {
        let mut e = SE::var(head);
        for t in tails {
            e = SE::dot(e, t);
        }
        e
    }
}

impl Display for SE {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            SE::Int(n) => write!(f, "{}", n),
            SE::Var(s) => write!(f, "{}", s),
            SE::Unit => write!(f, "()"),
            SE::Tuple(es) => {
                write!(f, "(tuple")?;
                for e in es { write!(f, " {}", e)?; }
                write!(f, ")")
            }
            SE::Apply(h, a) => write!(f, "(apply {} {})", h, a),
            SE::Bin(op, l, r) => write!(f, "({} {} {})", op, l, r),
            SE::Neg(e) => write!(f, "(neg {})", e),
            SE::Dot(e, l) => write!(f, "(dot {} {})", e, l),
            SE::Trailing(h, l, a) => write!(f, "(trail {} {} {})", h, l, a),
            SE::ParenArgs(es) => {
                write!(f, "(parg")?;
                for e in es { write!(f, " {}", e)?; }
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::grammar::ExprParser;
    use super::*;

    fn parse(s: &str) -> SE {
        ExprParser::new().parse(s).unwrap_or_else(|e| {
            panic!("spike parse failed on {:?}: {:?}", s, e)
        })
    }

    fn assert_parses_to(input: &str, expected: &str) {
        let got = parse(input);
        assert_eq!(format!("{}", got), expected, "input: {:?}", input);
    }

    // --- Precedence cascade -------------------------------------

    #[test] fn add_left_assoc() {
        assert_parses_to("1 + 2 + 3", "(+ (+ 1 2) 3)");
    }

    #[test] fn mult_binds_tighter_than_add() {
        assert_parses_to("1 + 2 * 3", "(+ 1 (* 2 3))");
        assert_parses_to("1 * 2 + 3", "(+ (* 1 2) 3)");
    }

    #[test] fn cons_right_assoc() {
        assert_parses_to("1 :: 2 :: 3", "(:: 1 (:: 2 3))");
        assert_parses_to("a @ b @ c", "(@ a (@ b c))");
    }

    #[test] fn andalso_binds_tighter_than_orelse() {
        assert_parses_to("a orelse b andalso c", "(orelse a (andalso b c))");
    }

    #[test] fn comp_below_cons() {
        assert_parses_to("a = 1 :: 2", "(= a (:: 1 2))");
    }

    #[test] fn unary_negation() {
        assert_parses_to("~x", "(neg x)");
        assert_parses_to("~ ~x", "(neg (neg x))");
        assert_parses_to("1 + ~x", "(+ 1 (neg x))");
    }

    #[test] fn negative_literal_distinct_from_unary() {
        // `~5` is one NEG_INT token, not unary applied to `5`.
        assert_parses_to("~5", "-5");
    }

    // --- `over` at 7.5 ------------------------------------------

    // NOTE: morel.pest:214 lets `over`'s RHS be a full Expr. Without
    // semantic predicates, that creates shift/reduce conflicts at
    // every higher precedence. We encode `over` as right-assoc with a
    // tight RHS (see grammar comment). Equivalent on every input the
    // pest action accepts (parser.rs:366-373 only handles binary over).
    #[test] fn over_associates_at_its_own_level() {
        // a over b + c  =>  (a over b) + c    (was (over a (+ b c)) in pest)
        assert_parses_to("a over b + c", "(+ (over a b) c)");
    }

    #[test] fn over_below_multiplicative() {
        // a * b over c  =>  a * (b over c)
        assert_parses_to("a * b over c", "(* a (over b c))");
    }

    // --- Postfix dispatch ---------------------------------------

    #[test] fn dot_on_leading_atom() {
        assert_parses_to("f.x", "(dot f x)");
        assert_parses_to("f.x.y", "(dot (dot f x) y)");
    }

    #[test] fn function_application_left_assoc() {
        assert_parses_to("f x", "(apply f x)");
        assert_parses_to("f x y", "(apply (apply f x) y)");
    }

    // NOTE: The pest case `f x.y` (where `.y` belongs to the
    // arg `x`, giving `(apply f (dot x y))`) is NOT representable
    // in pure LR(1). See the grammar comment on `ArgExpr` and the
    // findings written to `issue.md`. The following case_3 test
    // (commented out) shows what would need to work — and the
    // workaround.
    //
    // #[test] fn f_x_dot_y_paren_z() {
    //     assert_parses_to("f x.y (z)", "(apply (apply f (dot x y)) z)");
    // }
    #[test] fn f_x_dot_y_paren_z_workaround() {
        // Workaround: parenthesize the arg.
        assert_parses_to(
            "f (x.y) (z)",
            "(apply (apply f (dot x y)) z)",
        );
    }

    #[test] fn cs_complement_unit() {
        // Case 1 from morel.pest:222: `cs.complement ()` is one Apply
        // with method receiver `cs` and arg `()`. Works because the
        // chain is on the leading expr (PostfixExpr), not in arg
        // position.
        assert_parses_to(
            "cs.complement ()",
            "(apply (dot cs complement) ())",
        );
    }

    #[test] fn cs_complement_chain_via_trailing_method() {
        // Case 2: `cs.complement ().complement ()` — the second
        // `.complement ()` is a trailing method on the whole prior
        // Apply.
        assert_parses_to(
            "cs.complement ().complement ()",
            "(trail (apply (dot cs complement) ()) complement ())",
        );
    }

    #[test] fn parenthesized_atom_no_arg_chain() {
        // `f (x) y` — `(x)` is one arg, `y` is another. No postfix
        // attaches to `(x)` because `IdChain` requires a bare ident.
        assert_parses_to("f (x) y", "(apply (apply f x) y)");
    }

    #[test] fn method_arg_can_be_tuple() {
        assert_parses_to(
            "xs.drop (1, 2)",
            "(apply (dot xs drop) (tuple 1 2))",
        );
    }

    #[test] fn unit_literal_via_atom() {
        assert_parses_to("()", "()");
    }

    #[test] fn parenthesized_expr_strips_parens() {
        assert_parses_to("(1 + 2)", "(+ 1 2)");
    }
}
