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

//! Prints a relational tree.
//!
//! The text is `spec.md` §6 on morel-java's `julianhyde/449-tree`
//! branch, and it is the cross-implementation contract: the same query
//! prints the same text in morel-java, morel-rust and morel-go. It is
//! what `Sys.planOf` returns.
//!
//! The invariant that makes the text parseable is that **a relational
//! operator is the first non-whitespace on its line**. One node per
//! line, its inputs two spaces further in, its arguments in brackets in
//! the order the datatype lists them, and an argument that is absent --
//! an inner join's kind, a `true` condition -- omitted.
//!
//! Two numbering sequences run through the text, and both are
//! properties of the text rather than of any node: `t$0`, `t$1`, ...
//! for a type too long to print in full, listed once in a legend at the
//! end; and `v$0`, `v$1`, ... for the binders the compiler generated,
//! numbered by first occurrence so that the text depends on the query
//! and nothing else. An implementation that built the text by
//! concatenating what its children returned would get both wrong, and
//! get them wrong silently, because each child would start again at
//! zero -- so there is one writer, and it is threaded through.

// Nothing builds a relational tree yet -- the translator is milestone
// R5 of plan.md -- so nothing outside the tests calls this. Remove when
// R5 lands.
#![allow(dead_code)]

use crate::compile::core::{Expr, Rel};
use crate::compile::types::{Label, Type};
use crate::eval::val::Val;
use std::collections::HashMap;
use std::fmt::Write as _;
use std::rc::Rc;

/// A type longer than this is replaced by a reference and printed once
/// in the legend.
///
/// A character count, rather than a rule about the type's shape,
/// because three implementations must agree on which types are
/// abbreviated and they already agree on the text of a type. It sits
/// above `int option list` and `{a:int, b:int} list`, and below a
/// three-field record.
const MONIKER_LIMIT: usize = 24;

/// Returns the plan of the tree rooted at `exp`.
///
/// With `with_types`, every node line ends in its collection type,
/// which is what `Sys.planOf` prints; without, the tree alone.
pub fn plan(exp: &Expr, with_types: bool) -> String {
    let mut w = Writer::new(with_types);
    w.node(exp, 0);
    w.finish()
}

/// Builds the text of one plan.
///
/// There is one of these per plan, not one per node: the numbering
/// sequences span the whole text, a tree nested inside another tree's
/// expressions included.
struct Writer {
    out: String,
    with_types: bool,
    /// Monikers that have been given a `t$N`, in the order they were
    /// first seen, which is the order they are numbered and listed.
    type_refs: Vec<String>,
}

impl Writer {
    fn new(with_types: bool) -> Writer {
        Writer {
            out: String::new(),
            with_types,
            type_refs: Vec::new(),
        }
    }

    /// Writes one node, and its inputs below it.
    fn node(&mut self, exp: &Expr, indent: usize) {
        let line = match exp {
            Expr::Rel(t, rel) => {
                let mut line = rel.op_name().to_string();
                for arg in args(rel) {
                    let _ = write!(line, " [{}]", arg);
                }
                self.with_type(line, t)
            }
            // A leaf is an ordinary expression, and prints as one.
            leaf => self.with_type(format!("{}", leaf), &leaf.type_()),
        };
        let _ = writeln!(self.out, "{:indent$}{}", "", line, indent = indent);
        if let Expr::Rel(_, rel) = exp {
            for input in rel.inputs() {
                self.node(input, indent + 2);
            }
        }
    }

    /// Appends `: type` to a node's line, as a moniker or a reference to
    /// one.
    fn with_type(&mut self, mut line: String, t: &Rc<Type>) -> String {
        if !self.with_types {
            return line;
        }
        let moniker = format!("{}", t);
        if moniker.len() <= MONIKER_LIMIT {
            let _ = write!(line, " : {}", moniker);
            return line;
        }
        // Two types that print the same moniker share a reference,
        // because the moniker is all the plan says about them.
        let i = self
            .type_refs
            .iter()
            .position(|m| *m == moniker)
            .unwrap_or_else(|| {
                self.type_refs.push(moniker);
                self.type_refs.len() - 1
            });
        let _ = write!(line, " : t${}", i);
        line
    }

    /// Returns the finished text: the tree, then the legend, then the
    /// binders renumbered.
    fn finish(mut self) -> String {
        if !self.type_refs.is_empty() {
            self.out.push('\n');
            for (i, moniker) in self.type_refs.iter().enumerate() {
                let _ = writeln!(self.out, "t${} {}", i, moniker);
            }
        }
        renumber(&self.out)
    }
}

/// Returns a node's arguments, in the order the datatype lists them.
/// An argument that says nothing is left out: an inner join's kind, a
/// join's `true` condition, an empty aggregate list, and the `all` of a
/// set operator that does keep duplicates.
fn args(rel: &Rel) -> Vec<String> {
    match rel {
        Rel::Filter(_, condition) => vec![format!("{}", condition)],
        Rel::IfEmpty(_, value) => vec![format!("{}", value)],
        Rel::Project(_, e) | Rel::Sort(_, e) => vec![format!("{}", e)],
        Rel::Skip(_, n) | Rel::Take(_, n) => vec![format!("{}", n)],
        Rel::Unorder(_) => vec![],
        Rel::Group(_, keys, aggregates) => {
            let mut v = vec![labelled(keys)];
            if !aggregates.is_empty() {
                v.push(labelled(aggregates));
            }
            v
        }
        Rel::Join(kind, binder, condition, _, _) => {
            let mut v = Vec::new();
            if let Some(name) = kind.name() {
                v.push(name.to_string());
            }
            if let Some(name) = binder {
                v.push(name.clone());
            }
            if !is_true(condition) {
                v.push(format!("{}", condition));
            }
            v
        }
        Rel::Except(distinct, _)
        | Rel::Intersect(distinct, _)
        | Rel::Union(distinct, _) => {
            if *distinct {
                vec![]
            } else {
                vec!["all".to_string()]
            }
        }
    }
}

/// Renders a list of labelled expressions, as a `group`'s keys and
/// aggregates are written.
fn labelled(items: &[(Label, Expr)]) -> String {
    items
        .iter()
        .map(|(label, e)| format!("{} = {}", label, e))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Returns whether an expression is the literal `true`, which a join
/// omits.
fn is_true(exp: &Expr) -> bool {
    matches!(exp, Expr::Literal(_, Val::Bool(true)))
}

/// Renumbers the generated names in `text`, each prefix in its own
/// sequence, from zero, in order of first occurrence.
///
/// A binder takes whatever number its maker's counter gave it --
/// uniqueness is all allocation owes -- so `v$123`, `v$110`, `v$200`,
/// `v$110` print as `v$0`, `v$1`, `v$2`, `v$1`. Doing it here, on the
/// whole text at once, is what makes the text depend on the query and
/// nothing else, and is why a tree nested in another tree's expressions
/// continues the enclosing sequence rather than starting again.
///
/// A `$` cannot occur in an identifier the query wrote, so a generated
/// name cannot capture one. Text inside a string literal is left alone,
/// because a string is a value and not a name.
fn renumber(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut counters: HashMap<String, HashMap<String, usize>> = HashMap::new();
    let bytes: Vec<char> = text.chars().collect();
    let mut i = 0;
    let mut in_string = false;
    while i < bytes.len() {
        let c = bytes[i];
        if in_string {
            out.push(c);
            if c == '\\' && i + 1 < bytes.len() {
                i += 1;
                out.push(bytes[i]);
            } else if c == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        if c == '"' {
            in_string = true;
            out.push(c);
            i += 1;
            continue;
        }
        // A generated name is a run of lower-case letters, a `$`, and
        // digits, and is not preceded by a character an identifier could
        // continue from.
        if c.is_ascii_lowercase()
            && (i == 0 || !is_name_char(bytes[i - 1]))
            && let Some((prefix, digits, end)) = generated_name(&bytes, i)
        {
            let seq = counters.entry(prefix.clone()).or_default();
            let next = seq.len();
            let n = *seq.entry(digits).or_insert(next);
            let _ = write!(out, "{}${}", prefix, n);
            i = end;
            continue;
        }
        out.push(c);
        i += 1;
    }
    out
}

/// Returns whether `c` can occur in an identifier, so that a generated
/// name is not recognised in the middle of one.
fn is_name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\'' || c == '$'
}

/// Reads a generated name at `i`: a lower-case prefix, a `$`, and
/// digits. Returns the prefix, the digits, and where the name ends.
fn generated_name(chars: &[char], i: usize) -> Option<(String, String, usize)> {
    let mut j = i;
    while j < chars.len() && chars[j].is_ascii_lowercase() {
        j += 1;
    }
    if j == i || j >= chars.len() || chars[j] != '$' {
        return None;
    }
    let prefix: String = chars[i..j].iter().collect();
    let start = j + 1;
    let mut k = start;
    while k < chars.len() && chars[k].is_ascii_digit() {
        k += 1;
    }
    if k == start {
        return None;
    }
    // A name the query wrote cannot contain `$`, so what follows the
    // digits must not continue an identifier.
    if k < chars.len() && is_name_char(chars[k]) {
        return None;
    }
    Some((prefix, chars[start..k].iter().collect(), k))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::core::{JoinKind, Kind};
    use crate::compile::span::Span;
    use crate::compile::types::{Label, PrimitiveType, Type};
    use crate::eval::val::Val;
    use std::collections::BTreeMap;
    use std::rc::Rc;

    fn int() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Int))
    }

    fn bool_() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Bool))
    }

    fn id(name: &str, t: Rc<Type>) -> Expr {
        Expr::Identifier(t, name.to_string())
    }

    fn t() -> Expr {
        Expr::Literal(bool_(), Val::Bool(true))
    }

    fn node(rel: Rel) -> Expr {
        let t = rel.derive_type().expect("derives a type");
        Expr::Rel(t, Box::new(rel))
    }

    /// A record type wide enough to need a reference.
    fn dept() -> Rc<Type> {
        let mut fields = BTreeMap::new();
        fields.insert(Label::String("deptno".to_string()), int());
        fields.insert(
            Label::String("dname".to_string()),
            Rc::new(Type::Primitive(PrimitiveType::String)),
        );
        Rc::new(Type::Record(false, fields))
    }

    /// One node per line, inputs two spaces further in, and the leaf is
    /// an ordinary expression.
    #[test]
    fn a_node_a_line_and_its_inputs_below_it() {
        let tree = node(Rel::Filter(
            Box::new(id("r", Kind::List.apply(int()))),
            Box::new(t()),
        ));
        assert_eq!(plan(&tree, false), "filter [true]\n  r\n");
    }

    /// Every node line ends in its collection type.
    #[test]
    fn with_types_every_node_says_its_type() {
        let tree = node(Rel::Filter(
            Box::new(id("r", Kind::List.apply(int()))),
            Box::new(t()),
        ));
        assert_eq!(
            plan(&tree, true),
            "filter [true] : int list\n  r : int list\n"
        );
    }

    /// An argument that says nothing is left out: an inner join's kind,
    /// and a `true` condition.
    #[test]
    fn an_absent_argument_is_omitted() {
        let left = id("a", Kind::List.apply(int()));
        let right = id("b", Kind::List.apply(int()));
        let inner = node(Rel::Join(
            JoinKind::Inner,
            None,
            Box::new(t()),
            Box::new(left.clone()),
            Box::new(right.clone()),
        ));
        assert_eq!(plan(&inner, false), "join\n  a\n  b\n");

        // A left join says so, and a binder prints before the
        // condition.
        let outer = node(Rel::Join(
            JoinKind::Left,
            Some("v$7".to_string()),
            Box::new(id("p", bool_())),
            Box::new(left),
            Box::new(right),
        ));
        assert_eq!(plan(&outer, false), "join [left] [v$0] [p]\n  a\n  b\n");
    }

    /// A set operator says `all` when it keeps duplicates, and nothing
    /// when it does not.
    #[test]
    fn a_set_operator_says_whether_it_keeps_duplicates() {
        let inputs = vec![
            id("a", Kind::List.apply(int())),
            id("b", Kind::List.apply(int())),
        ];
        let all = node(Rel::Union(false, inputs.clone()));
        assert_eq!(plan(&all, false), "union [all]\n  a\n  b\n");
        let distinct = node(Rel::Union(true, inputs));
        assert_eq!(plan(&distinct, false), "union\n  a\n  b\n");
    }

    /// A group writes its keys, and its aggregates where it has any.
    #[test]
    fn a_group_writes_its_keys_and_aggregates() {
        let input = id("r", Kind::Bag.apply(int()));
        let keys =
            vec![(Label::String("k".to_string()), Expr::Input(int(), 0))];
        let with_aggregates = node(Rel::Group(
            Box::new(input.clone()),
            keys.clone(),
            vec![(Label::String("c".to_string()), id("n", int()))],
        ));
        assert_eq!(
            plan(&with_aggregates, false),
            "group [k = $0] [c = n]\n  r\n"
        );
        // No aggregates, so no second argument. This is `distinct`.
        let without = node(Rel::Group(Box::new(input), keys, vec![]));
        assert_eq!(plan(&without, false), "group [k = $0]\n  r\n");
    }

    /// A type longer than the limit prints as a reference, and once in
    /// a legend after a blank line; two nodes of the same type share
    /// the reference.
    #[test]
    fn a_long_type_prints_in_a_legend() {
        let input = id("depts", Kind::Bag.apply(dept()));
        let tree = node(Rel::Filter(Box::new(input), Box::new(t())));
        assert_eq!(
            plan(&tree, true),
            "filter [true] : t$0\n  \
             depts : t$0\n\
             \n\
             t$0 {deptno:int, dname:string} bag\n"
        );
    }

    /// The binders the compiler generated are numbered by first
    /// occurrence, so the text depends on the query and nothing else --
    /// and each prefix runs in its own sequence.
    #[test]
    fn generated_binders_are_renumbered() {
        assert_eq!(renumber("v$123 v$110 v$200 v$110"), "v$0 v$1 v$2 v$1");
        // Each prefix has its own sequence, so a tree's `v$` and a
        // lowering's `w$` do not interleave.
        assert_eq!(renumber("v$9 w$4 v$3 w$4"), "v$0 w$0 v$1 w$0");
        // A name the query wrote has no `$`, and is left alone.
        assert_eq!(renumber("deptno v$5 e"), "deptno v$0 e");
        // A string is a value, not a name.
        assert_eq!(renumber("\"v$9\" v$9"), "\"v$9\" v$0");
    }

    /// A tree nested inside another tree's expressions continues the
    /// enclosing text's numbering rather than starting again. An
    /// implementation that concatenated what its children returned
    /// would restart at zero, and would do it silently.
    #[test]
    fn a_nested_tree_continues_the_numbering() {
        let inner = node(Rel::Filter(
            Box::new(id("b", Kind::List.apply(int()))),
            Box::new(id("v$40", bool_())),
        ));
        let outer = node(Rel::Filter(
            Box::new(id("a", Kind::List.apply(int()))),
            Box::new(Expr::Apply(
                bool_(),
                Box::new(id("nonEmpty", bool_())),
                Box::new(Expr::Let(
                    Kind::List.apply(int()),
                    vec![],
                    Box::new(inner),
                )),
                Span::new(""),
            )),
        ));
        let text = plan(&outer, false);
        assert!(text.contains("v$0"), "renumbered from zero: {}", text);
        assert!(!text.contains("v$40"), "not the allocated number: {}", text);
    }
}
