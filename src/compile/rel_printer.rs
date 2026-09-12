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
use crate::compile::free_finder::free_names_in;
use crate::compile::lindig::{self, Doc};
use crate::compile::types::{Label, Type};
use crate::eval::val::Val;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;
use std::iter::once;
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
pub fn plan(exp: &Expr, with_types: bool, line_width: usize) -> String {
    // A relation reached from inside an expression prints as a
    // reference, and `Display` is what prints it. Rust's `Display`
    // carries no state of its own, so the list the reference goes into
    // lives here, where both this function and `Display` can reach it,
    // and stands for the writer morel-java threads through its
    // `unparse`. It is put back afterwards, so an expression printed
    // anywhere else prints as it always did.
    let previous = FRAGMENTS.with(|cell| {
        cell.replace(Some(Fragments {
            outer: free_names_in(exp),
            index: HashMap::new(),
            defs: Vec::new(),
        }))
    });
    let mut w = Writer::new(with_types, line_width);
    w.node(exp, 0);
    let text = w.finish();
    FRAGMENTS.with(|cell| cell.replace(previous));
    text
}

thread_local! {
    /// The relations broken out of the plan being printed, or `None`
    /// when no plan is being printed.
    static FRAGMENTS: RefCell<Option<Fragments>> =
        const { RefCell::new(None) };
}

/// The relations a plan broke out of the expressions they appeared in.
struct Fragments {
    /// What is bound outside the plan. A fragment declares what it
    /// reads from outside itself, but only what a reader of the plan
    /// could not otherwise resolve: `scott` is bound outside the whole
    /// plan, and every fragment would name it.
    outer: BTreeSet<String>,
    /// Where each relation sits in `defs`, by its address in the tree.
    /// Addressed rather than compared: two structurally equal
    /// subqueries are two subqueries, and giving them one reference
    /// would say they are one.
    index: HashMap<usize, usize>,
    /// The relations broken out, in the order they were first referred
    /// to, each with the text that stands for it.
    defs: Vec<(Rc<Expr>, String)>,
}

/// Returns the reference a relation prints as, breaking it out of the
/// plan if this is the first mention of it, or `None` where no plan is
/// being printed.
///
/// Asked when the relation is first referred to, which is the only
/// moment it needs to be known and the only moment we know the relation
/// is being broken out at all.
pub(crate) fn rel_ref(exp: &Expr) -> Option<String> {
    FRAGMENTS.with(|cell| {
        let mut slot = cell.borrow_mut();
        let fragments = slot.as_mut()?;
        let key = exp as *const Expr as usize;
        if let Some(i) = fragments.index.get(&key) {
            return Some(fragments.defs[*i].1.clone());
        }
        let i = fragments.defs.len();
        let text = header(i, exp, &fragments.outer);
        fragments.index.insert(key, i);
        fragments.defs.push((Rc::new(exp.clone()), text.clone()));
        Some(text)
    })
}

/// Returns the `i`th relation a plan broke out, and its header.
fn fragment(i: usize) -> Option<(Rc<Expr>, String)> {
    FRAGMENTS.with(|cell| {
        let slot = cell.borrow();
        let fragments = slot.as_ref()?;
        fragments
            .defs
            .get(i)
            .map(|(rel, text)| (Rc::clone(rel), text.clone()))
    })
}

/// Returns the text that stands for a fragment, at the reference and at
/// the definition alike: `r$N`, or `r$N[v$0, v$1]` where it reads
/// something from outside itself.
///
/// The list is transitive without trying, because a fragment nested
/// inside this one is part of its subtree however far away it is
/// printed, and its free names are free here too.
///
/// The order here is provisional: [`renumber`] settles it, once the
/// binders have the numbers the text gives them rather than the ones
/// their maker handed out.
fn header(i: usize, exp: &Expr, outer: &BTreeSet<String>) -> String {
    let free = free_names_in(exp);
    let mut names: Vec<&str> = free
        .iter()
        .filter(|name| !outer.contains(*name))
        .map(String::as_str)
        .collect();
    names.sort_by(|a, b| compare_generated(a, b));
    if names.is_empty() {
        format!("r${}", i)
    } else {
        format!("r${}[{}]", i, names.join(", "))
    }
}

/// Orders generated names by their number rather than as text, so that
/// `v$2` comes before `v$10`.
fn compare_generated(a: &str, b: &str) -> Ordering {
    match (a.find('$'), b.find('$')) {
        (Some(i), Some(j)) if i == j && a[..i] == b[..j] => {
            match (a[i + 1..].parse::<usize>(), b[j + 1..].parse::<usize>()) {
                (Ok(m), Ok(n)) => m.cmp(&n),
                _ => a.cmp(b),
            }
        }
        _ => a.cmp(b),
    }
}

/// Builds the text of one plan.
///
/// There is one of these per plan, not one per node: the numbering
/// sequences span the whole text, a tree nested inside another tree's
/// expressions included.
struct Writer {
    out: String,
    with_types: bool,
    /// Width at which a node's own line wraps, the session's
    /// `lineWidth`. Nothing else in the text depends on it: the nodes,
    /// their indentation and every number are the same at any width, so
    /// a plan read at another width is the same plan, folded
    /// differently.
    line_width: usize,
    /// Monikers that have been given a `t$N`, in the order they were
    /// first seen, which is the order they are numbered and listed.
    type_refs: Vec<String>,
}

impl Writer {
    fn new(with_types: bool, line_width: usize) -> Writer {
        Writer {
            out: String::new(),
            with_types,
            line_width,
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
        self.out.push_str(&wrap(&line, indent, self.line_width));
        self.out.push('\n');
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

    /// Returns the finished text: the tree, the fragments broken out
    /// of it, then the legend, then the binders renumbered.
    fn finish(mut self) -> String {
        // The list grows while it is walked, because a fragment may
        // itself hold a relation that has to be broken out. Index, do
        // not iterate.
        let mut i = 0;
        while let Some((rel, text)) = fragment(i) {
            self.out.push('\n');
            let _ = writeln!(self.out, "{} =", text);
            self.node(&rel, 2);
            i += 1;
        }
        if !self.type_refs.is_empty() {
            self.out.push('\n');
            for (i, moniker) in self.type_refs.iter().enumerate() {
                let _ = writeln!(self.out, "t${} {}", i, moniker);
            }
        }
        renumber(&self.out)
    }
}

/// Lays out one node's line, folded if it does not fit.
///
/// A continuation is indented four from the node, which is how a
/// reader -- and a parser -- tells a continuation from a grandchild:
/// after a node at indent *d*, the run of lines at *d + 4* before the
/// first line at *d + 2* belongs to that node.
///
/// The break points are the syntactic ones the text shows: before a
/// conjunction's `andalso` or `orelse`, and after the comma between a
/// record's fields. They are found in the rendered line rather than
/// built into it, so that a line which fits is character for character
/// the line an unwrapped printer would have written.
fn wrap(line: &str, indent: usize, line_width: usize) -> String {
    let indented = format!("{:indent$}{}", "", line, indent = indent);
    if indented.len() <= line_width {
        return indented;
    }
    let pieces = break_points(line);
    if pieces.len() < 2 {
        return indented;
    }
    let docs: Vec<Doc> = pieces
        .iter()
        .enumerate()
        .flat_map(|(i, piece)| {
            let mut v = Vec::new();
            if i > 0 {
                v.push(lindig::line());
            }
            v.push(lindig::text(piece));
            v
        })
        .collect();
    let doc = lindig::nest(
        (indent + 4) as i32,
        lindig::group(lindig::hcat(
            once(lindig::text(&format!("{:indent$}", "", indent = indent)))
                .chain(docs)
                .collect(),
        )),
    );
    lindig::render(line_width as i32, doc)
}

/// Splits a node's line at the points a fold may go: before a
/// conjunction's keyword at the top level, and after the comma between
/// the fields of a record that the line's argument opens with.
///
/// A piece keeps the text that precedes its break, so joining the
/// pieces with a single space gives the line back.
fn break_points(line: &str) -> Vec<String> {
    let chars: Vec<char> = line.chars().collect();
    let mut pieces = Vec::new();
    let mut start = 0;
    let mut depth = 0i32;
    let mut in_string = false;
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if in_string {
            if c == '\\' {
                i += 2;
                continue;
            }
            if c == '"' {
                in_string = false;
            }
            i += 1;
            continue;
        }
        match c {
            '"' => in_string = true,
            '(' | '[' | '{' => depth += 1,
            ')' | ']' | '}' => depth -= 1,
            _ => {}
        }
        // ` andalso ` or ` orelse ` joins two conditions, and the fold
        // goes before the keyword.
        if c == ' ' && depth == 1 {
            for keyword in ["andalso ", "orelse "] {
                if chars[i + 1..]
                    .starts_with(&keyword.chars().collect::<Vec<_>>()[..])
                {
                    pieces.push(chars[start..i].iter().collect());
                    start = i + 1;
                    break;
                }
            }
        }
        // A record's fields are separated by ", ", and the fold goes
        // after the comma.
        if c == ',' && depth == 2 && chars.get(i + 1) == Some(&' ') {
            pieces.push(chars[start..=i].iter().collect());
            start = i + 2;
            i += 2;
            continue;
        }
        i += 1;
    }
    if start < chars.len() {
        pieces.push(chars[start..].iter().collect());
    }
    pieces
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
            let n = renumbered(&prefix, &digits, &mut counters);
            let _ = write!(out, "{}${}", prefix, n);
            i = end;
            // A fragment says what it reads from outside itself, and
            // the names are written in order -- an order that only
            // exists once they have been renumbered, because it is the
            // text's numbering they are in order of and not their
            // maker's.
            if prefix == "r"
                && bytes.get(i) == Some(&'[')
                && let Some((names, close)) = header_names(&bytes, i)
            {
                let mut renamed: Vec<String> = names
                    .iter()
                    .map(|name| match name.split_once('$') {
                        Some((p, d)) if is_digits(d) => {
                            format!("{}${}", p, renumbered(p, d, &mut counters))
                        }
                        _ => name.clone(),
                    })
                    .collect();
                renamed.sort_by(|a, b| compare_generated(a, b));
                let _ = write!(out, "[{}]", renamed.join(", "));
                i = close + 1;
            }
            continue;
        }
        out.push(c);
        i += 1;
    }
    out
}

/// Gives a generated name the number the text gives it: its position
/// among the names that share its prefix, counting from zero in order
/// of first occurrence.
fn renumbered(
    prefix: &str,
    digits: &str,
    counters: &mut HashMap<String, HashMap<String, usize>>,
) -> usize {
    let seq = counters.entry(prefix.to_string()).or_default();
    let next = seq.len();
    *seq.entry(digits.to_string()).or_insert(next)
}

/// Returns whether `s` is a non-empty run of digits.
fn is_digits(s: &str) -> bool {
    !s.is_empty() && s.chars().all(|c| c.is_ascii_digit())
}

/// Reads the bracketed name list of a fragment header, given the index
/// of its `[`. Returns the names and where the `]` is.
fn header_names(chars: &[char], i: usize) -> Option<(Vec<String>, usize)> {
    let mut names = Vec::new();
    let mut name = String::new();
    let mut j = i + 1;
    while j < chars.len() {
        let c = chars[j];
        if c == ']' {
            if name.is_empty() {
                return None;
            }
            names.push(name);
            return Some((names, j));
        }
        if c == ',' && chars.get(j + 1) == Some(&' ') {
            if name.is_empty() {
                return None;
            }
            names.push(name.clone());
            name.clear();
            j += 2;
            continue;
        }
        if !is_name_char(c) {
            return None;
        }
        name.push(c);
        j += 1;
    }
    None
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
    use crate::compile::core::{Decl, JoinKind, Kind, Pat, ValBind};
    use crate::compile::library::BuiltInFunction;
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

    fn lit(i: i32) -> Expr {
        Expr::Literal(int(), Val::Int(i))
    }

    /// `a > b`, as an application of the operator.
    fn gt(a: Expr, b: Expr) -> Expr {
        Expr::Apply(
            bool_(),
            Box::new(Expr::Literal(bool_(), Val::Fn(BuiltInFunction::IntGt))),
            Box::new(Expr::Tuple(
                Rc::new(Type::Tuple(vec![int(), int()])),
                vec![a, b],
            )),
            Span::new(""),
        )
    }

    /// `let val name = value in body end`.
    fn let_(name: &str, value: Expr, body: Expr) -> Expr {
        let t = body.type_();
        Expr::Let(
            t,
            vec![Decl::NonRecVal(Box::new(ValBind {
                pat: Pat::Identifier(int(), name.to_string()),
                t: Type::Primitive(PrimitiveType::Int),
                expr: value,
                overload_pat: None,
                span: None,
            }))],
            Box::new(body),
        )
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
        assert_eq!(plan(&tree, false, 78), "filter [true]\n  r\n");
    }

    /// Every node line ends in its collection type.
    #[test]
    fn with_types_every_node_says_its_type() {
        let tree = node(Rel::Filter(
            Box::new(id("r", Kind::List.apply(int()))),
            Box::new(t()),
        ));
        assert_eq!(
            plan(&tree, true, 78),
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
        assert_eq!(plan(&inner, false, 78), "join\n  a\n  b\n");

        // A left join says so, and a binder prints before the
        // condition.
        let outer = node(Rel::Join(
            JoinKind::Left,
            Some("v$7".to_string()),
            Box::new(id("p", bool_())),
            Box::new(left),
            Box::new(right),
        ));
        assert_eq!(
            plan(&outer, false, 78),
            "join [left] [v$0] [p]\n  a\n  b\n"
        );
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
        assert_eq!(plan(&all, false, 78), "union [all]\n  a\n  b\n");
        let distinct = node(Rel::Union(true, inputs));
        assert_eq!(plan(&distinct, false, 78), "union\n  a\n  b\n");
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
            plan(&with_aggregates, false, 78),
            "group [k = $0] [c = n]\n  r\n"
        );
        // No aggregates, so no second argument. This is `distinct`.
        let without = node(Rel::Group(Box::new(input), keys, vec![]));
        assert_eq!(plan(&without, false, 78), "group [k = $0]\n  r\n");
    }

    /// A type longer than the limit prints as a reference, and once in
    /// a legend after a blank line; two nodes of the same type share
    /// the reference.
    #[test]
    fn a_long_type_prints_in_a_legend() {
        let input = id("depts", Kind::Bag.apply(dept()));
        let tree = node(Rel::Filter(Box::new(input), Box::new(t())));
        assert_eq!(
            plan(&tree, true, 78),
            "filter [true] : t$0\n  \
             depts : t$0\n\
             \n\
             t$0 {deptno:int, dname:string} bag\n"
        );
    }

    /// A node's line folds where it does not fit, and its continuation
    /// is indented four from the node, which is how a reader tells a
    /// continuation from a grandchild.
    #[test]
    fn a_line_folds_four_from_the_node() {
        let line = "filter [#deptno (#2 $0) = #deptno (#1 $0) \
                    andalso #job (#2 $0) = \"PRESIDENT\"] : t$1";
        // At a width that holds it, nothing moves.
        assert_eq!(wrap(line, 2, 200), format!("  {}", line));
        // At 78 it folds before the `andalso`, at 2 + 4.
        assert_eq!(
            wrap(line, 2, 78),
            "  filter [#deptno (#2 $0) = #deptno (#1 $0)\n      \
             andalso #job (#2 $0) = \"PRESIDENT\"] : t$1"
        );
    }

    /// A record's fields fold after the comma, and all of them fold
    /// together: the fold is one decision, not one per field.
    #[test]
    fn a_record_folds_after_each_comma() {
        let line = "project [{comm = #comm (#3 $0), dname = #dname (#1 $0), \
                    ename = #ename (#2 $0)}] : t$0";
        assert_eq!(
            wrap(line, 0, 78),
            "project [{comm = #comm (#3 $0),\n    \
             dname = #dname (#1 $0),\n    \
             ename = #ename (#2 $0)}] : t$0"
        );
    }

    /// The pieces a fold may go between join back into the line, so a
    /// line that fits is the line an unwrapped printer would write.
    #[test]
    fn the_pieces_give_the_line_back() {
        for line in [
            "filter [a andalso b] : int list",
            "project [{a = 1, b = 2}] : t$0",
            "join : t$1",
            // A comma inside a string is not a break point.
            "filter [$0 = \"a, b\"] : string list",
        ] {
            assert_eq!(break_points(line).join(" "), line, "{}", line);
        }
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

    /// A relation reached from inside an expression prints as a
    /// reference, and its lines follow the tree. This is `spec.md`
    /// §6.4's first example.
    #[test]
    fn a_relation_inside_an_expression_is_broken_out() {
        let inner = node(Rel::Filter(
            Box::new(Expr::List(Kind::List.apply(int()), vec![lit(3), lit(4)])),
            Box::new(gt(Expr::Input(int(), 0), id("v$5", int()))),
        ));
        let mut fields = BTreeMap::new();
        fields.insert(Label::String("i".to_string()), int());
        fields.insert(Label::String("ys".to_string()), Kind::List.apply(int()));
        let element = Rc::new(Type::Record(false, fields));
        let tree = node(Rel::Project(
            Box::new(Expr::List(Kind::List.apply(int()), vec![lit(1), lit(2)])),
            Box::new(let_(
                "v$5",
                Expr::Input(int(), 0),
                Expr::Tuple(element, vec![Expr::Input(int(), 0), inner]),
            )),
        ));
        assert_eq!(
            plan(&tree, true, 78),
            "project [let val v$0 = $0 in \
             {i = $0, ys = r$0[v$0]} end] : t$0\n  \
             [1, 2] : int list\n\
             \n\
             r$0[v$0] =\n  \
             filter [$0 > v$0] : int list\n    \
             [3, 4] : int list\n\
             \n\
             t$0 {i:int, ys:int list} list\n"
        );
    }

    /// A fragment declares what it reads from outside itself, and the
    /// list is transitive: `r$0` names `v$0` though nothing in its own
    /// lines mentions it, because the fragment nested inside it does.
    /// `spec.md` §6.4's second example, and the reason the list must be
    /// worked out before anything is written.
    #[test]
    fn a_fragment_declares_what_it_reads_transitively() {
        let pairs = || id("pairs", Kind::List.apply(int()));
        let innermost = node(Rel::Filter(
            Box::new(pairs()),
            Box::new(gt(Expr::Input(int(), 0), id("v$5", int()))),
        ));
        let middle = node(Rel::Filter(
            Box::new(pairs()),
            Box::new(Expr::Apply(
                bool_(),
                Box::new(id("nonEmpty", bool_())),
                Box::new(innermost),
                Span::new(""),
            )),
        ));
        let tree = node(Rel::Filter(
            Box::new(id("xs", Kind::List.apply(int()))),
            Box::new(let_(
                "v$5",
                Expr::Input(int(), 0),
                Expr::Apply(
                    bool_(),
                    Box::new(id("nonEmpty", bool_())),
                    Box::new(middle),
                    Span::new(""),
                ),
            )),
        ));
        assert_eq!(
            plan(&tree, false, 200),
            "filter [let val v$0 = $0 in nonEmpty (r$0[v$0]) end]\n  \
             xs\n\
             \n\
             r$0[v$0] =\n  \
             filter [nonEmpty (r$1[v$0])]\n    \
             pairs\n\
             \n\
             r$1[v$0] =\n  \
             filter [$0 > v$0]\n    \
             pairs\n"
        );
    }

    /// Two structurally equal subqueries are two subqueries, and giving
    /// them one reference would say they are one.
    #[test]
    fn equal_fragments_are_still_two_fragments() {
        let one = || {
            node(Rel::Filter(
                Box::new(id("xs", Kind::List.apply(int()))),
                Box::new(t()),
            ))
        };
        let tree = node(Rel::Filter(
            Box::new(id("ys", Kind::List.apply(int()))),
            Box::new(Expr::Tuple(
                Rc::new(Type::Tuple(vec![
                    Kind::List.apply(int()),
                    Kind::List.apply(int()),
                ])),
                vec![one(), one()],
            )),
        ));
        let text = plan(&tree, false, 200);
        assert!(text.starts_with("filter [(r$0, r$1)]\n"), "{}", text);
        assert_eq!(text.matches("filter [true]").count(), 2, "{}", text);
    }

    /// A fragment's names are in the order the *text* numbers them, not
    /// the order their maker handed out, so the sort happens after the
    /// renumbering and not before it.
    #[test]
    fn a_fragments_names_are_sorted_after_renumbering() {
        // `v$5` is seen first, so it is `v$0`; the header lists it
        // second, and comes out first.
        assert_eq!(renumber("v$5 v$3 r$0[v$3, v$5]"), "v$0 v$1 r$0[v$0, v$1]");
        // By number and not as text: `v$2` comes before `v$10`.
        assert_eq!(compare_generated("v$2", "v$10"), Ordering::Less);
        // A name the query wrote compares as text.
        assert_eq!(compare_generated("b", "a"), Ordering::Greater);
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
        let text = plan(&outer, false, 78);
        assert!(text.contains("v$0"), "renumbered from zero: {}", text);
        assert!(!text.contains("v$40"), "not the allocated number: {}", text);
    }
}
