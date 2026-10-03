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

use crate::compile::free_finder;
use crate::compile::library::BuiltInFunction;
use crate::compile::lindig::{
    Doc, beside, group, hcat, line, punctuate, render, text,
};
use crate::compile::postfix::peel_type;
use crate::compile::rel_lowerer;
use crate::compile::rel_printer;
use crate::compile::span::Span;
use crate::compile::type_env::Id;
use crate::compile::types::{self, Checks, Label, Type};
use crate::eval::val::Val;
use crate::syntax::ast::JoinType;
use crate::syntax::parser;
use std::cell::{Cell, RefCell};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::ops::Deref;
use std::rc::Rc;

/// Expression.
#[derive(Clone, Debug)]
pub enum Expr {
    Literal(Rc<Type>, Val),
    Identifier(Rc<Type>, String),

    /// `RecordSelector(type, slot)` is a function that returns the `slot`th
    /// field of a record or tuple. `type` is a function type, `record_type`
    /// -> `field_type`.
    RecordSelector(Rc<Type>, usize),
    Current(Rc<Type>),
    Ordinal(Rc<Type>),
    // 'over'; the `Span` is the position of the aggregate call (e.g.
    // `max over e.sal`), used to raise `Empty` there for an empty `max`/`min`.
    Aggregate(Rc<Type>, Box<Expr>, Box<Expr>, Span),

    /// `Apply(f, a)` represents `f a`, applying a function to an argument.
    Apply(Rc<Type>, Box<Expr>, Box<Expr>, Span),

    // Control structures. (There is no 'If'; use 'Case' instead.)
    Case(Rc<Type>, Box<Expr>, Vec<Match>, Span),
    Let(Rc<Type>, Vec<Decl>, Box<Expr>),
    Fn(Rc<Type>, Vec<Match>, Span),

    /// A node of a relational tree; see [`Rel`]. `t` is the collection
    /// type the node produces, so a node is an expression like any
    /// other and a query may appear wherever an expression may.
    #[allow(dead_code)]
    Rel(Rc<Type>, Box<Rel>),

    /// `raise e` — evaluates `e` to an `exn` value, then throws.
    /// `type` is the type of the surrounding context (since `raise`
    /// never returns).
    Raise(Rc<Type>, Box<Expr>, Span),

    // Constructors for data structures
    Tuple(Rc<Type>, Vec<Expr>), // e.g. `(x, y, z)`
    List(Rc<Type>, Vec<Expr>),  // e.g. `[x, y, z]`

    // Relational expressions
    From(Rc<Type>, Vec<Step>),

    /// Placeholder for "all values of type `t`" — produced by lowering
    /// `from p` (no `in`) when the variable's source has not yet been
    /// resolved by predicate inversion. The compile-time checker
    /// rejects programs that still contain `Extent` after the
    /// expander pass; for now (no expander), any program that lowers
    /// to an `Extent` errors with "unbounded variable in `from`".
    /// `span` points at the source `from p` step so the runtime
    /// "pattern not grounded" error can pinpoint the offending
    /// site. `names` are what the scan's pattern bound, which a
    /// tree, whose leaves are not named, reads back; see
    /// [extent_names].
    Extent(Rc<Type>, Span, Vec<String>),
}

/// Returns the body of a chain of `let` expressions; `exp` itself if it
/// is not a `let`.
///
/// A record with modifiers becomes one `let` per modifier whose body is
/// the record the last one produced, so a `yield` step's fields are
/// those of that record.
pub(crate) fn let_body(exp: &Expr) -> &Expr {
    let mut e = exp;
    while let Expr::Let(_, _, body) = e {
        e = body;
    }
    e
}

impl Expr {
    /// Creates a tuple expression.
    pub(crate) fn new_tuple(args: &[Expr]) -> Self {
        let types = args.iter().map(Expr::type_).collect::<Vec<_>>();
        let arg_type = Type::Tuple(types);
        Expr::Tuple(Rc::new(arg_type), args.to_vec())
    }

    /// Returns the implicit label for this expression, if any.
    pub fn implicit_label(&self) -> Option<String> {
        match self {
            Expr::Apply(_, fx, _, _) => {
                if let Expr::RecordSelector(t, slot) = fx.as_ref() {
                    let (param_type, _) = t.expect_fn();
                    param_type.field_name(*slot).map(ToString::to_string)
                } else {
                    None
                }
            }
            Expr::Aggregate(_, left, _, _) => left.implicit_label(),
            Expr::Identifier(_, name) => Some(name.clone()),
            Expr::Literal(_, Val::Fn(f)) => Some(f.label_name().to_string()),
            _ => None,
        }
    }

    /// Returns this expression's type.
    pub fn type_(&self) -> Rc<Type> {
        match self {
            // lint: sort until '#}' where '##Expr::'
            Expr::Aggregate(t, _, _, _) => t.clone(),
            Expr::Apply(t, _, _, _) => t.clone(),
            Expr::Case(t, _, _, _) => t.clone(),
            Expr::Current(t) => t.clone(),
            Expr::Extent(t, ..) => t.clone(),
            Expr::Fn(t, _, _) => t.clone(),
            Expr::From(t, _) => t.clone(),
            Expr::Identifier(t, _) => t.clone(),
            Expr::Let(t, _, _) => t.clone(),
            Expr::List(t, _) => t.clone(),
            Expr::Literal(t, _) => t.clone(),
            Expr::Ordinal(t) => t.clone(),
            Expr::Raise(t, _, _) => t.clone(),
            Expr::RecordSelector(t, _) => t.clone(),
            Expr::Rel(t, _) => t.clone(),
            Expr::Tuple(t, _) => t.clone(),
        }
    }

    /// Returns whether this expression, or any sub-expression, references
    /// an `ordinal` that counts *this* step's rows.
    ///
    /// A nested query is traversed only where it is evaluated once per
    /// execution rather than once per row -- the collection its first step
    /// scans, a `take` or `skip` count, an operand of `union`, `except` or
    /// `intersect`. An `ordinal` there counts the enclosing rows, so this
    /// step must supply it; anywhere else in the nested query it counts
    /// that query's own rows, which the nested query supplies itself.
    pub(crate) fn uses_ordinal(&self) -> bool {
        match self {
            Expr::Ordinal(_) => true,
            Expr::From(_, steps) => {
                steps.iter().enumerate().any(|(i, step)| match &step.kind {
                    StepKind::Scan(_, e, _) if i == 0 => e.uses_ordinal(),
                    StepKind::Skip(e) | StepKind::Take(e) => e.uses_ordinal(),
                    StepKind::Except(_, exprs)
                    | StepKind::Intersect(_, exprs)
                    | StepKind::Union(_, exprs) => {
                        exprs.iter().any(Expr::uses_ordinal)
                    }
                    _ => false,
                })
            }
            Expr::Aggregate(_, arg, agg, _) => {
                arg.uses_ordinal() || agg.uses_ordinal()
            }
            Expr::Apply(_, f, a, _) => f.uses_ordinal() || a.uses_ordinal(),
            Expr::Case(_, e, matches, _) => {
                e.uses_ordinal()
                    || matches.iter().any(|m| m.expr.uses_ordinal())
            }
            Expr::Fn(_, matches, _) => {
                matches.iter().any(|m| m.expr.uses_ordinal())
            }
            Expr::Let(_, decls, e) => {
                decls.iter().any(Decl::uses_ordinal) || e.uses_ordinal()
            }
            Expr::List(_, exprs) | Expr::Tuple(_, exprs) => {
                exprs.iter().any(Expr::uses_ordinal)
            }
            _ => false,
        }
    }

    /// Returns whether an `ordinal` in this expression sits inside a
    /// function, and so would be read from that function's own frame
    /// rather than the one holding the counter.
    ///
    /// Such a read has to come from the row instead: a field is captured
    /// by a closure like any other variable, a frame slot is not.
    pub(crate) fn ordinal_under_fn(&self) -> bool {
        fn walk(e: &Expr, in_fn: bool) -> bool {
            match e {
                Expr::Ordinal(_) => in_fn,
                Expr::Fn(_, matches, _) => {
                    matches.iter().any(|m| walk(&m.expr, true))
                }
                Expr::Aggregate(_, a, b, _) | Expr::Apply(_, a, b, _) => {
                    walk(a, in_fn) || walk(b, in_fn)
                }
                Expr::Case(_, e, matches, _) => {
                    walk(e, in_fn)
                        || matches.iter().any(|m| walk(&m.expr, in_fn))
                }
                Expr::Let(_, decls, e) => {
                    decls.iter().any(|d| decl_walk(d, in_fn)) || walk(e, in_fn)
                }
                Expr::List(_, es) | Expr::Tuple(_, es) => {
                    es.iter().any(|e| walk(e, in_fn))
                }
                Expr::Raise(_, e, _) => walk(e, in_fn),
                _ => false,
            }
        }
        fn decl_walk(d: &Decl, in_fn: bool) -> bool {
            match d {
                Decl::NonRecVal(b) => walk(&b.expr, in_fn),
                Decl::RecVal(binds) => {
                    binds.iter().any(|b| walk(&b.expr, in_fn))
                }
                _ => false,
            }
        }
        walk(self, false)
    }

    /// Returns the steps if this is a From expression.
    pub fn steps(&self) -> Option<&[Step]> {
        match self {
            Expr::From(_, steps) => Some(steps),
            _ => None,
        }
    }

    /// Returns this expression as a document, so that a layout can be
    /// chosen to fit a width. An `andalso` or `orelse` chain is a
    /// group of its own: it stays on one line if it fits, and otherwise
    /// breaks before each connective, which leads its line; the outer
    /// chain breaks before the inner one, so what fits on a line stays
    /// on it. Everything else is laid out as it always was.
    pub fn to_doc(&self) -> Doc {
        self.doc_bounded(0, 0)
    }

    /// Returns this expression as a document, in the operator context
    /// whose precedence bounds are `left` and `right`.
    ///
    /// Only an infix operator reads the bounds; everything else is
    /// bracketed already, or is an atom, and starts its operands in a
    /// fresh context. That is morel-java's `AstNode.unparse(w, left,
    /// right)` with the arms it does not need left out.
    fn doc_bounded(&self, left: u8, right: u8) -> Doc {
        match &self {
            // lint: sort until '#}' where '##Expr::'
            Expr::Aggregate(_, a0, a1, _) => {
                hcat(vec![a0.to_doc(), text(" over "), a1.to_doc()])
            }
            Expr::Apply(_, fx, arg, _) => {
                // `Apply(Lit(Val::Fn(op)), Tuple([a, b]))` is written
                // `a op b` when `op` has an infix form, and as a call
                // otherwise. The set is morel-java's (see
                // `BuiltInFunction::infix_op`), and so is the
                // bracketing: an operand is bracketed where the context
                // binds tighter than the operator does, which keeps
                // `$0 - ($0 - 1)` and drops the brackets from
                // `$0 - 1 + $0`.
                if let Expr::Literal(_, Val::Fn(func)) = fx.as_ref()
                    && let Expr::Tuple(_, args) = arg.as_ref()
                    && args.len() == 2
                    && let Some((op, op_left, op_right)) = func.infix_op()
                    && written_infix(func, op)
                {
                    let wrap = left > op_left || op_right < right;
                    let (left, right) =
                        if wrap { (0, 0) } else { (left, right) };
                    let a = args[0].doc_bounded(left, op_left);
                    let b = args[1].doc_bounded(op_right, right);
                    let doc = if matches!(
                        func,
                        BuiltInFunction::BoolAndAlso
                            | BuiltInFunction::BoolOrElse
                    ) {
                        group(hcat(vec![
                            a,
                            line(),
                            text(&format!("{} ", op)),
                            b,
                        ]))
                    } else {
                        hcat(vec![a, text(&format!(" {} ", op)), b])
                    };
                    if wrap {
                        return hcat(vec![text("("), doc, text(")")]);
                    }
                    return doc;
                }
                // Negation is a prefix operator, written before its one
                // operand, `~ $0`; it binds more tightly than any binary
                // operator, so `~ $0 + 1` needs no brackets and
                // `~ ($0 + 1)` keeps them.
                if let Expr::Literal(_, Val::Fn(func)) = fx.as_ref()
                    && !func.takes_pair()
                    && func
                        .op_name()
                        .unwrap_or_else(|| func.name())
                        .trim_start_matches("op ")
                        == "~"
                {
                    let operand = match arg.as_ref() {
                        Expr::Identifier(_, _) | Expr::Literal(_, _) => {
                            arg.to_doc()
                        }
                        _ => hcat(vec![text("("), arg.to_doc(), text(")")]),
                    };
                    return beside(text("~ "), operand);
                }
                // An argument is bracketed unless it is written as an
                // atom already: a name, a literal, or something that
                // carries its own brackets. `#rev List xs`, but
                // `#flatten Range ([OPEN (0, 10)])`. A function that
                // is not an atom is bracketed too: `(fn i => i >= 1)
                // n`, whose body would otherwise take the argument.
                let fx_doc = if needs_brackets_as_function(fx) {
                    hcat(vec![text("("), fx.to_doc(), text(")")])
                } else {
                    fx.to_doc()
                };
                match arg.as_ref() {
                    Expr::Identifier(_, _)
                    | Expr::Literal(_, _)
                    | Expr::RecordSelector(_, _)
                    | Expr::Tuple(_, _) => {
                        hcat(vec![fx_doc, text(" "), arg.to_doc()])
                    }
                    _ => {
                        hcat(vec![fx_doc, text(" ("), arg.to_doc(), text(")")])
                    }
                }
            }
            Expr::Case(_, e, arms, _) => hcat(vec![
                text("case "),
                e.to_doc(),
                text(" of "),
                matches_doc(arms),
            ]),
            Expr::Current(_) => text("current"),
            Expr::Extent(t, ..) => {
                // The extent of a type is named by the type of its
                // elements: `extent "int"` is every int.
                let elem = element_type(t).unwrap_or_else(|| t.clone());
                text(&format!("extent \"{}\"", elem))
            }
            Expr::Fn(_, arms, _) => beside(text("fn "), matches_doc(arms)),
            Expr::From(_, steps) => beside(text("from"), steps_doc(steps)),
            Expr::Identifier(_, name) => text(name),
            Expr::Let(_, decls, body) => {
                let decls_str = decls
                    .iter()
                    .map(|d| format!("{}", d))
                    .collect::<Vec<_>>()
                    .join("; ");
                hcat(vec![
                    text(&format!("let {} in ", decls_str)),
                    body.to_doc(),
                    text(" end"),
                ])
            }
            Expr::List(_, elems) => {
                enclosed("[", "]", elems.iter().map(Expr::to_doc).collect())
            }
            Expr::Literal(t, lit) => match relation_name(t, lit) {
                // A foreign relation is named, not written out: a
                // plan says where the rows come from, and a table
                // written into it says nothing and hides the rest.
                Some(name) => text(&name),
                None => text(&literal_text(lit)),
            },
            Expr::Ordinal(_) => text("ordinal"),
            Expr::Raise(_, e, _) => beside(text("raise "), e.to_doc()),
            Expr::RecordSelector(t, slot) => {
                // A selector is written by the field it selects: a
                // record's label, or a tuple's ordinal, which is
                // 1-based as it is in the source. `#rev List`, `#1 p`.
                let field = match t.as_ref() {
                    Type::Fn(param_type, _) => match peel_type(param_type) {
                        Type::Record(_, fields) => {
                            fields.keys().nth(*slot).map(|l| match l {
                                Label::String(name) => name.clone(),
                                Label::Ordinal(i) => i.to_string(),
                            })
                        }
                        _ => None,
                    },
                    _ => None,
                };
                match field {
                    Some(name) => text(&parser::selector_text(&name)),
                    None => text(&format!("#{}", slot + 1)),
                }
            }
            Expr::Rel(_, rel) => {
                // A relational operator is the first non-whitespace on
                // its line, and this one would not be, so while a plan
                // is being printed it prints as a reference and its
                // lines go below the tree, where they can be read.
                // Splicing them in here is what made a nested query's
                // plan unparseable: its indentation began again from
                // zero inside the line that held it.
                if let Some(reference) = rel_printer::rel_ref(self) {
                    return text(&reference);
                }
                // Outside a plan -- an error message, a trace -- a node
                // prints on one line, so that a tree built in a test
                // can be read at all.
                let mut docs = vec![text(rel.op_name())];
                for child in rel.children() {
                    docs.push(text(" ("));
                    docs.push(child.to_doc());
                    docs.push(text(")"));
                }
                hcat(docs)
            }
            Expr::Tuple(t, elems) => {
                if let Type::Record(_, type_fields) = t.as_ref() {
                    let fields = type_fields
                        .keys()
                        .zip(elems.iter())
                        .map(|(label, e)| {
                            beside(text(&format!("{} = ", label)), e.to_doc())
                        })
                        .collect();
                    return enclosed("{", "}", fields);
                }
                enclosed("(", ")", elems.iter().map(Expr::to_doc).collect())
            }
        }
    }

    /// Returns this expression as text, laid out to fit `width`.
    pub fn unparse(&self, width: i32) -> String {
        render(width, self.to_doc())
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        // No width: every group is laid out flat, on one line.
        write!(f, "{}", self.unparse(i32::MAX))
    }
}

thread_local! {
    /// The foreign relations a plan names rather than writes out,
    /// each with the type and the rows that identify it.
    static RELATIONS: RefCell<Vec<(String, Rc<Type>, String)>> =
        const { RefCell::new(Vec::new()) };
}

/// Registers a relation that a plan names rather than writes out.
///
/// A foreign relation reaches the plan as the value it holds, because
/// the inliner puts a constant in place of the name that stands for
/// it. Writing a whole table into a plan says nothing about the query
/// and crowds out what does, so the value is recognised on the way
/// out and the name it came from is printed instead.
///
/// A relation is recognised by its type -- a collection of records --
/// and by its rows, so a value that merely has the same shape is
/// written out as any other value is.
pub fn register_relation(name: &str, t: Rc<Type>, value: &Val) {
    if !is_relation_type(&t) {
        return;
    }
    let text = literal_text(value);
    RELATIONS.with(|cell| {
        let mut relations = cell.borrow_mut();
        if !relations.iter().any(|(n, _, _)| n == name) {
            relations.push((name.to_string(), t, text));
        }
    });
}

/// The name a plan gives a value, where it is a registered relation.
fn relation_name(t: &Rc<Type>, value: &Val) -> Option<String> {
    if !is_relation_type(t) {
        return None;
    }
    RELATIONS.with(|cell| {
        let relations = cell.borrow();
        let candidates: Vec<&(String, Rc<Type>, String)> =
            relations.iter().filter(|(_, rt, _)| rt == t).collect();
        if candidates.is_empty() {
            return None;
        }
        let text = literal_text(value);
        candidates
            .iter()
            .find(|(_, _, rows)| *rows == text)
            .map(|(name, _, _)| name.clone())
    })
}

/// Returns whether a type is one a relation has: a collection of
/// records.
fn is_relation_type(t: &Type) -> bool {
    match t {
        Type::Bag(elem) | Type::List(elem) => {
            matches!(elem.as_ref(), Type::Record(_, _))
        }
        _ => false,
    }
}

thread_local! {
    /// Whether the expression being printed has been through the
    /// inliner. Set by `Sys.planEx` around a post-inlining plan; see
    /// [`written_infix`].
    static INLINED: Cell<bool> = const { Cell::new(false) };
}

/// Returns whether the expression being printed has been through the
/// inliner; see [`print_inlined`].
pub fn inlined() -> bool {
    INLINED.with(Cell::get)
}

/// Prints `f` as a plan of an expression the inliner has been through,
/// which is what `Sys.planEx` shows for a phase after inlining.
pub fn print_inlined<T>(f: impl FnOnce() -> T) -> T {
    let previous = INLINED.with(|cell| cell.replace(true));
    let result = f();
    INLINED.with(|cell| cell.set(previous));
    result
}

/// Returns whether an operator is written infix, `$0 - 5`, rather
/// than as a call of the structure member that implements it,
/// `#`-` Int ($0, 5)`.
///
/// Before inlining, morel-java's Core holds the global operator the
/// query wrote, and its printer writes every operator infix. Inlining
/// replaces an overloaded operator with the instance the types chose,
/// which is a structure member, and a member prints as a call; only
/// `+`, the comparisons, `::`, `@`, `andalso` and `orelse`, which its
/// resolver converts back to operators, stay infix. A `Word` member
/// is a member from the start, `#`+` Word (0wxAB, 0wx1)`, because no
/// global operator resolves to it. One function value stands for the
/// global and the member here, so the stage of the plan decides.
pub(crate) fn written_infix(func: &BuiltInFunction, op: &str) -> bool {
    if func.parent() == Some("Word") {
        return false;
    }
    !INLINED.with(Cell::get)
        || matches!(
            op,
            "+" | "="
                | "<>"
                | "<"
                | "<="
                | ">"
                | ">="
                | "::"
                | "@"
                | "andalso"
                | "orelse"
        )
}

/// Returns a literal as a plan writes it. A real that is a whole
/// number keeps its `.0`, `1000.0`, so that it reads back as a real
/// and not an int; a value prints `1000`, and that is a different
/// thing in a different place.
/// Returns whether an expression applied as a function must be written
/// in brackets: one that is not an atom, whose last part would take the
/// argument for its own.
pub(crate) fn needs_brackets_as_function(fx: &Expr) -> bool {
    matches!(
        fx,
        Expr::Fn(..) | Expr::Case(..) | Expr::Raise(..) | Expr::Aggregate(..)
    )
}

fn literal_text(lit: &Val) -> String {
    let s = lit.to_string();
    match lit {
        Val::Real(_) if !s.contains(['.', 'E', 'e', 'i', 'n']) => s + ".0",
        _ => s,
    }
}

/// Returns `docs` between `open` and `close`, separated by `", "`,
/// all on one line.
fn enclosed(open: &str, close: &str, docs: Vec<Doc>) -> Doc {
    let mut all = vec![text(open)];
    all.extend(punctuate(&text(", "), docs));
    all.push(text(close));
    hcat(all)
}

/// Returns the arms of a `case` or `fn`, separated by `|`.
fn matches_doc(arms: &[Match]) -> Doc {
    let docs = arms
        .iter()
        .map(|m| beside(text(&format!("{} => ", m.pat)), m.expr.to_doc()))
        .collect();
    hcat(punctuate(&text(" | "), docs))
}

/// Match in a `case`.
#[derive(Clone, Debug)]
pub struct Match {
    pub pat: Pat,
    pub expr: Expr,
}

impl Display for Match {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} => {}", self.pat, self.expr)
    }
}

/// Binding of a pattern to a type.
#[derive(Clone, PartialEq, Debug)]
pub struct Binding {
    pub id: Id,
    pub type_: Rc<Type>,
}

impl Binding {
    pub fn new(id: Id, type_: Rc<Type>) -> Self {
        Binding { id, type_ }
    }

    /// Returns whether `bindings` matches the fields of `record_type`
    /// exactly: there are as many fields as bindings, and each binding has the
    /// same name and type as a field.
    ///
    /// The type is compared as well as the name because a row binder whose
    /// name equals its record's sole field name -- `yield g = {g = ...}` --
    /// has a binding named like the field but typed as the whole record, not
    /// as the field.
    pub fn matches_fields(bindings: &[Binding], record_type: &Type) -> bool {
        let Type::Record(_, fields) = record_type else {
            return false;
        };
        bindings.len() == fields.len()
            && bindings.iter().all(|b| {
                fields
                    .get(&Label::String(b.id.name.clone()))
                    .is_some_and(|t| **t == *b.type_)
            })
    }

    /// Collects all bindings from a pattern, recursively.
    /// For tuple patterns like `(i,j)`, this returns multiple bindings.
    pub fn collect_bindings(pat: &Pat, bindings: &mut Vec<Binding>) {
        match pat {
            // lint: sort until '#}' where '##Pat::'
            Pat::As(t, name, p) => {
                bindings.push(Binding::new(Id::new(name, 0), t.clone()));
                Binding::collect_bindings(p, bindings);
            }
            Pat::Cons(_, head, tail) => {
                Binding::collect_bindings(head, bindings);
                Binding::collect_bindings(tail, bindings);
            }
            Pat::Constructor(_, _, None)
            | Pat::Literal(_, _)
            | Pat::Wildcard(_) => {
                // These patterns don't bind any variables.
            }
            Pat::Constructor(_, _, Some(p)) => {
                Binding::collect_bindings(p, bindings);
            }
            Pat::Identifier(t, name) => {
                bindings.push(Binding::new(Id::new(name, 0), t.clone()));
            }
            Pat::List(_, pats) => {
                for p in pats {
                    Binding::collect_bindings(p, bindings);
                }
            }
            Pat::Record(_, fields, _) => {
                for field in fields {
                    match field {
                        PatField::Labeled(_, p) | PatField::Anonymous(p) => {
                            Binding::collect_bindings(p, bindings);
                        }
                    }
                }
            }
            Pat::Tuple(_, pats) => {
                for p in pats {
                    Binding::collect_bindings(p, bindings);
                }
            }
        }
    }
}

/// Environment available at a step in a query.
///
/// Tracks the variable bindings, whether the result is an atom (scalar)
/// vs record, and whether the result is ordered.
#[derive(Clone, PartialEq, Debug)]
pub struct StepEnv {
    pub bindings: Vec<Binding>,
    pub atom: bool,
    pub ordered: bool,
}

impl StepEnv {
    /// Empty environment - no bindings, not an atom, ordered.
    pub const fn empty() -> Self {
        StepEnv {
            bindings: Vec::new(),
            atom: false,
            ordered: true,
        }
    }

    pub fn new(bindings: Vec<Binding>, atom: bool, ordered: bool) -> Self {
        assert!(
            !atom || bindings.len() == 1,
            "Atom must have exactly one binding"
        );
        StepEnv {
            bindings,
            atom,
            ordered,
        }
    }

    pub fn with_ordered(&self, ordered: bool) -> Self {
        if ordered == self.ordered {
            return self.clone();
        }
        StepEnv {
            bindings: self.bindings.clone(),
            atom: self.atom,
            ordered,
        }
    }
}

/// Abstract syntax tree (AST) of a step in a query.
#[derive(Clone, Debug)]
pub struct Step {
    pub kind: StepKind,
    pub env: StepEnv,
    /// Join type of a [`StepKind::Scan`] step (inner / `left` / `right` /
    /// `full`); [`JoinType::Inner`] for every other kind of step. Carried on
    /// the `Step` rather than the `Scan` variant so the many passes that
    /// rebuild scan steps don't all have to thread it.
    pub join_type: JoinType,
}

impl Step {
    pub fn new(kind: StepKind, env: StepEnv) -> Self {
        Step {
            kind,
            env,
            join_type: JoinType::Inner,
        }
    }

    /// Creates a scan step with an explicit [`JoinType`].
    pub fn with_join(
        join_type: JoinType,
        kind: StepKind,
        env: StepEnv,
    ) -> Self {
        Step {
            kind,
            env,
            join_type,
        }
    }
}

impl StepKind {
    /// Returns a scan's `on` condition, if it has one.
    pub(crate) fn condition(&self) -> Option<&Expr> {
        match self {
            StepKind::Scan(_, _, Some(c)) => Some(c),
            _ => None,
        }
    }
}

/// Kind of step in a query.
#[derive(Clone, Debug)]
pub enum StepKind {
    // lint: sort until '#}'
    Compute(Box<Expr>),
    Distinct,
    Except(bool, Vec<Expr>),
    Exists,
    Group(Box<Expr>, Option<Box<Expr>>),
    Intersect(bool, Vec<Expr>),
    Order(Box<Expr>),
    Scan(Box<Pat>, Box<Expr>, Option<Box<Expr>>),
    Skip(Box<Expr>),
    Take(Box<Expr>),
    Union(bool, Vec<Expr>),
    Unorder,
    Where(Box<Expr>),
    Yield(Box<Expr>),
}

/// A node of a relational tree: an operator whose inputs are
/// collections and whose result is a collection.
///
/// The tree is morel-java's #449 representation of a query, and
/// `spec.md` on its `julianhyde/449-tree` branch is the contract. Two
/// things are worth knowing before reading the variants.
///
/// **There is no leaf constructor.** An input is an ordinary [`Expr`]
/// of collection type: another node, or a global, a variable, a list
/// literal -- anything. The boundary between the tree and the rest of
/// Core is wherever the expression stops being a node.
///
/// **A node binds the names its expressions read.** A node that sees
/// one row at a time -- a filter, a projection, a group, a sort --
/// binds its input's element as a [`Row`], and a join binds both of
/// its inputs' elements, as [`JoinRows`]. The expressions read them as
/// ordinary identifiers. This is morel-java's model, whose `RowRel`
/// binds a `row` pattern. The names are unique, made by
/// [`fresh_name`], so that no two nodes bind the same one and a pass
/// reasoning about free variables -- use counts, substitution -- sees
/// each row as a variable of its own; and they print as `$0` and `$1`
/// inside the node that binds them. A query's binders survive only in
/// the projection that names them, which is why a query with several
/// binders ends in one.
///
/// A pass that builds a node writes its expressions over the
/// placeholders [`ROW`] and [`RIGHT_ROW`], and [`Rel::bind`] gives the
/// node names of its own; a pass that reads one does the reverse,
/// [`Rel::open`]. No stored tree holds a placeholder.
///
/// Four things that look like constructors are not, and are spelled out
/// here so that they are not added: `distinct` is a [`Rel::Group`]
/// whose keys are the whole element; `compute` is a keyless `Group`
/// plus the extraction the enclosing expression performs; `yieldAll` is
/// a dependent join and a projection; and an outer apply is a
/// [`Rel::Join`] of kind `Left` whose right input reads its left row.
/// Correlation is not a mode either: it is a free occurrence of a
/// join's left row in its right input, so decorrelation rewrites the
/// right input until it no longer reads the row, rather than rewriting
/// one node into another.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum Rel {
    /// `except [distinct] r0 r1 ...`: the elements of `r0` that are in
    /// no later input. All inputs have the same element type.
    Except(bool, Vec<Expr>),

    /// `filter [cond] r`: the elements of the input for which `cond` is
    /// true. Fields are row, input, condition.
    Filter(Row, Box<Expr>, Box<Expr>),

    /// `group [keys] [aggregates] r`: one element per distinct key,
    /// whose value is a record of the keys and the aggregates -- or, if
    /// there is exactly one field in all, that field's value. Fields are
    /// row, input, keys, aggregates.
    ///
    /// `distinct` is this with the whole element as the key and no
    /// aggregates; `compute` is this with no keys.
    Group(Row, Box<Expr>, Vec<(Label, Expr)>, Vec<(Label, Expr)>),

    /// `intersect [distinct] r0 r1 ...`
    Intersect(bool, Vec<Expr>),

    /// `join [kind] [binder] [cond] left right`: the pairs of elements
    /// for which `cond` is true, with the components of the two inputs
    /// concatenated. Fields are kind, rows, condition, left, right.
    ///
    /// A join has no yield. The projection above it is where the
    /// components are named.
    ///
    /// The condition sees both rows, `$0` and `$1`, which are the left
    /// and right elements and are both present whatever the kind --
    /// whereas the *element* of an outer join wraps each component of a
    /// side that may be absent in `option`, on its own. The left row is
    /// in scope in the right input too, and a right input that reads it
    /// is what makes the join dependent: the plan prints the left row
    /// as the join's binder.
    Join(JoinKind, JoinRows, Box<Expr>, Box<Expr>, Box<Expr>),

    /// `project [e] r`: one element per input element, the value of `e`.
    /// Fields are row, input, expression.
    Project(Row, Box<Expr>, Box<Expr>),

    /// `skip [n] r`: the input's elements after the first `n`. Fields
    /// are input, count. The count is evaluated before the first element,
    /// so the node binds no row.
    Skip(Box<Expr>, Box<Expr>),

    /// `sort [e] r`: the input's elements ordered by `e`. Its output is
    /// a `list` whatever its input was. Fields are row, input, key.
    Sort(Row, Box<Expr>, Box<Expr>),

    /// `take [n] r`: the input's first `n` elements. Fields are input,
    /// count; like `skip`'s, the count reads no row.
    Take(Box<Expr>, Box<Expr>),

    /// `unorder r`: the input's elements, as a `bag`.
    Unorder(Box<Expr>),

    /// `union [distinct] r0 r1 ...`
    Union(bool, Vec<Expr>),
}

/// The names a node binds where one of its children is, each with its
/// type; see [`Rel::scoped_children`].
pub type Bound = Vec<(String, Rc<Type>)>;

/// A function of one of a node's children and the names the node binds
/// there; see [`Rel::map_scoped`].
pub type ScopedFn<'a> = dyn Fn(&Expr, &[(String, Rc<Type>)]) -> Expr + 'a;

/// The placeholder for a node's row while the node is being built or
/// read; see [`Rel::bind`] and [`Rel::open`].
pub const ROW: &str = "$0";

/// The placeholder for a join's right row; see [`ROW`].
pub const RIGHT_ROW: &str = "$1";

/// The placeholder for a node's row's position; see [`ROW`].
pub const ORDINAL: &str = "$ordinal";

/// The names a one-input node binds for its expressions to read: its
/// input's element, `$0` as the plan prints it, and, where the node
/// counts its rows, the element's position, `$ordinal`.
///
/// The position is the element's in the node's input, from zero. It
/// is bound beside the element rather than read out of it, which is
/// why a node that reads it has to be told it does: a filter over a
/// sort counts the sorted rows, and the same filter moved below the
/// sort would count others.
#[derive(Clone, Debug)]
pub struct Row {
    pub name: String,
    pub ordinal: Option<String>,
}

impl Row {
    /// A row that [`Rel::bind`] will name, and that counts its rows if
    /// its node's expressions read [`ORDINAL`].
    pub fn placeholder() -> Row {
        Row {
            name: ROW.to_string(),
            ordinal: None,
        }
    }
}

/// The names a join binds its inputs' elements to: `$0` and `$1` as
/// the plan prints them in its condition. The left row is in scope in
/// the right input as well, where it prints under its own name.
#[derive(Clone, Debug)]
pub struct JoinRows {
    pub left: String,
    pub right: String,
    /// The position of the pair, where the join counts its pairs: in
    /// the condition, the pair's position among those the join
    /// considers, `$ordinal`; in the right input, which is evaluated
    /// once for each left row, the position the next pair will have.
    /// Like the left row, it is in scope in the condition and the right
    /// input, and prints under its own name in the right input.
    pub ordinal: Option<String>,
}

impl JoinRows {
    /// Rows that [`Rel::bind`] will name.
    pub fn placeholder() -> JoinRows {
        JoinRows {
            left: ROW.to_string(),
            right: RIGHT_ROW.to_string(),
            ordinal: None,
        }
    }

    /// Rows whose left is already named, because the right input
    /// reads it by that name, and whose right [`Rel::bind`] will name.
    pub fn dependent(left: String) -> JoinRows {
        JoinRows {
            left,
            right: RIGHT_ROW.to_string(),
            ordinal: None,
        }
    }
}

thread_local! {
    /// The counter that every generated binder is named from. One
    /// counter, never reset, so that no two binders in a session share
    /// a name; a plan renumbers what it prints, so the numbers are not
    /// seen.
    static NEXT_NAME: Cell<usize> = const { Cell::new(0) };
}

/// Returns a binder name that nothing else has, `v$N`. A `$` cannot
/// occur in an identifier the query wrote, so it cannot capture one.
pub fn fresh_name() -> String {
    NEXT_NAME.with(|c| {
        let i = c.get();
        c.set(i + 1);
        format!("v${}", i)
    })
}

/// Returns `e` with every identifier `from` renamed `to`, through the
/// nodes of a tree. A row's name is unique, so nothing shadows it.
pub fn rename(e: &Expr, from: &str, to: &str) -> Expr {
    match e {
        Expr::Identifier(t, name) if name == from => {
            Expr::Identifier(t.clone(), to.to_string())
        }
        Expr::Rel(t, rel) => Expr::Rel(
            t.clone(),
            Box::new(rel.map_children(&|x| rename(x, from, to))),
        ),
        _ => rel_lowerer::map_children(e, &|x| rename(x, from, to)),
    }
}

#[allow(dead_code)]
impl Rel {
    /// Returns this node with a name of its own for each row that is
    /// still a placeholder, its expressions reading the name instead.
    ///
    /// A join's condition reads its left row as [`ROW`] whether or not
    /// the left row already has a name, which a dependent join's does.
    pub fn bind(self) -> Rel {
        fn bind_row(row: Row, mut exps: Vec<&mut Expr>) -> Row {
            let mut name = row.name;
            if name == ROW {
                name = fresh_name();
                for e in &mut exps {
                    **e = rename(e, ROW, &name);
                }
            }
            let mut ordinal = row.ordinal;
            let reads_ordinal = exps
                .iter()
                .any(|e| free_finder::free_names_in(e).contains(ORDINAL));
            if reads_ordinal && ordinal.as_deref().is_none_or(|o| o == ORDINAL)
            {
                let o = fresh_name();
                for e in &mut exps {
                    **e = rename(e, ORDINAL, &o);
                }
                ordinal = Some(o);
            }
            Row { name, ordinal }
        }
        match self {
            Rel::Filter(row, input, mut c) => {
                let row = bind_row(row, vec![&mut c]);
                Rel::Filter(row, input, c)
            }
            Rel::Group(row, input, mut keys, mut aggs) => {
                let exps = keys
                    .iter_mut()
                    .chain(aggs.iter_mut())
                    .map(|(_, e)| e)
                    .collect();
                let row = bind_row(row, exps);
                Rel::Group(row, input, keys, aggs)
            }
            Rel::Join(kind, rows, c, left, right) => {
                let left_name = if rows.left == ROW {
                    fresh_name()
                } else {
                    rows.left
                };
                let right_name = if rows.right == RIGHT_ROW {
                    fresh_name()
                } else {
                    rows.right
                };
                let mut c = rename(
                    &rename(&c, ROW, &left_name),
                    RIGHT_ROW,
                    &right_name,
                );
                let mut right = right;
                // The join counts its pairs where its condition or its
                // right input reads the position placeholder.
                let mut ordinal = rows.ordinal.filter(|o| o != ORDINAL);
                let reads =
                    |e: &Expr| free_finder::free_names_in(e).contains(ORDINAL);
                if reads(&c) || reads(&right) {
                    let o = ordinal.get_or_insert_with(fresh_name).clone();
                    c = rename(&c, ORDINAL, &o);
                    right = Box::new(rename(&right, ORDINAL, &o));
                }
                Rel::Join(
                    kind,
                    JoinRows {
                        left: left_name,
                        right: right_name,
                        ordinal,
                    },
                    Box::new(c),
                    left,
                    right,
                )
            }
            Rel::Project(row, input, mut e) => {
                let row = bind_row(row, vec![&mut e]);
                Rel::Project(row, input, e)
            }
            Rel::Sort(row, input, mut e) => {
                let row = bind_row(row, vec![&mut e]);
                Rel::Sort(row, input, e)
            }
            other => other,
        }
    }

    /// Returns this node with its rows renamed to the placeholders in
    /// its expressions, which is the form a pass reasons about and
    /// [`Rel::bind`] turns back into a node.
    ///
    /// A join's left row keeps its name, because its right input may
    /// read it by that name; only the condition reads it as [`ROW`].
    pub fn open(&self) -> Rel {
        let open = |row: &Row, e: &Expr| {
            let e = rename(e, &row.name, ROW);
            match &row.ordinal {
                Some(o) => rename(&e, o, ORDINAL),
                None => e,
            }
        };
        match self {
            Rel::Filter(row, input, c) => Rel::Filter(
                Row::placeholder(),
                input.clone(),
                Box::new(open(row, c)),
            ),
            Rel::Group(row, input, keys, aggs) => {
                let parts = |parts: &[(Label, Expr)]| {
                    parts
                        .iter()
                        .map(|(l, e)| (l.clone(), open(row, e)))
                        .collect()
                };
                Rel::Group(
                    Row::placeholder(),
                    input.clone(),
                    parts(keys),
                    parts(aggs),
                )
            }
            Rel::Join(kind, rows, c, left, right) => {
                let mut c =
                    rename(&rename(c, &rows.left, ROW), &rows.right, RIGHT_ROW);
                // The position keeps its name, which the right input may
                // read it by; only the condition reads it as the
                // placeholder.
                if let Some(o) = &rows.ordinal {
                    c = rename(&c, o, ORDINAL);
                }
                Rel::Join(
                    *kind,
                    JoinRows {
                        ordinal: rows.ordinal.clone(),
                        ..JoinRows::dependent(rows.left.clone())
                    },
                    Box::new(c),
                    left.clone(),
                    right.clone(),
                )
            }
            Rel::Project(row, input, e) => Rel::Project(
                Row::placeholder(),
                input.clone(),
                Box::new(open(row, e)),
            ),
            Rel::Sort(row, input, e) => Rel::Sort(
                Row::placeholder(),
                input.clone(),
                Box::new(open(row, e)),
            ),
            other => other.clone(),
        }
    }

    /// Returns this node with `f` applied to each of its inputs and
    /// expressions, its rows unchanged.
    pub fn map_children(&self, f: &dyn Fn(&Expr) -> Expr) -> Rel {
        let b = |e: &Expr| Box::new(f(e));
        let parts = |parts: &[(Label, Expr)]| {
            parts.iter().map(|(l, e)| (l.clone(), f(e))).collect()
        };
        match self {
            // lint: sort until '#}' where '##Rel::'
            Rel::Except(d, args) => {
                Rel::Except(*d, args.iter().map(f).collect())
            }
            Rel::Filter(row, input, c) => {
                Rel::Filter(row.clone(), b(input), b(c))
            }
            Rel::Group(row, input, keys, aggs) => {
                Rel::Group(row.clone(), b(input), parts(keys), parts(aggs))
            }
            Rel::Intersect(d, args) => {
                Rel::Intersect(*d, args.iter().map(f).collect())
            }
            Rel::Join(k, rows, c, l, r) => {
                Rel::Join(*k, rows.clone(), b(c), b(l), b(r))
            }
            Rel::Project(row, input, e) => {
                Rel::Project(row.clone(), b(input), b(e))
            }
            Rel::Skip(input, n) => Rel::Skip(b(input), b(n)),
            Rel::Sort(row, input, e) => Rel::Sort(row.clone(), b(input), b(e)),
            Rel::Take(input, n) => Rel::Take(b(input), b(n)),
            Rel::Union(d, args) => Rel::Union(*d, args.iter().map(f).collect()),
            Rel::Unorder(input) => Rel::Unorder(b(input)),
        }
    }

    /// Returns this node's children -- its inputs and its expressions --
    /// each with the names the node binds where that child is: none
    /// for an input or a count, the row (and the position, where the
    /// node counts its rows) for a per-row expression, and for a join
    /// the left row in its right input and both rows in its condition.
    /// Each name comes with its type.
    ///
    /// It is what a pass that reasons about names walks, where
    /// [`Rel::children`] says nothing about scope.
    pub fn scoped_children(&self) -> Vec<(&Expr, Bound)> {
        let elem = |e: &Expr| {
            element_type(&e.type_()).unwrap_or_else(|| e.type_().clone())
        };
        let int = || Rc::new(Type::Primitive(types::PrimitiveType::Int));
        let row_names = |row: &Row, input: &Expr| {
            let mut names = vec![(row.name.clone(), elem(input))];
            if let Some(o) = &row.ordinal {
                names.push((o.clone(), int()));
            }
            names
        };
        let mut v: Vec<(&Expr, Bound)> = Vec::new();
        match self {
            // lint: sort until '#}' where '##Rel::'
            Rel::Except(_, inputs)
            | Rel::Intersect(_, inputs)
            | Rel::Union(_, inputs) => {
                v.extend(inputs.iter().map(|e| (e, vec![])));
            }
            Rel::Filter(row, input, e)
            | Rel::Project(row, input, e)
            | Rel::Sort(row, input, e) => {
                v.push((input, vec![]));
                v.push((e, row_names(row, input)));
            }
            Rel::Group(row, input, keys, aggregates) => {
                v.push((input, vec![]));
                for (_, e) in keys.iter().chain(aggregates.iter()) {
                    v.push((e, row_names(row, input)));
                }
            }
            Rel::Join(_, rows, condition, left, right) => {
                let mut left_row = vec![(rows.left.clone(), elem(left))];
                if let Some(o) = &rows.ordinal {
                    left_row.push((o.clone(), int()));
                }
                let mut both = left_row.clone();
                both.push((rows.right.clone(), elem(right)));
                v.push((left, vec![]));
                v.push((right, left_row));
                v.push((condition, both));
            }
            Rel::Skip(input, n) | Rel::Take(input, n) => {
                v.push((input, vec![]));
                v.push((n, vec![]));
            }
            Rel::Unorder(input) => v.push((input, vec![])),
        }
        v
    }

    /// Returns this node with `f` applied to each of its children, each
    /// with the names the node binds there; see [`Rel::scoped_children`].
    /// The node's rows are unchanged.
    pub fn map_scoped(&self, f: &ScopedFn<'_>) -> Rel {
        let elem = |e: &Expr| {
            element_type(&e.type_()).unwrap_or_else(|| e.type_().clone())
        };
        let int = || Rc::new(Type::Primitive(types::PrimitiveType::Int));
        let row_names = |row: &Row, input: &Expr| {
            let mut names = vec![(row.name.clone(), elem(input))];
            if let Some(o) = &row.ordinal {
                names.push((o.clone(), int()));
            }
            names
        };
        let none: &[(String, Rc<Type>)] = &[];
        let b = |e: &Expr, names: &[(String, Rc<Type>)]| Box::new(f(e, names));
        match self {
            // lint: sort until '#}' where '##Rel::'
            Rel::Except(d, args) => {
                Rel::Except(*d, args.iter().map(|e| f(e, none)).collect())
            }
            Rel::Filter(row, input, c) => {
                let names = row_names(row, input);
                Rel::Filter(row.clone(), b(input, none), b(c, &names))
            }
            Rel::Group(row, input, keys, aggs) => {
                let names = row_names(row, input);
                let parts = |parts: &[(Label, Expr)]| {
                    parts
                        .iter()
                        .map(|(l, e)| (l.clone(), f(e, &names)))
                        .collect()
                };
                Rel::Group(
                    row.clone(),
                    b(input, none),
                    parts(keys),
                    parts(aggs),
                )
            }
            Rel::Intersect(d, args) => {
                Rel::Intersect(*d, args.iter().map(|e| f(e, none)).collect())
            }
            Rel::Join(k, rows, c, l, r) => {
                let mut left_row = vec![(rows.left.clone(), elem(l))];
                if let Some(o) = &rows.ordinal {
                    left_row.push((o.clone(), int()));
                }
                let mut both = left_row.clone();
                both.push((rows.right.clone(), elem(r)));
                Rel::Join(
                    *k,
                    rows.clone(),
                    b(c, &both),
                    b(l, none),
                    b(r, &left_row),
                )
            }
            Rel::Project(row, input, e) => {
                let names = row_names(row, input);
                Rel::Project(row.clone(), b(input, none), b(e, &names))
            }
            Rel::Skip(input, n) => Rel::Skip(b(input, none), b(n, none)),
            Rel::Sort(row, input, e) => {
                let names = row_names(row, input);
                Rel::Sort(row.clone(), b(input, none), b(e, &names))
            }
            Rel::Take(input, n) => Rel::Take(b(input, none), b(n, none)),
            Rel::Union(d, args) => {
                Rel::Union(*d, args.iter().map(|e| f(e, none)).collect())
            }
            Rel::Unorder(input) => Rel::Unorder(b(input, none)),
        }
    }

    /// Returns whether this is a join whose right input reads its left
    /// row, which is what makes a join dependent.
    pub fn is_dependent(&self) -> bool {
        match self {
            Rel::Join(_, rows, _, _, right) => {
                free_finder::free_names_in(right).contains(&rows.left)
            }
            _ => false,
        }
    }

    /// Returns this node's sub-expressions: its inputs, and the
    /// expressions its arguments are made of, in the order they are
    /// written.
    ///
    /// It is a flat view, and says nothing about scope: a join's left
    /// row is in scope in its condition and its right input, and every
    /// other row in its own node's expressions. A pass that reasons
    /// about names must walk the variants and honour that; this serves
    /// the passes for which the answer is the same either way, such as
    /// "does anything under here mention an extent".
    pub fn children(&self) -> Vec<&Expr> {
        let mut v: Vec<&Expr> = Vec::new();
        match self {
            Rel::Except(_, inputs)
            | Rel::Intersect(_, inputs)
            | Rel::Union(_, inputs) => v.extend(inputs.iter()),
            Rel::Filter(_, input, e)
            | Rel::Project(_, input, e)
            | Rel::Skip(input, e)
            | Rel::Sort(_, input, e)
            | Rel::Take(input, e) => {
                v.push(input);
                v.push(e);
            }
            Rel::Group(_, input, keys, aggregates) => {
                v.push(input);
                v.extend(keys.iter().map(|(_, e)| e));
                v.extend(aggregates.iter().map(|(_, e)| e));
            }
            Rel::Join(_, _, condition, left, right) => {
                v.push(left);
                v.push(right);
                v.push(condition);
            }
            Rel::Unorder(input) => v.push(input),
        }
        v
    }

    /// Returns the collection type this node produces: the element type
    /// `spec.md` §3 derives, under the kind §4 derives. `None` where an
    /// input is not a collection, which the validator reports.
    pub fn derive_type(&self) -> Option<Rc<Type>> {
        let kind = self.derive_kind()?;
        Some(kind.apply(self.derive_element_type()?))
    }

    /// Returns the element type this node produces; see
    /// [`Rel::derive_type`].
    pub fn derive_element_type(&self) -> Option<Rc<Type>> {
        match self {
            // The element passes through unchanged.
            Rel::Filter(_, input, _)
            | Rel::Skip(input, _)
            | Rel::Sort(_, input, _)
            | Rel::Take(input, _)
            | Rel::Unorder(input) => element_type(&input.type_()),
            // The element is what the expression builds.
            Rel::Project(_, _, e) => Some(e.type_()),
            // A record of the keys and the aggregates -- a record
            // whether there is one field or many, because an element
            // whose shape depended on how many labels there were would
            // make dropping one of two labels a change of shape that
            // nothing above could rewrite locally. Where a query wants
            // the bare value, a projection above says so. `spec.md` §3
            // is silent about no fields at all, which `group ()` makes;
            // `record_type` answers `unit`, which is what a record of
            // nothing is in ML and what the query's own type says.
            Rel::Group(_, _, keys, aggregates) => {
                let mut fields: Vec<(Label, Rc<Type>)> = Vec::new();
                for (label, e) in keys.iter().chain(aggregates.iter()) {
                    fields.push((label.clone(), e.type_()));
                }
                Some(Rc::new(types::record_type(fields.into_iter().collect())))
            }
            // The inputs' components, concatenated.
            Rel::Join(kind, _, _, left, right) => {
                Some(Rc::new(Type::Tuple(join_components(*kind, left, right)?)))
            }
            // Every input has the same element type, so the first says
            // what it is.
            Rel::Except(_, inputs)
            | Rel::Intersect(_, inputs)
            | Rel::Union(_, inputs) => element_type(&inputs.first()?.type_()),
        }
    }

    /// Returns the kind this node produces; see [`Rel::derive_type`].
    pub fn derive_kind(&self) -> Option<Kind> {
        match self {
            // A sort orders, and an unorder forgets, whatever they were
            // given. These two are why the kind is in the signature.
            Rel::Sort(_, _, _) => Some(Kind::List),
            Rel::Unorder(_) => Some(Kind::Bag),
            // The input's kind passes through.
            Rel::Filter(_, input, _)
            | Rel::Group(_, input, _, _)
            | Rel::Project(_, input, _)
            | Rel::Skip(input, _)
            | Rel::Take(input, _) => Kind::of(&input.type_()),
            Rel::Join(_, _, _, left, right) => Some(Kind::all([
                Kind::of(&left.type_())?,
                Kind::of(&right.type_())?,
            ])),
            Rel::Except(_, inputs)
            | Rel::Intersect(_, inputs)
            | Rel::Union(_, inputs) => {
                let mut kinds = Vec::with_capacity(inputs.len());
                for input in inputs {
                    kinds.push(Kind::of(&input.type_())?);
                }
                Some(Kind::all(kinds))
            }
        }
    }

    /// Returns this node's inputs: the collection-valued children,
    /// which are the lines below it when it prints. Its argument
    /// expressions are not among them; see [`Rel::children`] for those.
    pub fn inputs(&self) -> Vec<&Expr> {
        match self {
            Rel::Except(_, inputs)
            | Rel::Intersect(_, inputs)
            | Rel::Union(_, inputs) => inputs.iter().collect(),
            Rel::Filter(_, input, _)
            | Rel::Group(_, input, _, _)
            | Rel::Project(_, input, _)
            | Rel::Skip(input, _)
            | Rel::Sort(_, input, _)
            | Rel::Take(input, _)
            | Rel::Unorder(input) => vec![input],
            Rel::Join(_, _, _, left, right) => vec![left, right],
        }
    }

    /// Returns the name this node prints under.
    pub fn op_name(&self) -> &'static str {
        match self {
            Rel::Except(_, _) => "except",
            Rel::Filter(_, _, _) => "filter",
            Rel::Group(_, _, _, _) => "group",
            Rel::Intersect(_, _) => "intersect",
            Rel::Join(_, _, _, _, _) => "join",
            Rel::Project(_, _, _) => "project",
            Rel::Skip(_, _) => "skip",
            Rel::Sort(_, _, _) => "sort",
            Rel::Take(_, _) => "take",
            Rel::Unorder(_) => "unorder",
            Rel::Union(_, _) => "union",
        }
    }
}

/// Whether a collection is ordered. A node's type is a kind applied to
/// an element type, and `spec.md` §4 says which kind each constructor
/// produces.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
#[allow(dead_code)]
pub enum Kind {
    Bag,
    List,
}

#[allow(dead_code)]
impl Kind {
    /// Returns the kind of a collection type, or `None` if `t` is not a
    /// collection.
    pub fn of(t: &Type) -> Option<Kind> {
        match t {
            Type::Bag(_) => Some(Kind::Bag),
            Type::List(_) => Some(Kind::List),
            _ => None,
        }
    }

    /// Returns this kind applied to `elem`.
    pub fn apply(self, elem: Rc<Type>) -> Rc<Type> {
        Rc::new(match self {
            Kind::Bag => Type::Bag(elem),
            Kind::List => Type::List(elem),
        })
    }

    /// Returns `List` only if every kind is `List`. A join is a nested
    /// loop, and a set operator reads all of its inputs, so one bag
    /// makes the result a bag.
    pub fn all(kinds: impl IntoIterator<Item = Kind>) -> Kind {
        if kinds.into_iter().all(|k| k == Kind::List) {
            Kind::List
        } else {
            Kind::Bag
        }
    }
}

/// Returns the element type of a collection, or `None` if `t` is not a
/// collection.
#[allow(dead_code)]
/// Returns the names an extent's pattern binds, which is how a tree,
/// whose leaves carry no names, says what a leaf was called: one
/// name for a pattern that is one, a name per component for a tuple
/// of them, and none otherwise.
pub fn extent_names(pat: &Pat) -> Vec<String> {
    match pat {
        Pat::Identifier(_, name) => vec![name.clone()],
        Pat::Tuple(_, args) => {
            let names: Vec<String> = args
                .iter()
                .filter_map(|arg| match arg {
                    Pat::Identifier(_, name) => Some(name.clone()),
                    _ => None,
                })
                .collect();
            if names.len() == args.len() {
                names
            } else {
                Vec::new()
            }
        }
        // A record of names, in the order of its type's fields, which
        // is the order of the components a tree reads it by.
        Pat::Record(t, fields, false) => {
            let Type::Record(_, types) = peel_type(t) else {
                return Vec::new();
            };
            let mut names = Vec::new();
            for label in types.keys() {
                let name = fields.iter().find_map(|f| match f {
                    PatField::Labeled(l, p) if *l == label.to_string() => {
                        match p.as_ref() {
                            Pat::Identifier(_, n) => Some(n.clone()),
                            _ => None,
                        }
                    }
                    _ => None,
                });
                match name {
                    Some(n) => names.push(n),
                    None => return Vec::new(),
                }
            }
            names
        }
        _ => Vec::new(),
    }
}

pub fn element_type(t: &Type) -> Option<Rc<Type>> {
    match t {
        Type::Bag(e) | Type::List(e) => Some(e.clone()),
        _ => None,
    }
}

/// Returns the element types of `exp`'s components.
///
/// A join's components are its inputs' components concatenated, so
/// `(a join b) join c` and `a join (b join c)` both have three, in the
/// same order; anything else is one component, itself. A component of a
/// side an outer join can leave absent is wrapped in `option`, on its
/// own rather than as a whole row, and the wrapping is additive, so two
/// chained outer joins give `option option`.
#[allow(dead_code)]
pub fn components(exp: &Expr) -> Option<Vec<Rc<Type>>> {
    if let Expr::Rel(_, rel) = exp
        && let Rel::Join(kind, _, _, left, right) = rel.as_ref()
    {
        return join_components(*kind, left, right);
    }
    Some(vec![element_type(&exp.type_())?])
}

/// Returns the element types of a join's components; see
/// [`components`].
#[allow(dead_code)]
fn join_components(
    kind: JoinKind,
    left: &Expr,
    right: &Expr,
) -> Option<Vec<Rc<Type>>> {
    fn wrap(types: Vec<Rc<Type>>, absent: bool) -> Vec<Rc<Type>> {
        if !absent {
            return types;
        }
        types
            .into_iter()
            .map(|t| Rc::new(Type::Named(vec![t], "option".to_string())))
            .collect()
    }
    let mut v = wrap(components(left)?, kind.left_may_be_absent());
    v.extend(wrap(components(right)?, kind.right_may_be_absent()));
    Some(v)
}

/// Which rows an outer [`Rel::Join`] keeps, and therefore which of its
/// components may be absent.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
#[allow(dead_code)]
pub enum JoinKind {
    /// Every row is a matching pair; nothing is absent.
    Inner,
    /// A left element that matches nothing still yields a row, whose
    /// right components are absent.
    Left,
    /// As `Left`, with the sides exchanged.
    Right,
    /// Both, so a component of either side may be absent.
    Full,
}

#[allow(dead_code)]
impl JoinKind {
    /// Returns whether a row may have no element from the left input, so
    /// that the left components are `option`.
    pub fn left_may_be_absent(self) -> bool {
        matches!(self, JoinKind::Right | JoinKind::Full)
    }

    /// Returns whether a row may have no element from the right input.
    pub fn right_may_be_absent(self) -> bool {
        matches!(self, JoinKind::Left | JoinKind::Full)
    }

    /// Returns the name this kind prints under, or `None` for `Inner`,
    /// which is omitted.
    pub fn name(self) -> Option<&'static str> {
        match self {
            JoinKind::Inner => None,
            JoinKind::Left => Some("left"),
            JoinKind::Right => Some("right"),
            JoinKind::Full => Some("full"),
        }
    }
}

/// Pattern in core representation.
#[derive(Clone, PartialEq, Debug)]
pub enum Pat {
    Wildcard(Rc<Type>),
    /// `Identifier(t, name)` is a pattern that matches any expression and
    /// binds it to an identifier. For example, `x`.
    Identifier(Rc<Type>, String),
    /// `As(t, name, pat)` is a pattern that matches if its subpattern matches,
    /// and if so, binds the identifier. For example, `(x, y) as z`.
    As(Rc<Type>, String, Box<Pat>),
    /// `Constructor(t, name, pat)` is a pattern that matches a constructor
    /// (with or without an argument). For example, `EMPTY` or `LEAF x` or
    /// `NODE (left, right)`.
    Constructor(Rc<Type>, String, Option<Box<Pat>>),
    /// `Literal(t, val)` is a pattern that matches a literal, e.g. `1` or
    /// `"foo"`. It does not bind any values.
    Literal(Rc<Type>, Val),
    /// `Tuple(t, pats)` is a pattern that matches a tuple. The match succeeds
    /// if all elements of a tuple match, e.g. `(x, y, z)` or `(1, _, z)`.
    Tuple(Rc<Type>, Vec<Pat>),
    /// `Tuple(t, pats)` is a pattern that matches a list. The match succeeds
    /// if all elements of a list match, e.g. `[x, y, z]` or `[1, _, z]`. It
    /// can also be written `x :: y :: z :: nil`.
    List(Rc<Type>, Vec<Pat>),
    /// `Record(t, fields, ellipsis)` is a pattern that matches a record. The
    /// match succeeds if all fields match. For example, `{a = 1, b = (p, q),
    /// ...}` bind `p` and `q` if successful.
    Record(Rc<Type>, Vec<PatField>, bool),
    /// `Cons(t, head, tail)` is a pattern that matches a list. For example,
    /// `1 :: rest`.
    Cons(Rc<Type>, Box<Pat>, Box<Pat>),
}

/// Name of the frame slot holding the `ordinal` counter.
///
/// It holds a `$` so that it cannot be a field the user wrote: a query
/// may have its own field called `ordinal` (reached as `` `ordinal` ``),
/// and the counter must not clobber it.
pub(crate) const ORDINAL_SLOT: &str = "ordinal$";

/// Constructors whose values have a dedicated `Val` representation, so a
/// pattern naming one can be matched against a value at compile time.
/// Every other constructor belongs to a datatype whose values are
/// `Val::Constructor(tag, _)`; see [`Pat::is_decidable`].
const BUILT_IN_CONSTRUCTOR_PATS: [&str; 7] =
    ["EQUAL", "GREATER", "INL", "INR", "LESS", "NONE", "SOME"];

impl Pat {
    /// Returns the sub-patterns of a tuple, or of a record that has
    /// a pattern for every field, in the order of the slots of the
    /// value they match; `None` for any other pattern.
    pub fn components(&self) -> Option<Vec<&Pat>> {
        match self {
            Pat::Record(t, fields, false) => {
                let Type::Record(_, labels) = t.as_ref() else {
                    return None;
                };
                labels
                    .keys()
                    .map(|label| {
                        fields.iter().find_map(|f| match f {
                            PatField::Labeled(name, p)
                                if label.matches(name) =>
                            {
                                Some(p.as_ref())
                            }
                            _ => None,
                        })
                    })
                    .collect()
            }
            Pat::Tuple(_, args) => Some(args.iter().collect()),
            _ => None,
        }
    }

    /// Returns the name of this pattern if it is an identifier or `as`,
    /// otherwise None.
    pub fn name(&self) -> Option<String> {
        match self {
            Pat::Identifier(_, name) | Pat::As(_, name, _) => {
                Some(name.clone())
            }
            _ => None,
        }
    }

    /// Returns this pattern's type.
    pub fn type_(&self) -> Rc<Type> {
        match self {
            // lint: sort until '#}' where '##Pat::'
            Pat::As(t, _, _) => t.clone(),
            Pat::Cons(t, _, _) => t.clone(),
            Pat::Constructor(t, _, _) => t.clone(),
            Pat::Identifier(t, _) => t.clone(),
            Pat::List(t, _) => t.clone(),
            Pat::Literal(t, _) => t.clone(),
            Pat::Record(t, _, _) => t.clone(),
            Pat::Tuple(t, _) => t.clone(),
            Pat::Wildcard(t) => t.clone(),
        }
    }

    /// Returns a copy of this pattern with a different type.
    pub fn with_type(self, t: Rc<Type>) -> Self {
        match self {
            Pat::As(_, n, p) => Pat::As(t, n, p),
            Pat::Cons(_, h, tl) => Pat::Cons(t, h, tl),
            Pat::Constructor(_, n, p) => Pat::Constructor(t, n, p),
            Pat::Identifier(_, n) => Pat::Identifier(t, n),
            Pat::List(_, ps) => Pat::List(t, ps),
            Pat::Literal(_, v) => Pat::Literal(t, v),
            Pat::Record(_, fs, e) => Pat::Record(t, fs, e),
            Pat::Tuple(_, ps) => Pat::Tuple(t, ps),
            Pat::Wildcard(_) => Pat::Wildcard(t),
        }
    }

    /// Returns whether matching this pattern against a value can be
    /// decided by [`Self::bind_recurse`].
    ///
    /// A constructor of a user-defined datatype cannot: its values are
    /// `Val::Constructor(tag, _)`, and the tag is the constructor's
    /// position within the declaration, which the pattern does not
    /// record. `bind_recurse` answers `false` for such a pattern, which
    /// a caller would otherwise read as a definite non-match — so a
    /// caller that folds a `case` at compile time must first check this,
    /// and leave the `case` for the run-time matcher when it is false.
    pub(crate) fn is_decidable(&self) -> bool {
        match self {
            Pat::Constructor(_, name, inner) => {
                BUILT_IN_CONSTRUCTOR_PATS.contains(&name.as_str())
                    && inner.as_ref().is_none_or(|p| p.is_decidable())
            }
            Pat::As(_, _, p) => p.is_decidable(),
            Pat::Cons(_, h, t) => h.is_decidable() && t.is_decidable(),
            Pat::List(_, ps) | Pat::Tuple(_, ps) => {
                ps.iter().all(Pat::is_decidable)
            }
            Pat::Record(_, fields, _) => fields.iter().all(|f| match f {
                PatField::Labeled(_, p) | PatField::Anonymous(p) => {
                    p.is_decidable()
                }
            }),
            Pat::Identifier(_, _) | Pat::Literal(_, _) | Pat::Wildcard(_) => {
                true
            }
        }
    }

    /// Walks this pattern over `val`, calling `consumer` for each variable
    /// the pattern would bind. Returns `false` if the pattern fails to
    /// match the value (e.g. literal mismatch, wrong constructor) — the
    /// caller should raise the `Bind` exception in that case.
    ///
    /// Call [`Self::is_decidable`] first: for a constructor this method
    /// cannot decide, it answers `false`, which is indistinguishable
    /// from a genuine non-match.
    pub(crate) fn bind_recurse(
        &self,
        val: &Val,
        consumer: &mut dyn FnMut(Box<Pat>, &Val),
    ) -> bool {
        match self {
            // lint: sort until '#}' where '##Pat::'
            Pat::As(_, _name, inner) => {
                // Layered pattern 'p as inner_pat': bind 'p' to the
                // whole value, then recurse into the inner pattern.
                consumer(Box::new(self.clone()), val);
                inner.bind_recurse(val, consumer)
            }
            Pat::Cons(_, head, tail) => {
                // 'h :: t' matches a non-empty list.
                if let Val::List(vs) = val
                    && !vs.is_empty()
                {
                    head.bind_recurse(&vs[0], consumer)
                        && tail.bind_recurse(
                            &Val::List(Rc::new(vs[1..].to_vec())),
                            consumer,
                        )
                } else {
                    false
                }
            }
            Pat::Constructor(_, name, inner) => {
                // Constructor pattern. Supports the built-in `option`,
                // `either`, and `order` types and user-defined datatypes
                // (whose values are `Val::Constructor(ordinal, ...)`,
                // matched by name via the type's constructor list).
                use std::cmp::Ordering;
                let matched_inner: Option<Option<&Val>> =
                    match (name.as_str(), val) {
                        ("SOME", Val::Some(v)) => Some(Some(v.as_ref())),
                        ("INL", Val::Inl(v)) => Some(Some(v.as_ref())),
                        ("INR", Val::Inr(v)) => Some(Some(v.as_ref())),
                        ("NONE", Val::Unit) => Some(None),
                        ("LESS", Val::Order(o)) if o.0 == Ordering::Less => {
                            Some(None)
                        }
                        ("EQUAL", Val::Order(o)) if o.0 == Ordering::Equal => {
                            Some(None)
                        }
                        ("GREATER", Val::Order(o))
                            if o.0 == Ordering::Greater =>
                        {
                            Some(None)
                        }
                        // Built-in constructor name with a non-matching
                        // value of one of those special types: not a match.
                        (n, _) if BUILT_IN_CONSTRUCTOR_PATS.contains(&n) => {
                            None
                        }
                        // User-defined datatype constructor:
                        // `Val::Constructor(tag, payload)`, where the tag
                        // is the constructor's position within the
                        // declaration -- which the pattern does not record,
                        // so we cannot tell `RED` from `GREEN` here. Answer
                        // "no match"; callers that would act on the answer
                        // must first ask `is_decidable`.
                        _ => return false,
                    };
                let Some(matched_inner) = matched_inner else {
                    return false;
                };
                match (inner, matched_inner) {
                    (Some(p), Some(v)) => p.bind_recurse(v, consumer),
                    (None, None) => true,
                    _ => false,
                }
            }
            Pat::Identifier(_, _name) => {
                consumer(Box::new(self.clone()), val);
                true
            }
            Pat::List(_, pats) => {
                // 'val [a, b, c] = e' matches a list of exactly the
                // pattern's length.
                if let Val::List(vs) = val
                    && pats.len() == vs.len()
                {
                    for (p, v) in pats.iter().zip(vs.iter()) {
                        if !p.bind_recurse(v, consumer) {
                            return false;
                        }
                    }
                    true
                } else {
                    false
                }
            }
            Pat::Literal(_, lit) => {
                // Literal pattern matches iff value equals the literal.
                val == lit
            }
            Pat::Record(t, fields, _) => {
                // 'val {a, b = p, ...} = e': for each labelled field,
                // look up its index in the record type's alphabetical-key
                // order, then recurse.
                // A tuple is a record whose labels are ordinals, so a
                // record pattern matches one: `{1=a}` takes the first
                // field of a pair.
                // A name is not a shape, so a type written under one --
                // `val {i, j}: pp = ...` -- is peeled to find the fields.
                let labels: Option<Vec<Label>> = match peel_type(t) {
                    Type::Record(_, type_fields) => {
                        Some(type_fields.keys().cloned().collect())
                    }
                    Type::Tuple(types) => {
                        Some((1..=types.len()).map(Label::Ordinal).collect())
                    }
                    _ => None,
                };
                if let (Some(labels), Val::List(vs)) = (labels, val) {
                    let find = |needle: &str| {
                        labels.iter().position(|l| l.matches(needle))
                    };
                    for field in fields {
                        let (name_opt, sub_pat) = match field {
                            PatField::Labeled(name, p) => {
                                (Some(name.clone()), p.as_ref())
                            }
                            PatField::Anonymous(p) => (p.name(), p.as_ref()),
                        };
                        if let Some(name) = name_opt
                            && let Some(i) = find(&name)
                            && !sub_pat.bind_recurse(&vs[i], consumer)
                        {
                            return false;
                        }
                    }
                    true
                } else {
                    false
                }
            }
            Pat::Tuple(_, pats) => {
                // 'val (p1, p2, ...) = e' matches a tuple of the same
                // arity (or unit if pats is empty).
                if let Val::List(vs) = val
                    && pats.len() == vs.len()
                {
                    for (p, v) in pats.iter().zip(vs.iter()) {
                        if !p.bind_recurse(v, consumer) {
                            return false;
                        }
                    }
                    true
                } else {
                    matches!(val, Val::Unit) && pats.is_empty()
                }
            }
            Pat::Wildcard(_) => true,
        }
    }

    /// Calls a given function for each atomic identifier in this pattern.
    /// Since core doesn't have IDs, we'll use 0 as a placeholder.
    pub(crate) fn for_each_id_pat(
        &self,
        consumer: &mut impl FnMut((&Type, &str)),
    ) {
        match self {
            // lint: sort until '#}' where '##Pat::'
            Pat::As(t, name, inner) => {
                (*consumer)((t, name.as_str()));
                inner.for_each_id_pat(consumer);
            }
            Pat::Cons(_, head, tail) => {
                head.for_each_id_pat(consumer);
                tail.for_each_id_pat(consumer);
            }
            Pat::Constructor(_, _, pat) => {
                if let Some(p) = pat {
                    p.for_each_id_pat(consumer);
                }
            }
            Pat::Identifier(t, name) => (*consumer)((t, name.as_str())),
            Pat::List(_, pats) => {
                pats.iter().for_each(|p| p.for_each_id_pat(consumer))
            }
            Pat::Literal(_, _) => {
                // No identifiers to bind.
            }
            Pat::Record(_, pat_fields, _) => {
                for field in pat_fields {
                    match field {
                        PatField::Labeled(_, p) => p.for_each_id_pat(consumer),
                        PatField::Anonymous(p) => p.for_each_id_pat(consumer),
                    }
                }
            }
            Pat::Tuple(_, pats) => {
                pats.iter().for_each(|p| p.for_each_id_pat(consumer))
            }
            Pat::Wildcard(_) => {
                // No identifiers to bind.
            }
        }
    }
}

/// Returns a query's steps, as morel-java's core unparser writes them:
/// each step after the keyword that names it, and the scans after the
/// first introduced by `join`.
///
/// This is what `Sys.planEx` shows.
fn steps_doc(steps: &[Step]) -> Doc {
    let mut scanned = false;
    let mut docs = Vec::new();
    for step in steps {
        docs.push(text(" "));
        match &step.kind {
            // lint: sort until '#}' where '##StepKind::'
            StepKind::Compute(e) => {
                docs.push(beside(text("compute "), e.to_doc()));
            }
            StepKind::Distinct => docs.push(text("distinct")),
            StepKind::Except(distinct, es) => {
                docs.push(set_step_doc("except", *distinct, es));
            }
            StepKind::Exists => docs.push(text("exists")),
            StepKind::Group(key, agg) => {
                docs.push(beside(text("group "), key.to_doc()));
                if let Some(agg) = agg {
                    docs.push(beside(text(" compute "), agg.to_doc()));
                }
            }
            StepKind::Intersect(distinct, es) => {
                docs.push(set_step_doc("intersect", *distinct, es));
            }
            StepKind::Order(e) => docs.push(beside(text("order "), e.to_doc())),
            StepKind::Scan(pat, source, condition) => {
                if scanned {
                    docs.push(text("join "));
                }
                scanned = true;
                // A pattern that destructures is bracketed, so that what
                // it binds is not read as part of the step around it. A
                // tuple pattern is written in brackets already.
                match pat.as_ref() {
                    Pat::Identifier(_, _) | Pat::Tuple(_, _) => {
                        docs.push(text(&pat.to_string()));
                    }
                    _ => docs.push(text(&format!("({})", pat))),
                }
                // A scan over an extent has no source to name; what it
                // enumerates is the values of the pattern's type.
                match source.as_ref() {
                    Expr::Extent(..) => {
                        docs.push(text(&format!(" : {}", pat.type_())));
                    }
                    _ => docs.push(beside(text(" in "), source.to_doc())),
                }
                if let Some(condition) = condition {
                    docs.push(beside(text(" on "), condition.to_doc()));
                }
            }
            StepKind::Skip(e) => docs.push(beside(text("skip "), e.to_doc())),
            StepKind::Take(e) => docs.push(beside(text("take "), e.to_doc())),
            StepKind::Union(distinct, es) => {
                docs.push(set_step_doc("union", *distinct, es));
            }
            StepKind::Unorder => docs.push(text("unorder")),
            StepKind::Where(e) => docs.push(beside(text("where "), e.to_doc())),
            StepKind::Yield(e) => docs.push(beside(text("yield "), e.to_doc())),
        }
    }
    hcat(docs)
}

/// Returns a set operator's step: the keyword, `distinct` where the
/// step removes duplicates, and the operands.
///
/// The flag is *distinct*, which is what the parser sets for `union
/// distinct` and what [`crate::syntax::ast`] prints. This used to name
/// it `all` and write that word, so a plan said the opposite of the
/// query it came from and re-running the plan would have changed the
/// answer.
fn set_step_doc(keyword: &str, distinct: bool, exprs: &[Expr]) -> Doc {
    let mut docs = vec![text(keyword)];
    if distinct {
        docs.push(text(" distinct"));
    }
    for (i, e) in exprs.iter().enumerate() {
        docs.push(text(if i > 0 { ", " } else { " " }));
        docs.push(e.to_doc());
    }
    hcat(docs)
}

impl Display for Pat {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match &self {
            // lint: sort until '#}' where '##Pat::'
            Pat::As(_, name, pat) => write!(f, "{} as {}", pat, name),
            Pat::Cons(_, head, tail) => write!(f, "{} :: {}", head, tail),
            Pat::Constructor(_, name, None) => write!(f, "{}", name),
            Pat::Constructor(_, name, Some(pat)) => {
                // Wrap the constructor argument in parens to match
                // morel-java's unparser (e.g. `SOME(s)`, `INL(x)`).
                match pat.as_ref() {
                    Pat::Tuple(_, _) => write!(f, "{} {}", name, pat),
                    _ => write!(f, "{}({})", name, pat),
                }
            }
            Pat::Identifier(_, name) => write!(f, "{}", name),
            Pat::List(_, pats) => {
                let pats_str = pats
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "[{}]", pats_str)
            }
            Pat::Literal(_, val) => write!(f, "{}", val),
            Pat::Record(t, fields, ellipsis) => {
                // Expand `{a = ..., ...}` to `{a = ..., b = _, ...}`
                // listing every field of the record type (with `_` for
                // any field not bound by the pattern), so that the
                // unparser output matches morel-java.
                let labels: Vec<&Label> = match peel_type(t) {
                    Type::Record(_, fs) => fs.keys().collect(),
                    _ => Vec::new(),
                };
                if !labels.is_empty() && *ellipsis {
                    use std::collections::BTreeMap;
                    let mut explicit: BTreeMap<String, String> =
                        BTreeMap::new();
                    for field in fields {
                        match field {
                            PatField::Labeled(name, pat) => {
                                explicit
                                    .insert(name.clone(), format!("{}", pat));
                            }
                            PatField::Anonymous(pat) => {
                                if let Some(name) = pat.name() {
                                    explicit.insert(name, format!("{}", pat));
                                }
                            }
                        }
                    }
                    let parts: Vec<String> = labels
                        .iter()
                        .filter_map(|l| match l {
                            Label::String(s) => Some(s.as_str()),
                            _ => None,
                        })
                        .map(|name| {
                            let body = explicit
                                .get(name)
                                .cloned()
                                .unwrap_or_else(|| "_".to_string());
                            format!("{} = {}", name, body)
                        })
                        .collect();
                    return write!(f, "{{{}}}", parts.join(", "));
                }
                let fields_str = fields
                    .iter()
                    .map(|field| match field {
                        PatField::Labeled(name, pat) => {
                            format!("{} = {}", name, pat)
                        }
                        PatField::Anonymous(pat) => format!("{}", pat),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                if *ellipsis {
                    write!(f, "{{{}, ...}}", fields_str)
                } else {
                    write!(f, "{{{}}}", fields_str)
                }
            }
            Pat::Tuple(_, pats) => {
                let pats_str = pats
                    .iter()
                    .map(|p| format!("{}", p))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", pats_str)
            }
            Pat::Wildcard(_) => write!(f, "_"),
        }
    }
}

/// Abstract syntax tree (AST) of a field in a record pattern.
/// It can be labeled, anonymous, or ellipsis.
/// For example, `{ label = x, y, ... }` has one of each.
#[derive(Clone, PartialEq, Debug)]
pub enum PatField {
    Labeled(String, Box<Pat>), // e.g. `named = x`
    Anonymous(Box<Pat>),       // e.g. `y`
}

/// Declaration.
#[derive(Clone, Debug)]
pub enum Decl {
    /// Non-recursive value binding.
    NonRecVal(Box<ValBind>),
    /// Recursive value binding.
    RecVal(Vec<ValBind>),
    Over(String),
    Type(Vec<TypeBind>),
    Datatype(Vec<DatatypeBind>),
}

impl Decl {
    /// Returns whether any expression this declaration binds references
    /// an `ordinal` counting the enclosing step's rows.
    pub(crate) fn uses_ordinal(&self) -> bool {
        match self {
            Decl::NonRecVal(b) => b.expr.uses_ordinal(),
            Decl::RecVal(binds) => binds.iter().any(|b| b.expr.uses_ordinal()),
            _ => false,
        }
    }

    /// Invokes an action for each top-level binding.
    ///
    /// If a recursive val has multiple arms, each of those arms is a binding.
    /// If any of the arms binds a composite pattern, it is wrapped in an `as`.
    /// Consider:
    ///
    /// ```sml
    /// val w = 1
    /// and (x, y) = (2, 3)
    /// ```
    ///
    /// Translation introduces an extra `as` binding, `z`, to capture the
    /// composite pattern:
    ///
    /// ```sml
    /// val w = 1
    /// and (x, y) as z = (2, 3)
    /// ```
    ///
    /// `z` is marked *skipped* and the sub-bindings appear in the output.
    /// Thus, the output is
    ///
    /// ```text
    /// val w = 1 : int
    /// val x = 2 : int
    /// val y = 3 : int
    /// ```
    pub(crate) fn for_each_binding<F>(&self, action: &mut F)
    where
        F: FnMut(&Pat, &Expr, &Option<Box<Id>>, &Option<Span>),
    {
        match &self {
            Decl::NonRecVal(b) => call(action, b.deref()),
            Decl::RecVal(binds) => {
                for b in binds {
                    call(action, b);
                }
            }
            _ => {
                // Other kinds of declaration don't have bindings.
            }
        }

        fn call<F>(action: &mut F, b: &ValBind)
        where
            F: FnMut(&Pat, &Expr, &Option<Box<Id>>, &Option<Span>),
        {
            action(&b.pat, &b.expr, &b.overload_pat, &b.span);
        }
    }

    pub(crate) fn for_each_id_pat(&self, mut p0: impl FnMut((&Type, &str))) {
        match self {
            Decl::NonRecVal(val_bind) => val_bind.pat.for_each_id_pat(&mut p0),
            Decl::RecVal(val_binds) => {
                for val_bind in val_binds {
                    val_bind.pat.for_each_id_pat(&mut p0)
                }
            }
            Decl::Over(_) | Decl::Type(_) | Decl::Datatype(_) => {}
        }
    }
}

impl Display for Decl {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            // lint: sort until '#}' where '##Decl::'
            Decl::Datatype(datatypes) => {
                write!(f, "datatype ")?;
                fmt_list(f, datatypes, "; ")
            }
            Decl::NonRecVal(bind) => write!(f, "val {}", bind),
            Decl::Over(name) => write!(f, "over {}", name),
            Decl::RecVal(binds) => {
                write!(f, "val rec ")?;
                fmt_list(f, binds, " and ")
            }
            Decl::Type(types) => {
                write!(f, "type ")?;
                fmt_list(f, types, "; ")
            }
        }
    }
}

/// Value binding.
#[derive(Clone, Debug)]
pub struct ValBind {
    pub pat: Pat,
    pub t: Type,
    pub expr: Expr,
    pub overload_pat: Option<Box<Id>>,
    /// Source span of the binding (the pattern + expression, not including
    /// the leading 'val' keyword or trailing ';'). Used to report the
    /// location of a 'Bind' exception when the pattern fails to match.
    pub span: Option<Span>,
}

impl Display for ValBind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{} = {}", self.pat, self.expr)
    }
}

/// Type binding.
#[derive(Clone, Debug)]
pub struct TypeBind {
    /// Type parameters of the alias, e.g. `'a` in
    /// `type 'a my_list = 'a list`.
    pub type_vars: Vec<String>,
    pub name: String,
    pub type_: Type,
    /// The conditions of a checked type, empty if the type is
    /// unchecked. They are carried so that the declaration echoes as it
    /// was written.
    pub checks: Checks,
}

impl Display for TypeBind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{}: {}{}", self.name, self.type_, self.checks)
    }
}

/// Datatype binding.
#[derive(Clone, Debug)]
pub struct DatatypeBind {
    pub type_vars: Vec<String>,
    pub name: String,
    pub constructors: Vec<ConBind>,
}

impl Display for DatatypeBind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let constructors_str = self
            .constructors
            .iter()
            .map(|c| format!("{}", c))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{}: {}", self.name, constructors_str)
    }
}

/// Constructor binding.
#[derive(Clone, Debug)]
pub struct ConBind {
    pub name: String,
    pub type_: Option<Type>,
}

impl Display for ConBind {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(
            f,
            "{}{}",
            self.name,
            match &self.type_ {
                Some(t) => format!(": {}", t),
                None => "".to_string(),
            }
        )
    }
}

/// Formats a collection with a separator, handling the enumeration pattern.
fn fmt_list<T: Display>(
    f: &mut Formatter<'_>,
    items: &[T],
    separator: &str,
) -> FmtResult {
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            write!(f, "{}", separator)?;
        }
        write!(f, "{}", item)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::types::PrimitiveType;

    fn int_t() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Int))
    }

    fn bool_t() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Bool))
    }

    /// Applies a binary operator to two operands.
    fn call(op: BuiltInFunction, t: Rc<Type>, a: Expr, b: Expr) -> Expr {
        let pair_t = Rc::new(Type::Tuple(vec![a.type_(), b.type_()]));
        let fn_t = Rc::new(Type::Fn(pair_t.clone(), t.clone()));
        Expr::Apply(
            t,
            Box::new(Expr::Literal(fn_t, Val::Fn(op))),
            Box::new(Expr::Tuple(pair_t, vec![a, b])),
            Span::new(""),
        )
    }

    /// Returns `(x > 1 andalso y > 2) andalso z > 3`.
    fn conjunction() -> Expr {
        let gt = |name: &str, n: i32| {
            call(
                BuiltInFunction::IntGt,
                bool_t(),
                Expr::Identifier(int_t(), name.to_string()),
                Expr::Literal(int_t(), Val::Int(n)),
            )
        };
        let and = |a, b| call(BuiltInFunction::BoolAndAlso, bool_t(), a, b);
        and(and(gt("x", 1), gt("y", 2)), gt("z", 3))
    }

    /// No width prints on one line, and so does a width the text fits.
    #[test]
    fn test_fits() {
        let e = conjunction();
        let flat = "x > 1 andalso y > 2 andalso z > 3";
        assert_eq!(e.to_string(), flat);
        assert_eq!(e.unparse(flat.len() as i32), flat);
    }

    /// An `andalso` chain that does not fit breaks before each
    /// `andalso`, which leads its line; the outer group breaks before
    /// the inner one, so what fits on a line stays on it.
    #[test]
    fn test_breaks() {
        let e = conjunction();
        assert_eq!(e.unparse(20), "x > 1 andalso y > 2\nandalso z > 3");
        assert_eq!(e.unparse(10), "x > 1\nandalso y > 2\nandalso z > 3");
    }

    fn int() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Int))
    }

    fn string() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::String))
    }

    fn bool_() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Bool))
    }

    /// A leaf: any expression of collection type will do, because there
    /// is no leaf constructor.
    fn leaf(elem: Rc<Type>, kind: Kind) -> Expr {
        Expr::Identifier(kind.apply(elem), "r".to_string())
    }

    fn node(rel: Rel) -> Expr {
        let rel = rel.bind();
        let t = rel.derive_type().expect("derives a type");
        Expr::Rel(t, Box::new(rel))
    }

    /// The element a node is being built over, `$0`.
    fn row(t: Rc<Type>) -> Expr {
        Expr::Identifier(t, ROW.to_string())
    }

    fn option(t: Rc<Type>) -> Rc<Type> {
        Rc::new(Type::Named(vec![t], "option".to_string()))
    }

    /// `filter`, `skip` and `take` pass their input's element and kind
    /// through; `sort` orders whatever it is given, and `unorder`
    /// forgets.
    #[test]
    fn one_input_nodes_derive_their_type() {
        let input = leaf(int(), Kind::List);
        let cond = Expr::Literal(bool_(), Val::Bool(true));
        let filter = Rel::Filter(
            Row::placeholder(),
            Box::new(input.clone()),
            Box::new(cond.clone()),
        );
        assert_eq!(*filter.derive_type().unwrap(), Type::List(int()));

        let bag_input = leaf(int(), Kind::Bag);
        let on_bag = Rel::Filter(
            Row::placeholder(),
            Box::new(bag_input.clone()),
            Box::new(cond),
        );
        assert_eq!(*on_bag.derive_type().unwrap(), Type::Bag(int()));

        // A sort's output is a list whatever its input was, and an
        // unorder's is a bag. These two are why the kind is derived
        // rather than carried.
        let key = row(int());
        let sort = Rel::Sort(
            Row::placeholder(),
            Box::new(bag_input.clone()),
            Box::new(key.clone()),
        );
        assert_eq!(*sort.derive_type().unwrap(), Type::List(int()));
        let unorder = Rel::Unorder(Box::new(input.clone()));
        assert_eq!(*unorder.derive_type().unwrap(), Type::Bag(int()));

        // `project`'s element is what its expression builds, so a
        // projection may change the element type.
        let project = Rel::Project(
            Row::placeholder(),
            Box::new(input.clone()),
            Box::new(key),
        );
        assert_eq!(*project.derive_type().unwrap(), Type::List(int()));
        let to_string = Rel::Project(
            Row::placeholder(),
            Box::new(input),
            Box::new(Expr::Identifier(string(), "s".to_string())),
        );
        assert_eq!(*to_string.derive_type().unwrap(), Type::List(string()));
    }

    /// A join concatenates its inputs' components, and they stay flat:
    /// three inputs give three components in either association.
    #[test]
    fn join_concatenates_components() {
        let a = leaf(int(), Kind::List);
        let b = leaf(string(), Kind::List);
        let c = leaf(bool_(), Kind::List);
        let t = Expr::Literal(bool_(), Val::Bool(true));
        let join = |kind, left: Expr, right: Expr| {
            Rel::Join(
                kind,
                JoinRows::placeholder(),
                Box::new(t.clone()),
                Box::new(left),
                Box::new(right),
            )
        };

        let ab = node(join(JoinKind::Inner, a.clone(), b.clone()));
        assert_eq!(
            *ab.type_(),
            Type::List(Rc::new(Type::Tuple(vec![int(), string()])))
        );

        // Left-deep and right-deep have the same three components.
        let left_deep = node(join(JoinKind::Inner, ab, c.clone()));
        let bc = node(join(JoinKind::Inner, b, c));
        let right_deep = node(join(JoinKind::Inner, a.clone(), bc));
        let three = Type::Tuple(vec![int(), string(), bool_()]);
        assert_eq!(*left_deep.type_(), Type::List(three.clone().into()));
        assert_eq!(*right_deep.type_(), Type::List(three.into()));
    }

    /// An outer join wraps each component of the side that may be
    /// absent, on its own rather than the row as a whole, and the
    /// wrapping is additive when joins chain.
    #[test]
    fn outer_join_wraps_each_component() {
        let a = leaf(int(), Kind::List);
        let b = leaf(string(), Kind::List);
        let c = leaf(bool_(), Kind::List);
        let t = Expr::Literal(bool_(), Val::Bool(true));
        let join = |kind, left: Expr, right: Expr| {
            Rel::Join(
                kind,
                JoinRows::placeholder(),
                Box::new(t.clone()),
                Box::new(left),
                Box::new(right),
            )
        };

        let left = node(join(JoinKind::Left, a.clone(), b.clone()));
        assert_eq!(
            *left.type_(),
            Type::List(Rc::new(Type::Tuple(vec![int(), option(string())])))
        );
        let right = node(join(JoinKind::Right, a.clone(), b.clone()));
        assert_eq!(
            *right.type_(),
            Type::List(Rc::new(Type::Tuple(vec![option(int()), string()])))
        );
        let full = node(join(JoinKind::Full, a.clone(), b));
        assert_eq!(
            *full.type_(),
            Type::List(Rc::new(Type::Tuple(vec![
                option(int()),
                option(string())
            ])))
        );

        // Chained, the wrapping is additive: the first join's right
        // component is wrapped again by the second.
        let chained = node(join(JoinKind::Left, left, c));
        assert_eq!(
            *chained.type_(),
            Type::List(Rc::new(Type::Tuple(vec![
                int(),
                option(string()),
                option(bool_())
            ])))
        );
    }

    /// A join is a nested loop, so one bag makes the result a bag; the
    /// same holds for a set operator, which reads all of its inputs.
    #[test]
    fn one_bag_makes_a_bag() {
        let t = Expr::Literal(bool_(), Val::Bool(true));
        let join = |left: Expr, right: Expr| {
            Rel::Join(
                JoinKind::Inner,
                JoinRows::placeholder(),
                Box::new(t.clone()),
                Box::new(left),
                Box::new(right),
            )
        };
        let list = leaf(int(), Kind::List);
        let bag = leaf(int(), Kind::Bag);
        assert_eq!(
            join(list.clone(), list.clone()).derive_kind(),
            Some(Kind::List)
        );
        assert_eq!(
            join(list.clone(), bag.clone()).derive_kind(),
            Some(Kind::Bag)
        );
        assert_eq!(
            Rel::Union(false, vec![list.clone(), list.clone()]).derive_kind(),
            Some(Kind::List)
        );
        assert_eq!(
            Rel::Union(false, vec![list.clone(), bag]).derive_kind(),
            Some(Kind::Bag)
        );
        // A set operator's element type is its inputs', which agree.
        assert_eq!(
            *Rel::Except(true, vec![list.clone(), list])
                .derive_type()
                .unwrap(),
            Type::List(int())
        );
    }

    /// A group builds a record of its keys and aggregates, of one field
    /// or many.
    #[test]
    fn group_builds_a_record() {
        let input = leaf(int(), Kind::Bag);
        let key = row(int());
        let total = Expr::Identifier(int(), "total".to_string());
        let two = Rel::Group(
            Row::placeholder(),
            Box::new(input.clone()),
            vec![(Label::String("deptno".to_string()), key.clone())],
            vec![(Label::String("total".to_string()), total.clone())],
        );
        let t = two.derive_type().unwrap();
        match t.as_ref() {
            Type::Bag(elem) => match elem.as_ref() {
                Type::Record(_, fields) => assert_eq!(fields.len(), 2),
                other => panic!("expected a record, got {:?}", other),
            },
            other => panic!("expected a bag, got {:?}", other),
        }

        // One aggregate and no keys: still a record, of one field; a
        // query that wants the bare value projects it out above.
        let one = Rel::Group(
            Row::placeholder(),
            Box::new(input),
            vec![],
            vec![(Label::String("total".to_string()), total)],
        );
        match one.derive_type().unwrap().as_ref() {
            Type::Bag(elem) => match elem.as_ref() {
                Type::Record(_, fields) => assert_eq!(fields.len(), 1),
                other => panic!("expected a record, got {:?}", other),
            },
            other => panic!("expected a bag, got {:?}", other),
        }
    }

    /// A node binds its row, so reading it frees no name; and the name
    /// is the node's own, not the placeholder it was built over.
    #[test]
    fn a_row_is_bound_by_its_node() {
        use crate::compile::free_finder::free_names_in;
        let input = leaf(int(), Kind::List);
        let filter = node(Rel::Filter(
            Row::placeholder(),
            Box::new(input),
            Box::new(row(int())),
        ));
        assert!(free_names_in(&filter).contains("r"));
        assert_eq!(free_names_in(&filter).len(), 1);
        let Expr::Rel(_, rel) = &filter else {
            panic!("a node");
        };
        let Rel::Filter(row, _, condition) = rel.as_ref() else {
            panic!("a filter");
        };
        assert_ne!(row.name, ROW);
        assert!(
            matches!(condition.as_ref(), Expr::Identifier(_, n) if *n == row.name)
        );
        // Opened, it reads the placeholder again.
        let Rel::Filter(row, _, condition) = rel.open() else {
            panic!("a filter");
        };
        assert_eq!(row.name, ROW);
        assert!(
            matches!(condition.as_ref(), Expr::Identifier(_, n) if n == ROW)
        );
    }

    /// A node counts its rows where its expressions read the position
    /// placeholder, and not otherwise; the position is bound beside the
    /// row, and reading it frees no name either.
    #[test]
    fn a_node_binds_an_ordinal_where_it_reads_one() {
        use crate::compile::free_finder::free_names_in;
        let position = Expr::Identifier(int(), ORDINAL.to_string());
        let project = node(Rel::Project(
            Row::placeholder(),
            Box::new(leaf(int(), Kind::List)),
            Box::new(position),
        ));
        let Expr::Rel(_, rel) = &project else {
            panic!("a node");
        };
        let Rel::Project(bound, _, e) = rel.as_ref() else {
            panic!("a projection");
        };
        let ordinal = bound.ordinal.clone().expect("binds an ordinal");
        assert_ne!(ordinal, ORDINAL);
        assert!(matches!(e.as_ref(), Expr::Identifier(_, n) if *n == ordinal));
        assert_eq!(free_names_in(&project).len(), 1);

        let plain = Rel::Project(
            Row::placeholder(),
            Box::new(leaf(int(), Kind::List)),
            Box::new(row(int())),
        )
        .bind();
        let Rel::Project(bound, _, _) = plain else {
            panic!("a projection");
        };
        assert_eq!(bound.ordinal, None);
    }

    /// A node's children come with the names it binds there: none in
    /// an input, the row in a per-row expression, and for a join the
    /// left row in its right input and both rows in its condition.
    #[test]
    fn a_node_says_what_it_binds_where() {
        let filter = node(Rel::Filter(
            Row::placeholder(),
            Box::new(leaf(int(), Kind::List)),
            Box::new(Expr::Literal(bool_(), Val::Bool(true))),
        ));
        let Expr::Rel(_, rel) = &filter else {
            panic!("a node");
        };
        let Rel::Filter(row, _, _) = rel.as_ref() else {
            panic!("a filter");
        };
        let names: Vec<Vec<String>> = rel
            .scoped_children()
            .into_iter()
            .map(|(_, names)| names.into_iter().map(|(n, _)| n).collect())
            .collect();
        assert_eq!(names, vec![vec![], vec![row.name.clone()]]);

        let join = node(Rel::Join(
            JoinKind::Inner,
            JoinRows::dependent("v".to_string()),
            Box::new(Expr::Literal(bool_(), Val::Bool(true))),
            Box::new(leaf(int(), Kind::List)),
            Box::new(leaf(int(), Kind::List)),
        ));
        let Expr::Rel(_, rel) = &join else {
            panic!("a node");
        };
        let Rel::Join(_, rows, _, _, _) = rel.as_ref() else {
            panic!("a join");
        };
        // `map_scoped` hands each child the same names, whatever order
        // it builds the node in.
        let seen = RefCell::new(Vec::new());
        rel.map_scoped(&|e, names| {
            seen.borrow_mut().push((
                format!("{}", e),
                names.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>(),
            ));
            e.clone()
        });
        let mut seen = seen.into_inner();
        seen.sort();
        assert_eq!(
            seen,
            vec![
                ("r".to_string(), vec![]),
                ("r".to_string(), vec!["v".to_string()]),
                (
                    "true".to_string(),
                    vec!["v".to_string(), rows.right.clone()]
                ),
            ]
        );
    }

    /// A join's left row is in scope in its right input, and reading it
    /// there is what makes the join dependent.
    #[test]
    fn join_left_row_is_bound_in_the_right_input() {
        use crate::compile::free_finder::free_names_in;
        let left = Expr::Identifier(Kind::List.apply(int()), "l".to_string());
        let right_reads_binder =
            Expr::Identifier(Kind::List.apply(int()), "v".to_string());
        let join = node(Rel::Join(
            JoinKind::Inner,
            JoinRows::dependent("v".to_string()),
            Box::new(Expr::Literal(bool_(), Val::Bool(true))),
            Box::new(left),
            Box::new(right_reads_binder),
        ));
        let free = free_names_in(&join);
        assert!(free.contains("l"));
        assert!(!free.contains("v"), "the binder binds in the right input");
        let Expr::Rel(_, rel) = &join else {
            panic!("a node");
        };
        assert!(rel.is_dependent());
    }
}
