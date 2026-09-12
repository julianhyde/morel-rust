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

use crate::compile::postfix::peel_type;
use crate::compile::span::Span;
use crate::compile::type_env::Id;
use crate::compile::types::{Checks, Label, Type};
use crate::eval::val::Val;
use crate::syntax::ast::JoinType;
use std::collections::BTreeMap;
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

    /// `Input(t, i)` names the element of the `i`th input of the
    /// relational node that encloses it: `$0` for a one-input node's
    /// input, and `$0` and `$1` for a join's left and right. `t` is that
    /// element's type.
    ///
    /// It is a node of its own rather than an identifier, and that is
    /// deliberate. morel-java made it an `Id` first, over a pattern
    /// named `"$0"`, and every `$0` in a tree was then the same variable
    /// to anything reasoning about free variables -- use counts,
    /// substitution -- because a pattern compares by name and ordinal
    /// and not by type. It does not announce itself when it is wrong: a
    /// use count that is too high only makes the inliner decline, while
    /// one that is too low makes it substitute across a node boundary.
    /// See spec.md §2 and plan.md.
    #[allow(dead_code)]
    Input(Rc<Type>, usize),

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
    Exists(Rc<Type>, Vec<Step>),
    Forall(Rc<Type>, Vec<Step>),

    /// Placeholder for "all values of type `t`" — produced by lowering
    /// `from p` (no `in`) when the variable's source has not yet been
    /// resolved by predicate inversion. The compile-time checker
    /// rejects programs that still contain `Extent` after the
    /// expander pass; for now (no expander), any program that lowers
    /// to an `Extent` errors with "unbounded variable in `from`".
    /// `span` points at the source `from p` step so the runtime
    /// "pattern not grounded" error can pinpoint the offending
    /// site.
    Extent(Rc<Type>, Span),
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
            Expr::Exists(t, _) => t.clone(),
            Expr::Extent(t, _) => t.clone(),
            Expr::Fn(t, _, _) => t.clone(),
            Expr::Forall(t, _) => t.clone(),
            Expr::From(t, _) => t.clone(),
            Expr::Identifier(t, _) => t.clone(),
            Expr::Input(t, _) => t.clone(),
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
            Expr::From(_, steps)
            | Expr::Exists(_, steps)
            | Expr::Forall(_, steps) => {
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
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match &self {
            // lint: sort until '#}' where '##Expr::'
            Expr::Aggregate(_, a0, a1, _) => {
                write!(f, "({} over {})", a0, a1)
            }
            Expr::Apply(_, fx, arg, _) => {
                // `Apply(Lit(Val::Fn(op)), Tuple([a, b]))` is written
                // `a op b` when `op` has an infix form, and as a call
                // otherwise: `x + 1`, but `#* Int (x, 2)`. The set is
                // morel-java's (see `BuiltInFunction::infix_op`).
                if let Expr::Literal(_, Val::Fn(func)) = fx.as_ref()
                    && let Expr::Tuple(_, args) = arg.as_ref()
                    && args.len() == 2
                    && let Some(op) = func.infix_op()
                {
                    return write!(f, "{} {} {}", args[0], op, args[1]);
                }
                // An argument is bracketed unless it is written as an
                // atom already: a name, a literal, or something that
                // carries its own brackets. `#rev List xs`, but
                // `#flatten Range ([OPEN (0, 10)])`.
                match arg.as_ref() {
                    Expr::Identifier(_, _)
                    | Expr::Input(_, _)
                    | Expr::Literal(_, _)
                    | Expr::Tuple(_, _) => write!(f, "{} {}", fx, arg),
                    _ => write!(f, "{} ({})", fx, arg),
                }
            }
            Expr::Case(_, e, arms, _) => {
                write!(f, "case {} of ", e)?;
                for (i, match_) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{} => {}", match_.pat, match_.expr)?;
                }
                Ok(())
            }
            Expr::Current(_) => write!(f, "current"),
            Expr::Exists(_, steps) => write!(f, "exists {:?}", steps),
            Expr::Extent(t, _) => write!(f, "extent({})", t),
            Expr::Fn(_, arms, _) => {
                write!(f, "fn ")?;
                for (i, match_) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{} => {}", match_.pat, match_.expr)?;
                }
                Ok(())
            }
            Expr::Forall(_, steps) => {
                write!(f, "forall")?;
                write_steps(f, steps)
            }
            Expr::From(_, steps) => {
                write!(f, "from")?;
                write_steps(f, steps)
            }
            Expr::Identifier(_, name) => write!(f, "{}", name),
            Expr::Input(_, i) => write!(f, "${}", i),
            Expr::Let(_, decls, body) => {
                write!(f, "let ")?;
                let mut first = true;
                for decl in decls {
                    if first {
                        first = false;
                    } else {
                        write!(f, "; ")?;
                    }
                    write!(f, "{}", decl)?;
                }
                write!(f, " in {} end", body)
            }
            Expr::List(_, elems) => {
                let elems_str = elems
                    .iter()
                    .map(|e| format!("{}", e))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "[{}]", elems_str)
            }
            Expr::Literal(_, lit) => write!(f, "{}", lit),
            Expr::Ordinal(_) => write!(f, "ordinal"),
            Expr::Raise(_, e, _) => write!(f, "raise {}", e),
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
                    Some(name) => write!(f, "#{}", name),
                    None => write!(f, "#{}", slot + 1),
                }
            }
            // Provisional. `spec.md` §6 lays a node out one per line,
            // with its type, and that is milestone R4; until then a node
            // prints on one line so that a tree built in a test can be
            // read at all.
            Expr::Rel(_, rel) => {
                write!(f, "{}", rel.op_name())?;
                for child in rel.children() {
                    write!(f, " ({})", child)?;
                }
                Ok(())
            }
            Expr::Tuple(t, elems) => {
                if let Type::Record(_, type_fields) = t.as_ref() {
                    write!(f, "{{")?;
                    let mut first = true;
                    for (label, e) in type_fields.keys().zip(elems.iter()) {
                        if first {
                            first = false;
                        } else {
                            write!(f, ", ")?;
                        }
                        write!(f, "{} = {}", label, e)?;
                    }
                    return write!(f, "}}");
                }
                let elems_str = elems
                    .iter()
                    .map(|e| format!("{}", e))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({})", elems_str)
            }
        }
    }
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
/// **A node holds no names.** Its expressions read their input's
/// element as [`Expr::Input`], `$0`, which every node rebinds to its
/// own input; a join's right element is `$1`. What a binder used to be
/// called survives only in the projection that names it, which is why a
/// query with several binders ends in one.
///
/// Four things that look like constructors are not, and are spelled out
/// here so that they are not added: `distinct` is a [`Rel::Group`]
/// whose keys are the whole element; `compute` is a keyless `Group`
/// plus the extraction the enclosing expression performs; `yieldAll` is
/// a dependent join and a projection; and an outer apply is a
/// [`Rel::Join`] of kind `Left` carrying a binder. Correlation is not a
/// mode either: it is a free occurrence of a join's binder in its right
/// input, so decorrelation drops the binder rather than rewriting one
/// node into another.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub enum Rel {
    /// `except [distinct] r0 r1 ...`: the elements of `r0` that are in
    /// no later input. All inputs have the same element type.
    Except(bool, Vec<Expr>),

    /// `filter [cond] r`: the elements of the input for which `cond` is
    /// true. Fields are input, condition.
    Filter(Box<Expr>, Box<Expr>),

    /// `group [keys] [aggregates] r`: one element per distinct key,
    /// whose value is a record of the keys and the aggregates -- or, if
    /// there is exactly one field in all, that field's value. Fields are
    /// input, keys, aggregates.
    ///
    /// `distinct` is this with the whole element as the key and no
    /// aggregates; `compute` is this with no keys.
    Group(Box<Expr>, Vec<(Label, Expr)>, Vec<(Label, Expr)>),

    /// `ifEmpty [e] r`: the input's elements where it has some, and the
    /// single element `e` where it has none. Fields are input, value.
    ///
    /// `e` is evaluated only where the input is empty, so -- like a
    /// `Skip` count -- it cannot read `$0`. It can read whatever
    /// encloses the tree, which inside the right input of a dependent
    /// join includes that join's binder.
    IfEmpty(Box<Expr>, Box<Expr>),

    /// `intersect [distinct] r0 r1 ...`
    Intersect(bool, Vec<Expr>),

    /// `join [kind] [binder] [cond] left right`: the pairs of elements
    /// for which `cond` is true, with the components of the two inputs
    /// concatenated. Fields are kind, binder, condition, left, right.
    ///
    /// A join has no yield. The projection above it is where the
    /// components are named.
    ///
    /// The binder, where there is one, names the left element inside the
    /// right input and nowhere else; its presence is what makes the join
    /// dependent. The condition sees `$0` and `$1`, which are the left
    /// and right elements and are both present whatever the kind --
    /// whereas the *element* of an outer join wraps each component of a
    /// side that may be absent in `option`, on its own.
    Join(JoinKind, Option<String>, Box<Expr>, Box<Expr>, Box<Expr>),

    /// `project [e] r`: one element per input element, the value of `e`.
    /// Fields are input, expression.
    Project(Box<Expr>, Box<Expr>),

    /// `skip [n] r`: the input's elements after the first `n`. Fields
    /// are input, count. The count is evaluated before the first element
    /// and so cannot read `$0`.
    Skip(Box<Expr>, Box<Expr>),

    /// `sort [e] r`: the input's elements ordered by `e`. Its output is
    /// a `list` whatever its input was. Fields are input, key.
    Sort(Box<Expr>, Box<Expr>),

    /// `take [n] r`: the input's first `n` elements. Fields are input,
    /// count; the count cannot read `$0`.
    Take(Box<Expr>, Box<Expr>),

    /// `unorder r`: the input's elements, as a `bag`.
    Unorder(Box<Expr>),

    /// `union [distinct] r0 r1 ...`
    Union(bool, Vec<Expr>),
}

#[allow(dead_code)]
impl Rel {
    /// Returns this node's sub-expressions: its inputs, and the
    /// expressions its arguments are made of, in the order they are
    /// written.
    ///
    /// It is a flat view, and says nothing about scope: a join's binder
    /// is in scope in its right input and nowhere else, and every node
    /// rebinds `$0` for its own expressions. A pass that rewrites, or
    /// that reasons about names, must walk the variants and honour
    /// that; this serves the passes for which the answer is the same
    /// either way, such as "does anything under here mention an
    /// extent".
    pub fn children(&self) -> Vec<&Expr> {
        let mut v: Vec<&Expr> = Vec::new();
        match self {
            Rel::Except(_, inputs)
            | Rel::Intersect(_, inputs)
            | Rel::Union(_, inputs) => v.extend(inputs.iter()),
            Rel::Filter(input, e)
            | Rel::IfEmpty(input, e)
            | Rel::Project(input, e)
            | Rel::Skip(input, e)
            | Rel::Sort(input, e)
            | Rel::Take(input, e) => {
                v.push(input);
                v.push(e);
            }
            Rel::Group(input, keys, aggregates) => {
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
            Rel::Filter(input, _)
            | Rel::Skip(input, _)
            | Rel::Sort(input, _)
            | Rel::Take(input, _)
            | Rel::Unorder(input) => element_type(&input.type_()),
            // `ifEmpty`'s value is another element, so it has the
            // input's type; the node's element type is that.
            Rel::IfEmpty(input, _) => element_type(&input.type_()),
            // The element is what the expression builds.
            Rel::Project(_, e) => Some(e.type_()),
            // A record of the keys and the aggregates -- or, where
            // there is exactly one field in all, that field's type,
            // which is how `compute` yields a scalar.
            Rel::Group(_, keys, aggregates) => {
                let mut fields: Vec<(Label, Rc<Type>)> = Vec::new();
                for (label, e) in keys.iter().chain(aggregates.iter()) {
                    fields.push((label.clone(), e.type_()));
                }
                if fields.len() == 1 {
                    return Some(fields.pop().unwrap().1);
                }
                let mut map = BTreeMap::new();
                for (label, t) in fields {
                    map.insert(label, t);
                }
                Some(Rc::new(Type::Record(false, map)))
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
            Rel::Sort(_, _) => Some(Kind::List),
            Rel::Unorder(_) => Some(Kind::Bag),
            // The input's kind passes through.
            Rel::Filter(input, _)
            | Rel::Group(input, _, _)
            | Rel::IfEmpty(input, _)
            | Rel::Project(input, _)
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
            Rel::Filter(input, _)
            | Rel::Group(input, _, _)
            | Rel::IfEmpty(input, _)
            | Rel::Project(input, _)
            | Rel::Skip(input, _)
            | Rel::Sort(input, _)
            | Rel::Take(input, _)
            | Rel::Unorder(input) => vec![input],
            Rel::Join(_, _, _, left, right) => vec![left, right],
        }
    }

    /// Returns the name this node prints under.
    pub fn op_name(&self) -> &'static str {
        match self {
            Rel::Except(_, _) => "except",
            Rel::Filter(_, _) => "filter",
            Rel::Group(_, _, _) => "group",
            Rel::IfEmpty(_, _) => "ifEmpty",
            Rel::Intersect(_, _) => "intersect",
            Rel::Join(_, _, _, _, _) => "join",
            Rel::Project(_, _) => "project",
            Rel::Skip(_, _) => "skip",
            Rel::Sort(_, _) => "sort",
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

/// Writes a query's steps, as morel-java's core unparser writes them:
/// each step after the keyword that names it, and the scans after the
/// first introduced by `join`.
///
/// This is what `Sys.planEx` shows.
fn write_steps(f: &mut Formatter<'_>, steps: &[Step]) -> FmtResult {
    let mut scanned = false;
    for step in steps {
        write!(f, " ")?;
        match &step.kind {
            // lint: sort until '#}' where '##StepKind::'
            StepKind::Compute(e) => write!(f, "compute {}", e)?,
            StepKind::Distinct => write!(f, "distinct")?,
            StepKind::Except(all, es) => write_set_step(f, "except", *all, es)?,
            StepKind::Exists => write!(f, "exists")?,
            StepKind::Group(key, agg) => {
                write!(f, "group {}", key)?;
                if let Some(agg) = agg {
                    write!(f, " compute {}", agg)?;
                }
            }
            StepKind::Intersect(all, es) => {
                write_set_step(f, "intersect", *all, es)?;
            }
            StepKind::Order(e) => write!(f, "order {}", e)?,
            StepKind::Scan(pat, source, condition) => {
                if scanned {
                    write!(f, "join ")?;
                }
                scanned = true;
                // A pattern that destructures is bracketed, so that what
                // it binds is not read as part of the step around it. A
                // tuple pattern is written in brackets already.
                match pat.as_ref() {
                    Pat::Identifier(_, _) | Pat::Tuple(_, _) => {
                        write!(f, "{}", pat)?;
                    }
                    _ => write!(f, "({})", pat)?,
                }
                // A scan over an extent has no source to name; what it
                // enumerates is the values of the pattern's type.
                match source.as_ref() {
                    Expr::Extent(_, _) => write!(f, " : {}", pat.type_())?,
                    _ => write!(f, " in {}", source)?,
                }
                if let Some(condition) = condition {
                    write!(f, " on {}", condition)?;
                }
            }
            StepKind::Skip(e) => write!(f, "skip {}", e)?,
            StepKind::Take(e) => write!(f, "take {}", e)?,
            StepKind::Union(all, es) => write_set_step(f, "union", *all, es)?,
            StepKind::Unorder => write!(f, "unorder")?,
            StepKind::Where(e) => write!(f, "where {}", e)?,
            StepKind::Yield(e) => write!(f, "yield {}", e)?,
        }
    }
    Ok(())
}

/// Writes a `union`, `intersect` or `except` step and its operands.
fn write_set_step(
    f: &mut Formatter<'_>,
    keyword: &str,
    all: bool,
    exprs: &[Expr],
) -> FmtResult {
    write!(f, "{}", keyword)?;
    if all {
        write!(f, " all")?;
    }
    for (i, e) in exprs.iter().enumerate() {
        write!(f, "{} {}", if i > 0 { "," } else { "" }, e)?;
    }
    Ok(())
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
        let t = rel.derive_type().expect("derives a type");
        Expr::Rel(t, Box::new(rel))
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
        let filter =
            Rel::Filter(Box::new(input.clone()), Box::new(cond.clone()));
        assert_eq!(*filter.derive_type().unwrap(), Type::List(int()));

        let bag_input = leaf(int(), Kind::Bag);
        let on_bag = Rel::Filter(Box::new(bag_input.clone()), Box::new(cond));
        assert_eq!(*on_bag.derive_type().unwrap(), Type::Bag(int()));

        // A sort's output is a list whatever its input was, and an
        // unorder's is a bag. These two are why the kind is derived
        // rather than carried.
        let key = Expr::Input(int(), 0);
        let sort =
            Rel::Sort(Box::new(bag_input.clone()), Box::new(key.clone()));
        assert_eq!(*sort.derive_type().unwrap(), Type::List(int()));
        let unorder = Rel::Unorder(Box::new(input.clone()));
        assert_eq!(*unorder.derive_type().unwrap(), Type::Bag(int()));

        // `project`'s element is what its expression builds, so a
        // projection may change the element type.
        let project = Rel::Project(Box::new(input.clone()), Box::new(key));
        assert_eq!(*project.derive_type().unwrap(), Type::List(int()));
        let to_string = Rel::Project(
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
                None,
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
                None,
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
                None,
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

    /// A group builds a record of its keys and aggregates -- unless
    /// there is exactly one field in all, which is how a keyless group
    /// (`compute`) yields a scalar.
    #[test]
    fn group_builds_a_record_or_one_field() {
        let input = leaf(int(), Kind::Bag);
        let key = Expr::Input(int(), 0);
        let total = Expr::Identifier(int(), "total".to_string());
        let two = Rel::Group(
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

        // One aggregate and no keys: the element is the aggregate's own
        // type, not a record of one field.
        let one = Rel::Group(
            Box::new(input),
            vec![],
            vec![(Label::String("total".to_string()), total)],
        );
        assert_eq!(*one.derive_type().unwrap(), Type::Bag(int()));
    }

    /// An input reference is not a variable, so it frees no name. That
    /// is the point of making it a node of its own.
    #[test]
    fn input_reference_is_not_a_variable() {
        use crate::compile::free_finder::free_names_in;
        let input = leaf(int(), Kind::List);
        let filter = node(Rel::Filter(
            Box::new(input),
            Box::new(Expr::Input(int(), 0)),
        ));
        assert!(free_names_in(&filter).contains("r"));
        assert_eq!(free_names_in(&filter).len(), 1);
    }

    /// A dependent join's binder is in scope in its right input, and
    /// nowhere else.
    #[test]
    fn join_binder_is_bound_in_the_right_input() {
        use crate::compile::free_finder::free_names_in;
        let left = Expr::Identifier(Kind::List.apply(int()), "l".to_string());
        let right_reads_binder =
            Expr::Identifier(Kind::List.apply(int()), "v".to_string());
        let join = node(Rel::Join(
            JoinKind::Inner,
            Some("v".to_string()),
            Box::new(Expr::Literal(bool_(), Val::Bool(true))),
            Box::new(left),
            Box::new(right_reads_binder),
        ));
        let free = free_names_in(&join);
        assert!(free.contains("l"));
        assert!(!free.contains("v"), "the binder binds in the right input");
    }
}
