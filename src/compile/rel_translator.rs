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

//! Translates a step list into a relational tree.
//!
//! This is variable elimination. A step list is a sequence of steps
//! each executing in an environment of bindings; a tree's expressions
//! name their input element `$0` and bind nothing. So a binder becomes
//! an expression over `$0` -- the element itself, where the element is
//! that binder's value, otherwise a component or a field of it -- and
//! the binding list disappears, because a node's element type says
//! everything the bindings said.
//!
//! It **declines rather than guesses**: a construct it cannot translate
//! gives `None`, and the caller counts the declines. morel-java's
//! translator does the same, and the count is how it knew when it was
//! finished.
//!
//! Nothing depends on the answer yet. The tree is built beside the step
//! list that does the work, which is what makes this safe to be wrong
//! about: a disagreement shows up as a tree that fails the validator or
//! prints a different plan, with the step list still running the query.

// The translator has no caller outside the tests until the shadow that
// runs it over the corpus lands. Remove when it does.
#![allow(dead_code)]

use crate::compile::core::{
    Binding, Decl, Expr, JoinKind, JoinRows, Match, ORDINAL, Pat, PatField,
    RIGHT_ROW, ROW, Rel, Row, Step, StepEnv, StepKind, ValBind, element_type,
    fresh_name, rename,
};
use crate::compile::free_finder::free_names_in;
use crate::compile::library::BuiltInFunction;
use crate::compile::postfix::peel_type;
use crate::compile::rel_lowerer::map_children;
use crate::compile::rel_validator;
use crate::compile::span::Span;
use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::val::Val;
use crate::syntax::ast::JoinType;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

/// Translates the query `from steps`, whose type is `query_type`, into
/// a tree; or returns `None` where it declines.
pub fn translate(steps: &[Step], query_type: &Rc<Type>) -> Option<Expr> {
    DECLINE.with(|cell| cell.set(None));
    LEAKED.with(|cell| cell.borrow_mut().clear());
    translate_with(
        steps,
        query_type,
        BTreeMap::new(),
        Rc::new(Cell::new(0)),
        false,
    )
}

thread_local! {
    /// Why the translation in progress declined, if it has.
    static DECLINE: Cell<Option<&'static str>> = const { Cell::new(None) };

    /// Binders that were in scope for a step's expression and are still
    /// read by it after the substitution that was supposed to remove
    /// them. Kept beside the tree rather than inside it because the
    /// tree is the thing being checked: see
    /// [`rel_validator::validate_eliminating`].
    static LEAKED: RefCell<BTreeSet<String>> =
        const { RefCell::new(BTreeSet::new()) };
}

/// Returns `e` with every query inside it translated into a tree of
/// its own, where the translation succeeds; a query it declines is
/// left as it is. `e` itself is not a query, or is one the caller has
/// translated already.
pub fn trees_within(e: &Expr) -> Expr {
    DECLINE.with(|cell| cell.set(None));
    LEAKED.with(|cell| cell.borrow_mut().clear());
    let counter = Rc::new(Cell::new(0));
    let map = BTreeMap::new();
    let mut nested = |t: &Rc<Type>, steps: &[Step]| {
        translate_with(steps, t, BTreeMap::new(), Rc::clone(&counter), false)
    };
    substitute_with(e, &map, &mut nested).unwrap_or_else(|| e.clone())
}

/// Returns the binders the last [`translate`] failed to eliminate,
/// which its tree must not read.
pub fn leaked() -> BTreeSet<String> {
    LEAKED.with(|cell| cell.borrow().clone())
}

/// Records why the translator is declining, and declines.
///
/// It declines rather than guesses, and saying why is what turns the
/// count of declines into a list of what to build next. A reason is
/// written where the decision is taken, and the *first* one stands: an
/// outer caller sees the `None` too, and a coarse reason written there
/// would bury the exact one underneath it.
fn decline<T>(reason: &'static str) -> Option<T> {
    DECLINE.with(|cell| {
        if cell.get().is_none() {
            cell.set(Some(reason));
        }
    });
    None
}

/// Forgets the reason, for a decline that was only an attempt: what it
/// says is about a path not taken.
fn forget_decline() {
    DECLINE.with(|cell| cell.set(None));
}

/// Translates a query whose expressions may read the names in `outer`,
/// which is how a nested tree reads the row that encloses it.
/// `nested` says whether the query is inside another being translated.
fn translate_with(
    steps: &[Step],
    query_type: &Rc<Type>,
    outer: BTreeMap<String, Expr>,
    counter: Rc<Cell<usize>>,
    nested: bool,
) -> Option<Expr> {
    let mut t = Translator {
        tree: None,
        bindings: Vec::new(),
        outer,
        counter,
        in_scope: Vec::new(),
        nested,
    };
    for step in steps {
        t.step(step)?;
    }
    // A query with no steps iterates over one unit row, and `[()]` is
    // that row: `from` is `[()]`, and the leaf its author did not
    // write is the whole of why the answer has one row rather than
    // none. Only a step asks for the leaf, so a query with no steps
    // asks here.
    let tree = t.tree.take().unwrap_or_else(unit_leaf);
    if tree.type_() == *query_type && t.binders_are_the_element(&tree) {
        return Some(tree);
    }
    // A query that computes an aggregate is a value, not a collection:
    // `compute` is a group with no keys, and the single element is
    // taken out by the expression that holds the query. So the tree's
    // *element* is what the query's type is, and there is nothing to
    // name.
    if element_type(query_type).is_none() {
        if element_type(&tree.type_()).as_ref() == Some(query_type) {
            return Some(tree);
        }
        return decline("a query whose type is not a collection");
    }
    // A query with several binders has a row that no step built: the
    // step list carries the binders in an environment, and the tree's
    // element is its inputs' components. So it ends in a projection
    // that names them -- which is where the names a tree does not hold
    // come back. This is also the check: if the projection does not
    // give the query's own type, the translation is wrong and declines
    // rather than printing a plan for a different query.
    // `name_the_components` says why it could not, which is exact
    // where a reason written here would be coarse.
    let tree = t.name_the_components(tree, query_type)?;
    if tree.type_() != *query_type {
        return decline("a tree whose type is not the query's");
    }
    Some(tree)
}

thread_local! {
    /// What the shadow has seen since it was last taken.
    static SHADOW: RefCell<Shadow> = RefCell::new(Shadow::default());
}

/// What translating every query a script compiles turned up.
#[derive(Default)]
pub struct Shadow {
    /// Queries that became a tree.
    pub translated: usize,
    /// Queries the translator declined, which is not a fault: it
    /// declines rather than guesses. The count is the coverage we do
    /// not have yet.
    pub declined: usize,
    /// How many declined for each reason, which is what says where the
    /// coverage is worth buying next. A decline with no reason is
    /// itself a finding: something returned `None` without saying so.
    pub reasons: BTreeMap<&'static str, usize>,
    /// The first query to decline for each reason. A count says how
    /// much, and this says what: a reason on its own is not enough to
    /// go and look.
    pub examples: BTreeMap<&'static str, String>,
    /// Trees the validator complained about, each with the query it
    /// came from. Every one is a bug -- here, or in morel-java, or in
    /// what `spec.md` meant -- and the query is enough to find it.
    pub invalid: Vec<String>,
}

/// Translates every query in `decl`, and records what happened without
/// printing anything.
///
/// morel-java's step-1 technique, and the cheapest bug detector on
/// offer. The tree is built beside the step list that does the work,
/// so a disagreement here is a finding rather than a regression:
/// nothing depends on the answer.
///
/// [`translate`] already declines where the tree's type is not the
/// query's, so that half of the check is inside it and a failure shows
/// up as a decline. What is left is the validator, and it is asked of
/// every tree.
pub fn shadow(decl: &Decl) {
    shadow_decl(decl);
}

/// Returns what the shadow has seen, and forgets it.
pub fn take_shadow() -> Shadow {
    SHADOW.with(RefCell::take)
}

fn shadow_query(exp: &Expr, steps: &[Step]) {
    let tree = translate(steps, &exp.type_());
    let reason = DECLINE.with(Cell::get);
    SHADOW.with(|cell| {
        let mut shadow = cell.borrow_mut();
        match &tree {
            None => {
                shadow.declined += 1;
                let reason = reason.unwrap_or("unsaid");
                *shadow.reasons.entry(reason).or_default() += 1;
                shadow
                    .examples
                    .entry(reason)
                    .or_insert_with(|| format!("{}", exp));
            }
            Some(tree) => {
                shadow.translated += 1;
                let leaked = leaked();
                for error in rel_validator::validate_eliminating(tree, &leaked)
                {
                    shadow.invalid.push(format!("{}: {}", error, exp));
                }
            }
        }
    });
}

fn shadow_decl(decl: &Decl) {
    match decl {
        Decl::NonRecVal(b) => shadow_expr(&b.expr),
        Decl::RecVal(binds) => binds.iter().for_each(|b| shadow_expr(&b.expr)),
        Decl::Datatype(_) | Decl::Over(_) | Decl::Type(_) => {}
    }
}

fn shadow_expr(e: &Expr) {
    match e {
        // A query, and then what its steps hold: a query nested inside
        // another is a query too, and is where the interesting cases
        // are.
        Expr::From(_, steps) => {
            shadow_query(e, steps);
            steps.iter().for_each(shadow_step);
        }
        Expr::Aggregate(_, a, b, _) | Expr::Apply(_, a, b, _) => {
            shadow_expr(a);
            shadow_expr(b);
        }
        Expr::Case(_, subject, arms, _) => {
            shadow_expr(subject);
            arms.iter().for_each(|m| shadow_expr(&m.expr));
        }
        Expr::Fn(_, arms, _) => {
            arms.iter().for_each(|m| shadow_expr(&m.expr));
        }
        Expr::Let(_, decls, body) => {
            decls.iter().for_each(shadow_decl);
            shadow_expr(body);
        }
        Expr::List(_, items) | Expr::Tuple(_, items) => {
            items.iter().for_each(shadow_expr);
        }
        Expr::Raise(_, a, _) => shadow_expr(a),
        Expr::Rel(_, rel) => rel.children().into_iter().for_each(shadow_expr),
        Expr::Current(_)
        | Expr::Extent(_, _)
        | Expr::Identifier(_, _)
        | Expr::Literal(_, _)
        | Expr::Ordinal(_)
        | Expr::RecordSelector(_, _) => {}
    }
}

fn shadow_step(step: &Step) {
    match &step.kind {
        StepKind::Scan(_, source, condition) => {
            shadow_expr(source);
            condition.iter().for_each(|c| shadow_expr(c));
        }
        StepKind::Compute(e)
        | StepKind::Order(e)
        | StepKind::Skip(e)
        | StepKind::Take(e)
        | StepKind::Where(e)
        | StepKind::Yield(e) => shadow_expr(e),
        StepKind::Group(keys, aggregates) => {
            shadow_expr(keys);
            aggregates.iter().for_each(|a| shadow_expr(a));
        }
        StepKind::Except(_, inputs)
        | StepKind::Intersect(_, inputs)
        | StepKind::Union(_, inputs) => inputs.iter().for_each(shadow_expr),
        _ => {}
    }
}

/// Where in its input's element a binder's value is.
///
/// A binder is not an expression until the element type is known, and
/// the element type changes under it: a join makes the element a tuple
/// of components, so a binder that was the whole element becomes the
/// first of them, and the components' own types grow as further inputs
/// join. Holding the path and reading it against the current element
/// keeps every binder right after each step, where holding the
/// expression would leave the earlier ones stale.
#[derive(Clone, Debug)]
struct Path(Vec<Hop>);

/// One step of a [`Path`].
#[derive(Clone, Debug)]
enum Hop {
    /// Component `i` of a tuple, 1-based as the source writes it.
    Component(usize),
    /// Field `label` of a record, which a `yield` of a record makes.
    Field(String),
    /// The row's position, `$ordinal`, which is not read out of the
    /// element at all: a node that counts its rows binds it beside
    /// `$0`.
    Ordinal,
}

impl Path {
    /// The element itself, `$0`.
    fn whole() -> Path {
        Path(Vec::new())
    }

    /// Component `i` of the element.
    fn component(i: usize) -> Path {
        Path(vec![Hop::Component(i)])
    }

    /// Field `label` of the element.
    fn field(label: &str) -> Path {
        Path(vec![Hop::Field(label.to_string())])
    }

    /// The row's position, `$ordinal`.
    fn ordinal() -> Path {
        Path(vec![Hop::Ordinal])
    }

    /// Returns whether this path is the row's position.
    fn is_ordinal(&self) -> bool {
        matches!(self.0.as_slice(), [Hop::Ordinal])
    }

    /// Returns this path read from inside component `i` instead of
    /// from the element, which is what a join does to the paths its
    /// inputs' binders had.
    fn under(&self, i: usize) -> Path {
        let mut hops = vec![Hop::Component(i)];
        hops.extend(self.0.iter().cloned());
        Path(hops)
    }

    /// Returns this path followed by one more hop, which is what a
    /// pattern does as it nests.
    fn then(&self, hop: Hop) -> Path {
        let mut hops = self.0.clone();
        hops.push(hop);
        Path(hops)
    }

    /// Returns the expression that reads this path out of the element
    /// of the node's only input, `$0`.
    fn read(&self, elem: &Rc<Type>) -> Option<Expr> {
        self.read_at(elem, 0)
    }

    /// Returns the expression that reads this path out of the element
    /// of input `index`. A join's condition sees `$0` and `$1`, its
    /// two inputs' elements, where every other expression sees only
    /// `$0`.
    fn read_at(&self, elem: &Rc<Type>, index: usize) -> Option<Expr> {
        self.read_from(row_ref(elem, index))
    }

    /// Returns the expression that reads this path out of `base`, which
    /// names an element. A dependent join's binder names the left
    /// element by an ordinary variable, and its right input reads the
    /// left binders through that.
    fn read_from(&self, base: Expr) -> Option<Expr> {
        let mut e = base;
        for hop in &self.0 {
            e = hop.read_from(e)?;
        }
        Some(e)
    }
}

impl Hop {
    /// Returns the expression that takes this step out of `base`.
    fn read_from(&self, base: Expr) -> Option<Expr> {
        let elem = base.type_();
        // A path that does not fit the element it is read out of is a
        // bookkeeping mistake rather than a gap, so it says so: a
        // binder's place was recorded against one element and read
        // against another.
        match self {
            // A record has components too, and they are its fields in
            // label order: `from (dno, name, loc) in scott.depts`
            // takes a record apart with a tuple pattern, and the
            // pattern is positional where the element is not.
            Hop::Component(i) => {
                let types: Vec<Rc<Type>> = match peel(&elem) {
                    Type::Tuple(types) => types.clone(),
                    Type::Record(_, fields) => {
                        fields.values().cloned().collect()
                    }
                    _ => {
                        return decline(
                            "a component of an element that has none",
                        );
                    }
                };
                match types.get(i - 1) {
                    None => decline("a component the element does not have"),
                    Some(t) => Some(selector(base, i - 1, t.clone())),
                }
            }
            Hop::Field(label) => {
                let Type::Record(_, fields) = peel(&elem) else {
                    return decline("a field of an element that has none");
                };
                match fields.keys().position(|l| l.matches(label)) {
                    None => decline("a field the element does not have"),
                    Some(slot) => {
                        let t = fields.values().nth(slot)?.clone();
                        Some(selector(base, slot, t))
                    }
                }
            }
            // The position is bound beside the element, not inside it,
            // so the base is not read; but only the node that counts
            // the rows binds it, so it can be read only where the base
            // is that node's row. Read through a join's component, or
            // from a dependent join's right input, it would count
            // other rows.
            Hop::Ordinal => {
                if !is_row(&base) {
                    return decline("`ordinal` read where its rows are not");
                }
                Some(ordinal_ref())
            }
        }
    }
}

/// What a query's binders have become, as the translation walks its
/// steps.
struct Translator {
    /// The tree built so far. `None` before the first step; a query
    /// with no scan gets the unit leaf.
    tree: Option<Expr>,
    /// Where each binder's value is in the current element, in the
    /// order the query bound them.
    bindings: Vec<(String, Path)>,
    /// Names bound outside this tree that its expressions may read:
    /// the binder that a dependent join carries, resolved to what it
    /// names in the left element. A nested tree reads its enclosing row
    /// only this way, because `$0` is its own (spec.md §2 rule 3).
    outer: BTreeMap<String, Expr>,
    /// Supplies the names of the parameters of the converters that
    /// [`Translator::converted`] composes, `col$N`. Shared with the
    /// translators of nested trees, so that no two in one statement
    /// have the same name; uniqueness is all allocation owes, because
    /// the printer renumbers what it prints. Every other binder the
    /// translation invents is named by [`fresh_name`].
    counter: Rc<Cell<usize>>,
    /// What the previous step's environment bound, and therefore what
    /// this step's expressions may read and this step's rewrite must
    /// remove. It is the compiler's answer rather than `bindings`,
    /// which is the translation's, so that a wrong `bindings` is caught
    /// rather than agreed with.
    in_scope: Vec<String>,
    /// Whether this query is inside another that is being translated.
    ///
    /// An expression a query evaluates once rather than once per row
    /// -- its first scan's source, a `skip` or `take` count, a set
    /// operand -- reads `ordinal` as the position of the enclosing
    /// step's row. Here no node binds that position, so the
    /// placeholder is left for the enclosing query, whose node for that
    /// step binds it; where it cannot, the enclosing query declines.
    /// A query inside nothing has no enclosing step, and declines.
    nested: bool,
}

impl Translator {
    /// Translates one step, or declines, and records what the next
    /// step's expressions may read.
    ///
    /// The names come from the step's own environment and not from
    /// `self.bindings`, because they are what the check is made of and
    /// the two must not be the same guess: a translation that works out
    /// the wrong name for a binder would agree with itself and say
    /// nothing.
    fn step(&mut self, step: &Step) -> Option<()> {
        let result = self.translate_step(step);
        self.in_scope = step
            .env
            .bindings
            .iter()
            .map(|b| b.id.name.clone())
            .collect();
        result
    }

    /// Translates one step, or declines.
    fn translate_step(&mut self, step: &Step) -> Option<()> {
        // A query with no scan iterates over a single element, which
        // is unit, so its leaf is `[()]` -- a leaf its author did not
        // write, and the whole of why the answer has one row rather
        // than none. See spec.md §3.1.
        if self.tree.is_none() && !matches!(step.kind, StepKind::Scan(..)) {
            self.tree = Some(unit_leaf());
        }
        match &step.kind {
            StepKind::Scan(pat, source, condition) => {
                self.scan(pat, source, condition.as_deref(), step.join_type)
            }
            StepKind::Where(condition) => {
                let condition = self.rewrite(condition)?;
                self.wrap(|input| {
                    Rel::Filter(Row::placeholder(), input, Box::new(condition))
                })
            }
            StepKind::Yield(e) => self.yield_(e, &step.env),
            StepKind::Order(e) => {
                let key = self.rewrite(e)?;
                self.wrap(|input| {
                    Rel::Sort(Row::placeholder(), input, Box::new(key))
                })
            }
            StepKind::Skip(n) => {
                let n = self.count(n)?;
                self.wrap(|input| Rel::Skip(input, Box::new(n)))
            }
            StepKind::Take(n) => {
                let n = self.count(n)?;
                self.wrap(|input| Rel::Take(input, Box::new(n)))
            }
            StepKind::Unorder => self.wrap(Rel::Unorder),
            // A set operator's flag is whether it keeps duplicates;
            // the node's is whether it removes them.
            StepKind::Except(all, inputs) => {
                self.set_op(*all, inputs, Rel::Except)
            }
            StepKind::Intersect(all, inputs) => {
                self.set_op(*all, inputs, Rel::Intersect)
            }
            StepKind::Union(all, inputs) => {
                self.set_op(*all, inputs, Rel::Union)
            }
            StepKind::Group(keys, aggregates) => {
                self.group(keys, aggregates.as_deref())
            }
            // `compute` is a group with no keys, plus the extraction of
            // the single element that the enclosing expression
            // performs.
            StepKind::Compute(aggregates) => self.group_of(vec![], aggregates),
            // `distinct` is a group on every binder with no aggregate,
            // which is what the compiler makes of it too, so it needs
            // no node of its own.
            StepKind::Distinct => self.distinct(),
            // `exists` short-circuits a query into a boolean, and none
            // of `spec.md` §3's eleven constructors does that. It is
            // not missing coverage; there is nothing to build.
            StepKind::Exists => decline("a query that tests for existence"),
        }
    }

    /// Translates a scan: the first is the tree's leaf, and a later one
    /// joins.
    fn scan(
        &mut self,
        pat: &Pat,
        source: &Expr,
        condition: Option<&Expr>,
        join_type: JoinType,
    ) -> Option<()> {
        // Where each name the pattern binds sits in the element. A
        // pattern that can fail becomes a filter and a projection, and
        // is more than this does.
        let Some(paths) = binder_paths(pat) else {
            return decline("a scan pattern that is not a name or a tuple");
        };
        // A pattern that can fail filters as well as binds, and the two
        // halves are separate nodes: the filter goes over the scan's
        // own source, where the element it tests is `$0`.
        let mut tests = Vec::new();
        let Some(source_elem) = element_type(&source.type_()) else {
            return decline("a scan over something that is not a collection");
        };
        if pat_tests(pat, &Path::whole(), &source_elem, &mut tests).is_none() {
            return decline("a scan pattern that cannot be tested");
        }
        let test = all_of(tests);
        match self.tree.take() {
            None => {
                // The first scan is the tree's leaf, and has nothing to
                // join against, so neither a condition nor an outer
                // kind can mean anything here.
                if condition.is_some() || join_type != JoinType::Inner {
                    return decline("a first scan with a condition or a kind");
                }
                self.tree =
                    Some(filtered(self.source_tree(source, true)?, test)?);
                self.bindings = paths;
            }
            Some(left) => {
                // A scan that reads an earlier binder is a dependent
                // join: the join carries a binder, and its right input
                // reads the left element through it. Dependence is not
                // a mode of the node -- it is the free occurrence of
                // that binder, which is why decorrelation is dropping
                // the binder rather than rewriting one node into
                // another.
                let mut rows = JoinRows::placeholder();
                let right;
                if reads_a_binding(source, &self.bindings) {
                    // A correlated outer join, or one carrying a
                    // condition as well, is more than this does.
                    if condition.is_some() || join_type != JoinType::Inner {
                        self.tree = Some(left);
                        return decline("a correlated outer join");
                    }
                    let name = self.new_binder();
                    if let Some(tree) = self.correlated(source, &left, &name) {
                        rows = JoinRows::dependent(name);
                        right = tree;
                    } else {
                        self.tree = Some(left);
                        return None;
                    }
                } else {
                    right = self.source_tree(source, false)?;
                }
                let right = filtered(right, test)?;
                let n = components_of(&left) + 1;
                // The condition sees the two inputs' elements as `$0`
                // and `$1`, and both are present whatever the kind --
                // where the join's *element* wraps a side that may be
                // absent. So it is rewritten against the inputs, not
                // against the row the join produces.
                let condition = match condition
                    .map(|c| self.join_condition(c, &left, &right, &paths))
                {
                    None => true_literal(),
                    Some(Some(c)) => c,
                    // The condition reads something this cannot
                    // rewrite, so the whole query is declined rather
                    // than joined on the wrong terms.
                    Some(None) => {
                        self.tree = Some(left);
                        return decline("a join condition");
                    }
                };
                let kind = match join_type {
                    JoinType::Inner => JoinKind::Inner,
                    JoinType::Left => JoinKind::Left,
                    JoinType::Right => JoinKind::Right,
                    JoinType::Full => JoinKind::Full,
                };
                let join = Rel::Join(
                    kind,
                    rows,
                    Box::new(condition),
                    Box::new(left),
                    Box::new(right),
                );
                let tree = node(join)?;
                // The components concatenate, so a tree that had one
                // component becomes the first of them and its binders
                // read through it; one that was a join already has its
                // binders addressed by component, and keeps them.
                if n == 2 {
                    for (_, path) in &mut self.bindings {
                        *path = path.under(1);
                    }
                }
                for (bound, path) in paths {
                    self.bindings.push((bound, path.under(n)));
                }
                self.tree = Some(tree);
            }
        }
        Some(())
    }

    /// Translates a `yield`: a projection, whose element is what the
    /// expression builds, and whose value names what the query called
    /// its binders.
    fn yield_(&mut self, e: &Expr, env: &StepEnv) -> Option<()> {
        // A `yield` the resolver added to carry `ordinal` in the row
        // adds no node: a tree binds the position beside the element,
        // so the binder reads `$ordinal` from here on.
        if let Some(name) = self.materialized_ordinal(e) {
            self.bindings.push((name, Path::ordinal()));
            return Some(());
        }
        let value = self.rewrite(e)?;
        let elem = value.type_();
        // A projection of the element itself changes nothing, and is
        // the `yield` that puts the row back after `ordinal` is done
        // with.
        if !is_row(&value) {
            self.wrap(|input| {
                Rel::Project(Row::placeholder(), input, Box::new(value))
            })?;
        }
        self.bindings = bindings_over(env, &elem)?;
        Some(())
    }

    /// Returns the name of the field under which a `yield` carries
    /// `ordinal`, where the `yield` is one the resolver added for that
    /// and nothing else: every other field is a binder yielded as
    /// itself.
    fn materialized_ordinal(&self, e: &Expr) -> Option<String> {
        let Expr::Tuple(t, exprs) = e else {
            return None;
        };
        let Type::Record(_, fields) = t.as_ref() else {
            return None;
        };
        let mut ordinal = None;
        for (label, value) in fields.keys().zip(exprs) {
            let Label::String(name) = label else {
                return None;
            };
            match value {
                Expr::Ordinal(_) if name.starts_with("ordinal$") => {
                    ordinal = Some(name.clone());
                }
                Expr::Identifier(_, id)
                    if id == name
                        && self.bindings.iter().any(|(b, _)| b == name) => {}
                _ => return None,
            }
        }
        ordinal
    }

    /// Rewrites a `skip` or `take` count, which is evaluated once,
    /// before any row, and so cannot read a row's position.
    fn count(&self, n: &Expr) -> Option<Expr> {
        let n = self.rewrite(n)?;
        if reads_ordinal(&n) && !self.nested {
            return decline("a count that reads `ordinal`");
        }
        Some(n)
    }

    /// Translates a scan's source. A query of its own is a tree of its
    /// own, and anything else is a leaf whose names may need changing.
    ///
    /// The first scan's source is evaluated once, so an `ordinal` in it
    /// counts the rows of an enclosing step; see [`Translator::nested`].
    /// A later scan's is evaluated once per row of the scans before it,
    /// and no node binds a position for those.
    fn source_tree(&self, source: &Expr, first: bool) -> Option<Expr> {
        let tree = self.source_tree2(source)?;
        if reads_ordinal(&tree) && !(first && self.nested) {
            return decline("a scan source that reads `ordinal`");
        }
        Some(tree)
    }

    fn source_tree2(&self, source: &Expr) -> Option<Expr> {
        match source {
            Expr::From(t, steps) => translate_with(
                steps,
                t,
                self.outer.clone(),
                Rc::clone(&self.counter),
                true,
            ),
            leaf => match substitute(leaf, &self.outer) {
                None => decline("a scan source over the enclosing row"),
                some => some,
            },
        }
    }

    /// Returns the names a tree nested in this one reads, with the
    /// query's binders read through `binder`, the name the row goes by
    /// there, and a binder that is the row's position as `ordinal`.
    ///
    /// Where there is no name for the position -- a dependent join
    /// binds none -- such a binder is left out, and
    /// [`Translator::reads_skipped`] says whether the nested tree
    /// wanted it.
    fn outer_through(
        &self,
        binder: &Expr,
        ordinal: Option<&Expr>,
    ) -> Option<BTreeMap<String, Expr>> {
        let mut outer = self.outer.clone();
        for (bound, path) in &self.bindings {
            if path.is_ordinal() {
                if let Some(ordinal) = ordinal {
                    outer.insert(bound.clone(), ordinal.clone());
                }
                continue;
            }
            outer.insert(bound.clone(), path.read_from(binder.clone())?);
        }
        Some(outer)
    }

    /// Returns whether an expression still reads a binder that
    /// [`Translator::outer_through`] left out.
    fn reads_skipped(&self, e: &Expr, outer: &BTreeMap<String, Expr>) -> bool {
        let free = free_names_in(e);
        self.bindings.iter().any(|(bound, _)| {
            !outer.contains_key(bound) && free.contains(bound)
        })
    }

    /// Returns a fresh name for a binder the translation invents.
    fn new_binder(&self) -> String {
        fresh_name()
    }

    /// Translates the right input of a dependent join: the scan's
    /// source, with the left binders read through `name`, which the
    /// join binds to the left element.
    fn correlated(
        &self,
        source: &Expr,
        left: &Expr,
        name: &str,
    ) -> Option<Expr> {
        let Some(left_elem) = element_type(&left.type_()) else {
            return decline("a join whose left is not a collection");
        };
        let binder = Expr::Identifier(left_elem, name.to_string());
        let outer = self.outer_through(&binder, None)?;
        let tree = match source {
            // The source is a query of its own, so it is a tree of its
            // own, whose `$0` is its own element.
            Expr::From(t, steps) => translate_with(
                steps,
                t,
                outer.clone(),
                Rc::clone(&self.counter),
                true,
            ),
            // Otherwise it is a leaf, and only its names change.
            leaf => substitute(leaf, &outer),
        }?;
        if reads_ordinal(&tree) || self.reads_skipped(&tree, &outer) {
            return decline("a scan source that reads `ordinal`");
        }
        Some(tree)
    }

    /// Rewrites a join's `on` condition. The binders the left input
    /// bound read `$0`, its element; the binder the scan introduces
    /// reads `$1`, the right element.
    fn join_condition(
        &self,
        condition: &Expr,
        left: &Expr,
        right: &Expr,
        paths: &[(String, Path)],
    ) -> Option<Expr> {
        let (Some(left_elem), Some(right_elem)) =
            (element_type(&left.type_()), element_type(&right.type_()))
        else {
            return decline("a join whose input is not a collection");
        };
        let mut map = self.outer.clone();
        for (bound, path) in &self.bindings {
            map.insert(bound.clone(), path.read_at(&left_elem, 0)?);
        }
        for (bound, path) in paths {
            map.insert(bound.clone(), path.read_at(&right_elem, 1)?);
        }
        // A join's condition sees pairs of rows, and a join binds no
        // position for either of them.
        let condition = substitute(condition, &map)?;
        if reads_ordinal(&condition) {
            return decline("a join condition that reads `ordinal`");
        }
        Some(condition)
    }

    /// Translates a `group`: the keys and the aggregates, each a list
    /// of labelled expressions over `$0`.
    fn group(&mut self, keys: &Expr, aggregates: Option<&Expr>) -> Option<()> {
        let Some(keys) = labelled_parts(keys) else {
            return decline("a group's keys");
        };
        match aggregates {
            None => self.group_parts(keys, vec![]),
            Some(aggregates) => match labelled_parts(aggregates) {
                None => decline("a group's aggregates"),
                Some(aggregates) => self.group_parts(keys, aggregates),
            },
        }
    }

    /// Translates `distinct`: a group whose keys are the whole element
    /// and whose aggregate list is empty (`spec.md` §3.2).
    ///
    /// The binders are how the element is taken apart, and together
    /// they are the whole of it, so one key each reconstructs the row
    /// the query wrote and reads as the query wrote it. Where the
    /// query bound no name at all -- `yield i + j distinct`, whose row
    /// is a value nothing names -- the key is the element itself,
    /// under a name the printer made: §6.7's `v$` is exactly the
    /// vocabulary for a name that is not the query's.
    fn distinct(&mut self) -> Option<()> {
        let Some(elem) =
            self.tree.as_ref().and_then(|t| element_type(&t.type_()))
        else {
            return decline(
                "a `distinct` over a tree that is not a collection",
            );
        };
        if self.bindings.is_empty() {
            let name = Label::String(self.new_binder());
            return self.group_parts(vec![(name, row_ref(&elem, 0))], vec![]);
        }
        let mut keys = Vec::with_capacity(self.bindings.len());
        for (name, path) in &self.bindings {
            keys.push((Label::String(name.clone()), path.read(&elem)?));
        }
        self.group_parts(keys, vec![])
    }

    /// Translates a group whose aggregates are an expression and whose
    /// keys are already known.
    fn group_of(
        &mut self,
        keys: Vec<(Label, Expr)>,
        aggregates: &Expr,
    ) -> Option<()> {
        let Some(aggregates) = labelled_parts(aggregates) else {
            return decline("a compute's aggregates");
        };
        self.group_parts(keys, aggregates)
    }

    /// Builds the `group` node and rebinds the query's names to the
    /// record it produces.
    fn group_parts(
        &mut self,
        keys: Vec<(Label, Expr)>,
        aggregates: Vec<(Label, Expr)>,
    ) -> Option<()> {
        let rewrite = |t: &Self, parts: Vec<(Label, Expr)>| {
            parts
                .into_iter()
                .map(|(label, e)| Some((label, t.rewrite(&e)?)))
                .collect::<Option<Vec<_>>>()
        };
        let keys = rewrite(self, keys)?;
        let aggregates = aggregates
            .into_iter()
            .map(|(label, e)| Some((label, self.rows(e)?)))
            .collect::<Option<Vec<_>>>()?;
        let aggregates = rewrite(self, aggregates)?;
        let names: Vec<Label> = keys
            .iter()
            .chain(aggregates.iter())
            .map(|(label, _)| label.clone())
            .collect();
        let aggregates = self.converted(aggregates)?;
        self.wrap(|input| {
            Rel::Group(Row::placeholder(), input, keys, aggregates)
        })?;
        // The element is a record of the keys and the aggregates, a
        // record whether there is one field or many, so each is read
        // by its label. Where the query wants the bare value of its
        // one field, the projection that closes the query says so.
        self.bindings = names
            .iter()
            .filter_map(|label| match label {
                Label::String(name) => Some((name.clone(), Path::field(name))),
                Label::Ordinal(_) => None,
            })
            .collect();
        Some(())
    }

    /// Composes each aggregate whose function takes a bag with a
    /// converter, where the input is a list: `fn col$0 => count
    /// (#fromList Bag col$0) over ()`. The parameter takes a generated
    /// name that does not start with `$`, because a `$` name is a
    /// node's pattern. This is what morel-java's resolver does, and
    /// the plan text shows it.
    fn converted(
        &self,
        aggregates: Vec<(Label, Expr)>,
    ) -> Option<Vec<(Label, Expr)>> {
        let ordered = self
            .tree
            .as_ref()
            .is_some_and(|t| matches!(peel(&t.type_()), Type::List(_)));
        if !ordered {
            return Some(aggregates);
        }
        Some(
            aggregates
                .into_iter()
                .map(|(label, e)| {
                    let Expr::Aggregate(t, f, arg, span) = e else {
                        return (label, e);
                    };
                    if !takes_bag(&f) {
                        return (label, Expr::Aggregate(t, f, arg, span));
                    }
                    let elem = arg.type_();
                    let list_t = Rc::new(Type::List(elem.clone()));
                    let bag_t = Rc::new(Type::Bag(elem));
                    let name = format!("col${}", self.counter.get());
                    self.counter.set(self.counter.get() + 1);
                    let param = Expr::Identifier(list_t.clone(), name.clone());
                    let converter = Expr::Literal(
                        Rc::new(Type::Fn(list_t.clone(), bag_t.clone())),
                        Val::Fn(BuiltInFunction::BagFromList),
                    );
                    let converted = Expr::Apply(
                        bag_t,
                        Box::new(converter),
                        Box::new(param),
                        span.clone(),
                    );
                    let applied = Expr::Apply(
                        t.clone(),
                        f,
                        Box::new(converted),
                        span.clone(),
                    );
                    let composed = Expr::Fn(
                        Rc::new(Type::Fn(list_t.clone(), t.clone())),
                        vec![Match {
                            pat: Pat::Identifier(list_t, name),
                            expr: applied,
                        }],
                        span.clone(),
                    );
                    (label, Expr::Aggregate(t, Box::new(composed), arg, span))
                })
                .collect(),
        )
    }

    /// Turns `elements`, which is a group's rows, into the aggregate it
    /// stands for: the identity function over the whole element.
    ///
    /// `elements` is a name the compiler answers out of the group's
    /// frame rather than out of any binding, so it survives
    /// substitution and leaves the tree naming something no node
    /// defines. morel-java's resolver writes it as `#id Fn over $0`,
    /// which `spec.md` §3's `group` already expresses, so there is
    /// nothing to add to the datatype -- only the rewrite the resolver
    /// does and we did not. A group that bound the name itself keeps
    /// it, because then it is an ordinary binder and substitution has
    /// the answer.
    fn rows(&self, e: Expr) -> Option<Expr> {
        let Expr::Identifier(t, name) = &e else {
            return Some(e);
        };
        if name != "elements"
            || self.bindings.iter().any(|(bound, _)| bound == name)
        {
            return Some(e);
        }
        let Some(elem) =
            self.tree.as_ref().and_then(|t| element_type(&t.type_()))
        else {
            return decline("`elements` over a tree that is not a collection");
        };
        Some(Expr::Aggregate(
            t.clone(),
            Box::new(Expr::Literal(
                Rc::new(Type::Fn(t.clone(), t.clone())),
                Val::Fn(BuiltInFunction::FnId),
            )),
            Box::new(row_ref(&elem, 0)),
            Span::new(""),
        ))
    }

    /// Translates a set operator: the tree so far, and the step's
    /// inputs.
    fn set_op(
        &mut self,
        distinct: bool,
        inputs: &[Expr],
        f: impl FnOnce(bool, Vec<Expr>) -> Rel,
    ) -> Option<()> {
        let mut left = self.tree.take()?;
        // The operands are rows the query wrote, and after several
        // binders the tree's element is its inputs' components, which
        // have no names. So the components are named first, here rather
        // than at the end: a set operator compares its inputs element
        // by element, and two elements of different shapes are not
        // comparable at all. Found by the shadow, on
        // `from j in [1, 2] join i in ["x", "y"] except [...]`, which
        // built an `except` over `int * string` and `{i:string, j:int}`
        // and let the validator say so.
        let Some(operand) = inputs.first() else {
            return decline("a set operator with no operand");
        };
        if element_type(&left.type_()) != element_type(&operand.type_()) {
            let named = self.name_the_components(left, &operand.type_())?;
            left = named;
            // The element is now the record the binders name, so each
            // binder reads its own field of it.
            self.bindings = self
                .bindings
                .iter()
                .map(|(name, _)| (name.clone(), Path::field(name)))
                .collect();
        }
        let mut all_inputs = vec![left];
        for operand in inputs {
            all_inputs.push(self.rewrite_operand(operand)?);
        }
        self.tree = Some(node(f(distinct, all_inputs))?);
        // A set operator's element is its inputs', so the binder that
        // named the element still does.
        Some(())
    }

    /// Rewrites a set operator's operand.
    ///
    /// An operand is a collection compared with the tree element by
    /// element, not an expression evaluated once per row, so it does
    /// not read `$0` and the binders over `$0` are not in its map.
    /// What it may read is `outer`, the row of an enclosing query --
    /// which is how `from x in [10, 20] yield (from i in [1, 2] union
    /// [current])` reaches `x` -- and a query it holds is a tree of
    /// its own, translated here rather than left as the step list it
    /// arrived as.
    fn rewrite_operand(&self, e: &Expr) -> Option<Expr> {
        let counter = Rc::clone(&self.counter);
        let outer = self.outer.clone();
        let operand = substitute_with(e, &self.outer, &mut |t, steps| {
            translate_with(steps, t, outer.clone(), Rc::clone(&counter), true)
        })?;
        // An operand is evaluated once, so an `ordinal` in it counts
        // the rows of an enclosing step; see [`Translator::nested`].
        if reads_ordinal(&operand) && !self.nested {
            return decline("a set operand that reads `ordinal`");
        }
        Some(operand)
    }

    /// Adds the projection that builds the query's row out of the
    /// components the tree's element holds.
    /// Reports whether the query's binders read the element as it
    /// is: one binder that is the whole element, or one binder per
    /// field, each reading the field of its own name. A pattern that
    /// permutes a record's fields, `{b = c, c = a, a = b}`, does not,
    /// and needs the projection that names the components even
    /// though the types agree.
    fn binders_are_the_element(&self, tree: &Expr) -> bool {
        match self.bindings.as_slice() {
            [] => true,
            [(_, path)] if path.0.is_empty() => true,
            bindings => {
                let Some(elem) = element_type(&tree.type_()) else {
                    return false;
                };
                let Type::Record(_, fields) = peel(&elem) else {
                    return false;
                };
                let labels: Vec<&Label> = fields.keys().collect();
                bindings.len() == labels.len()
                    && bindings.iter().all(|(name, path)| {
                        match path.0.as_slice() {
                            [Hop::Field(label)] => label == name,
                            [Hop::Component(i)] => labels
                                .get(i - 1)
                                .is_some_and(|l| l.matches(name)),
                            _ => false,
                        }
                    })
            }
        }
    }

    fn name_the_components(
        &self,
        tree: Expr,
        query_type: &Rc<Type>,
    ) -> Option<Expr> {
        let Some(row) = element_type(query_type) else {
            return decline("a query whose type is not a collection");
        };
        let Some(elem) = element_type(&tree.type_()) else {
            return decline("a tree whose type is not a collection");
        };
        // One binder, and the row is its value: the element atomizes
        // rather than becoming a record of one field. `from (x, 20) in
        // pairs` answers a list of `x`, not of `{x = x}`.
        if let [(_, path)] = self.bindings.as_slice() {
            let value = path.read(&elem)?;
            if value.type_() == row {
                return node(Rel::Project(
                    Row::placeholder(),
                    Box::new(tree),
                    Box::new(value),
                ));
            }
        }
        let Type::Record(_, fields) = peel(&row) else {
            return decline("a query whose row is not a record");
        };
        let mut values = Vec::with_capacity(fields.len());
        for label in fields.keys() {
            let Label::String(name) = label else {
                return decline("a query whose row has an ordinal label");
            };
            let Some((_, path)) =
                self.bindings.iter().find(|(bound, _)| bound == name)
            else {
                return decline("a query whose row names an unbound binder");
            };
            values.push(path.read(&elem)?);
        }
        let value = Expr::Tuple(row, values);
        node(Rel::Project(
            Row::placeholder(),
            Box::new(tree),
            Box::new(value),
        ))
    }

    /// Replaces the tree with a node built over it.
    fn wrap(&mut self, f: impl FnOnce(Box<Expr>) -> Rel) -> Option<()> {
        let Some(input) = self.tree.take() else {
            return decline("a step with nothing under it");
        };
        self.tree = Some(node(f(Box::new(input)))?);
        Some(())
    }

    /// Rewrites an expression over the query's binders into one over
    /// `$0`.
    ///
    /// A query nested inside the expression is a tree of its own, and
    /// its `$0` is its own element (`spec.md` §2 rule 3), so it cannot
    /// read this row that way. The expression is then wrapped in a
    /// `let` that gives the row a name, and the nested tree reads the
    /// binders through that name. The `let` appears only where there is
    /// a nested tree to want it: an expression that substitutes
    /// straight through is left as it was.
    fn rewrite(&self, e: &Expr) -> Option<Expr> {
        let rewritten = self.rewrite_expr(e)?;
        // A binder that was in scope and is still read is a binder the
        // substitution did not remove. It is not a decline: the tree we
        // built is wrong, and saying so is worth more than hiding it in
        // a count. `spec.md` §2 has no environment for it to name.
        let free = free_names_in(&rewritten);
        LEAKED.with(|cell| {
            cell.borrow_mut().extend(
                self.in_scope.iter().filter(|n| free.contains(*n)).cloned(),
            );
        });
        Some(rewritten)
    }

    /// Substitutes the binders out of an expression, wrapping it in a
    /// `let` where it holds a query that needs the row by name.
    fn rewrite_expr(&self, e: &Expr) -> Option<Expr> {
        let Some(elem) =
            self.tree.as_ref().and_then(|t| element_type(&t.type_()))
        else {
            return decline(
                "an expression over a tree that is not a collection",
            );
        };
        let mut map = self.outer.clone();
        for (name, path) in &self.bindings {
            map.insert(name.clone(), path.read(&elem)?);
        }
        if let Some(plain) = substitute(e, &map) {
            return Some(plain);
        }
        // That was an attempt, not a decision: an expression holding a
        // query declines here and succeeds below, so whatever it said
        // is about a path not taken.
        //
        // A nested tree binds its own row and position, so it reads
        // this node's through names that a `let` binds first: the row's,
        // and the position's -- which a nested query reads both where a
        // binder holds it and where it evaluates `ordinal` once, before
        // its first row. Each `let` is there only where the nested tree
        // reads its name, the row's outside the position's, as
        // morel-java writes them.
        forget_decline();
        let row_name = self.new_binder();
        let ordinal_name = self.new_binder();
        let binder = Expr::Identifier(elem.clone(), row_name.clone());
        let ordinal =
            Expr::Identifier(ordinal_ref().type_(), ordinal_name.clone());
        let outer = self.outer_through(&binder, Some(&ordinal))?;
        let counter = Rc::clone(&self.counter);
        let Some(body) = substitute_with(e, &map, &mut |t, steps| {
            translate_with(steps, t, outer.clone(), Rc::clone(&counter), true)
        }) else {
            return decline("an expression over the binders");
        };
        let body = rename_in_nested(&body, ORDINAL, &ordinal_name);
        let free = free_names_in(&body);
        let mut body = body;
        if free.contains(&ordinal_name) {
            body = let_binding(ordinal_name, ordinal_ref(), body);
        }
        if free.contains(&row_name) {
            body = let_binding(row_name, row_ref(&elem, 0), body);
        }
        Some(body)
    }
}

/// Returns `e` with `from` renamed `to` inside the trees nested in it,
/// and nowhere else.
fn rename_in_nested(e: &Expr, from: &str, to: &str) -> Expr {
    match e {
        Expr::Rel(_, _) => rename(e, from, to),
        _ => map_children(e, &|x| rename_in_nested(x, from, to)),
    }
}

/// Builds `let val name = value in body end`, which is how a row gets
/// the name a tree nested in one of its expressions reads it by.
fn let_binding(name: String, value: Expr, body: Expr) -> Expr {
    let value_type = value.type_();
    Expr::Let(
        body.type_(),
        vec![Decl::NonRecVal(Box::new(ValBind {
            pat: Pat::Identifier(value_type.clone(), name),
            t: (*value_type).clone(),
            expr: value,
            overload_pat: None,
            span: None,
        }))],
        Box::new(body),
    )
}

/// Returns how many components an expression's element has: a join's
/// inputs' components concatenated, and otherwise one.
fn components_of(exp: &Expr) -> usize {
    match exp {
        Expr::Rel(_, rel) => match rel.as_ref() {
            Rel::Join(_, _, _, left, right) => {
                components_of(left) + components_of(right)
            }
            _ => 1,
        },
        _ => 1,
    }
}

/// Builds `#slot e`, reading a field or a component. The printer writes
/// it by the name of the field, or by its 1-based position where the
/// element is a tuple.
fn selector(e: Expr, slot: usize, t: Rc<Type>) -> Expr {
    let selector_type = Rc::new(Type::Fn(e.type_(), t.clone()));
    Expr::Apply(
        t,
        Box::new(Expr::RecordSelector(selector_type, slot)),
        Box::new(e),
        Span::new(""),
    )
}

/// Returns the literal `true`, which a join with no condition carries
/// and the printer omits.
fn true_literal() -> Expr {
    Expr::Literal(
        Rc::new(Type::Primitive(PrimitiveType::Bool)),
        Val::Bool(true),
    )
}

/// Looks through a type alias, as the structural tests here must.
fn peel(t: &Rc<Type>) -> &Type {
    peel_type(t)
}

/// Returns where each of a step's binders sits in the element the step
/// produced.
///
/// The step's environment is what the compiler says is in scope after
/// the step, and the element is what the tree holds, so this is where
/// the two are matched up. Taking the names from the environment rather
/// than from the expression is the whole point: `yield f = d` binds `f`
/// and the expression is `d`, and a translation that reads the name off
/// the expression binds `d`, drops `f`, and leaves the next step
/// reading a name nothing defines.
///
/// An atom's single binder is the whole element. Otherwise the element
/// is a record and each binder is a field of it, which
/// [`Binding::matches_fields`] checks by type as well as by name --
/// `yield g = {g = ...}` binds `g` to the record and not to its sole
/// field.
fn bindings_over(
    env: &StepEnv,
    elem: &Rc<Type>,
) -> Option<Vec<(String, Path)>> {
    if let [only] = env.bindings.as_slice()
        && (env.atom || only.type_ == *elem)
    {
        return Some(vec![(only.id.name.clone(), Path::whole())]);
    }
    if Binding::matches_fields(&env.bindings, peel(elem)) {
        return Some(
            env.bindings
                .iter()
                .map(|b| (b.id.name.clone(), Path::field(&b.id.name)))
                .collect(),
        );
    }
    decline("a step whose element does not hold its binders")
}

/// Decomposes a record expression into its labelled parts, which is
/// how a `group`'s keys and aggregates are written.
///
/// A single key or aggregate is not written as a record at all --
/// `group i` rather than `group {i = i}` -- so the name comes from the
/// expression, the way the query's own `yield` takes it.
fn labelled_parts(e: &Expr) -> Option<Vec<(Label, Expr)>> {
    // `group ()` groups on nothing, which is one group, and is how
    // `compute` is written when it is written as a `group`. The `()`
    // reaches here as the unit value, not as a tuple of no fields.
    if matches!(e, Expr::Literal(_, Val::Unit))
        || matches!(e, Expr::Tuple(_, items) if items.is_empty())
    {
        return Some(vec![]);
    }
    let Expr::Tuple(t, items) = e else {
        let Some(name) = e.implicit_label() else {
            return decline("a group's part that has no name");
        };
        return Some(vec![(Label::String(name), e.clone())]);
    };
    let Type::Record(_, fields) = peel(t) else {
        return decline("a group's parts that are not a record");
    };
    if fields.len() != items.len() {
        return decline("a group's parts that are not a record");
    }
    Some(fields.keys().cloned().zip(items.iter().cloned()).collect())
}

/// Returns whether an aggregate function is declared over a bag, and
/// so needs a converter where the input is a list.
///
/// The collection aggregates -- `count`, `sum`, `max`, `min`, `empty`,
/// `nonEmpty`, `only` -- are declared over `'a bag` and adapt to a
/// list, so their instance here is typed by the input; morel-java's
/// are declared over a bag and converted, and its plan text shows the
/// converter. Any other function is what its type says.
fn takes_bag(f: &Expr) -> bool {
    if let Expr::Literal(_, Val::Fn(func)) = f {
        let name = func.plan_name();
        if matches!(
            name,
            "count" | "empty" | "max" | "min" | "nonEmpty" | "only" | "sum"
        ) {
            return true;
        }
    }
    match peel(&f.type_()) {
        Type::Fn(param, _) => matches!(peel(param), Type::Bag(_)),
        _ => false,
    }
}

/// Returns the leaf `[()]`, over which a query with no scan iterates.
fn unit_leaf() -> Expr {
    let unit = Rc::new(Type::Primitive(PrimitiveType::Unit));
    Expr::List(
        Rc::new(Type::List(unit.clone())),
        vec![Expr::Literal(unit, Val::Unit)],
    )
}

/// Returns `tree` with a filter over it, or `tree` itself where there
/// is nothing to filter on.
fn filtered(tree: Expr, test: Option<Expr>) -> Option<Expr> {
    match test {
        None => Some(tree),
        Some(test) => node(Rel::Filter(
            Row::placeholder(),
            Box::new(tree),
            Box::new(test),
        )),
    }
}

/// Returns the placeholder that reads the element of a node's input
/// `index` while the node is being built: `$0`, or a join's `$1`.
fn row_ref(elem: &Rc<Type>, index: usize) -> Expr {
    let name = if index == 0 { ROW } else { RIGHT_ROW };
    Expr::Identifier(elem.clone(), name.to_string())
}

/// Returns whether an expression is the element itself, `$0`.
fn is_row(e: &Expr) -> bool {
    matches!(e, Expr::Identifier(_, name) if name == ROW)
}

/// Returns the placeholder that reads the position of the row a node
/// is being built over, `$ordinal`; the node binds it.
fn ordinal_ref() -> Expr {
    Expr::Identifier(
        Rc::new(Type::Primitive(PrimitiveType::Int)),
        ORDINAL.to_string(),
    )
}

/// Returns whether an expression reads the position placeholder,
/// which only the node about to be built can bind.
fn reads_ordinal(e: &Expr) -> bool {
    free_names_in(e).contains(ORDINAL)
}

/// Builds the expression for a node, with the type it derives and
/// names of its own for the rows its expressions read.
fn node(rel: Rel) -> Option<Expr> {
    let rel = rel.bind();
    match rel.derive_type() {
        // A node whose type does not derive is one the datatype's own
        // rules reject, which is a finding rather than a gap.
        None => decline("a node whose type does not derive"),
        Some(t) => Some(Expr::Rel(t, Box::new(rel))),
    }
}

/// Returns where each name a scan's pattern binds sits in the element
/// it matches. A variable names the whole of it, and a tuple of
/// variables names its components -- which is how the names come back
/// in the projection that ends the tree, where the tree itself carries
/// none.
fn binder_paths(pat: &Pat) -> Option<Vec<(String, Path)>> {
    let mut paths = Vec::new();
    collect_paths(pat, &Path::whole(), &mut paths)?;
    Some(paths)
}

/// Adds where each name `pat` binds sits, given where `pat` itself
/// sits in the element.
fn collect_paths(
    pat: &Pat,
    at: &Path,
    paths: &mut Vec<(String, Path)>,
) -> Option<()> {
    match pat {
        Pat::Identifier(_, name) => paths.push((name.clone(), at.clone())),
        // A wildcard binds nothing, and nothing needs to read it. Nor
        // does a literal: it filters, and `pat_tests` says how.
        Pat::Literal(_, _) | Pat::Wildcard(_) => {}
        // `x as p` binds the name and whatever `p` binds.
        Pat::As(_, name, inner) => {
            paths.push((name.clone(), at.clone()));
            collect_paths(inner, at, paths)?;
        }
        Pat::Tuple(_, pats) => {
            for (i, p) in pats.iter().enumerate() {
                collect_paths(p, &at.then(Hop::Component(i + 1)), paths)?;
            }
        }
        Pat::Record(_, fields, _) => {
            for field in fields {
                let (label, p) = match field {
                    PatField::Labeled(label, p) => (label.clone(), p),
                    // `{y}` names the field by the pattern in it.
                    PatField::Anonymous(p) => match p.name() {
                        None => {
                            return decline(
                                "a record pattern field                                             with no name",
                            );
                        }
                        Some(name) => (name, p),
                    },
                };
                collect_paths(p, &at.then(Hop::Field(label)), paths)?;
            }
        }
        // A pattern that can fail becomes a filter and a projection,
        // which is more than this does.
        _ => return None,
    }
    Some(())
}

/// Adds the conditions under which `pat` matches the element it is
/// read out of, or declines where it is a pattern this cannot test.
///
/// A pattern that can fail filters as well as binds, and the two
/// halves separate: this is the filter, and [`collect_paths`] is the
/// binding. A scan is then a leaf with a filter over it, and where the
/// binders do not describe the element a projection over that --
/// ordinary nodes that a rule can see through, rather than one node
/// holding a `case` that yields a collection.
///
/// A user datatype's constructor is not tested here. It filters too,
/// but extracting what it binds needs a `case` of its own: a datatype
/// has no total accessor for a constructor's argument, and no value to
/// give the branch that does not match.
fn pat_tests(
    pat: &Pat,
    at: &Path,
    elem: &Rc<Type>,
    tests: &mut Vec<Expr>,
) -> Option<()> {
    match pat {
        Pat::Identifier(_, _) | Pat::Wildcard(_) => {}
        Pat::As(_, _, inner) => pat_tests(inner, at, elem, tests)?,
        Pat::Literal(t, value) => {
            // A type with one value has one pattern, and a test against
            // it cannot fail. `from i in [1, 2, 3], () in [()]` binds
            // nothing and filters nothing, and a `filter [$0 = ()]`
            // over the leaf says it does.
            if !matches!(peel(t), Type::Primitive(PrimitiveType::Unit)) {
                tests.push(equals(at.read(elem)?, value, t));
            }
        }
        Pat::Tuple(_, pats) => {
            for (i, p) in pats.iter().enumerate() {
                pat_tests(p, &at.then(Hop::Component(i + 1)), elem, tests)?;
            }
        }
        Pat::Record(_, fields, _) => {
            for field in fields {
                let (label, p) = match field {
                    PatField::Labeled(label, p) => (label.clone(), p),
                    PatField::Anonymous(p) => (p.name()?, p),
                };
                pat_tests(p, &at.then(Hop::Field(label)), elem, tests)?;
            }
        }
        _ => return None,
    }
    Some(())
}

/// Builds `e = value`, which is the test a literal pattern makes.
fn equals(e: Expr, value: &Val, t: &Rc<Type>) -> Expr {
    let eq = match peel(t) {
        Type::Primitive(PrimitiveType::Bool) => BuiltInFunction::BoolEq,
        Type::Primitive(PrimitiveType::Char) => BuiltInFunction::CharEq,
        Type::Primitive(PrimitiveType::Int) => BuiltInFunction::IntEq,
        Type::Primitive(PrimitiveType::Real) => BuiltInFunction::RealEq,
        Type::Primitive(PrimitiveType::String) => BuiltInFunction::StringEq,
        _ => BuiltInFunction::GEq,
    };
    let boolean = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let pair = Rc::new(Type::Tuple(vec![t.clone(), t.clone()]));
    Expr::Apply(
        boolean.clone(),
        Box::new(Expr::Literal(
            Rc::new(Type::Fn(pair.clone(), boolean)),
            Val::Fn(eq),
        )),
        Box::new(Expr::Tuple(
            pair,
            vec![e, Expr::Literal(t.clone(), value.clone())],
        )),
        Span::new(""),
    )
}

/// Joins conditions with `andalso`, or returns `None` where there are
/// none.
fn all_of(mut tests: Vec<Expr>) -> Option<Expr> {
    let mut all = tests.pop()?;
    let boolean = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let pair = Rc::new(Type::Tuple(vec![boolean.clone(), boolean.clone()]));
    while let Some(test) = tests.pop() {
        all = Expr::Apply(
            boolean.clone(),
            Box::new(Expr::Literal(
                Rc::new(Type::Fn(pair.clone(), boolean.clone())),
                Val::Fn(BuiltInFunction::BoolAndAlso),
            )),
            Box::new(Expr::Tuple(pair.clone(), vec![test, all])),
            Span::new(""),
        );
    }
    Some(all)
}

/// Returns whether `source` reads any of the query's binders, which
/// makes a scan dependent.
fn reads_a_binding(source: &Expr, bindings: &[(String, Path)]) -> bool {
    let free = free_names_in(source);
    bindings.iter().any(|(name, _)| free.contains(name))
}

/// Replaces every identifier named in `map` with the expression it maps
/// to, and declines where an expression is not one it knows how to
/// walk.
fn substitute(e: &Expr, map: &BTreeMap<String, Expr>) -> Option<Expr> {
    substitute_with(e, map, &mut |_, _| None)
}

/// Translates a query nested inside an expression into a tree of its
/// own, or declines.
type Nested<'a> = dyn FnMut(&Rc<Type>, &[Step]) -> Option<Expr> + 'a;

/// Substitutes as [`substitute`] does, and hands a nested query to
/// `nested`, which translates it into a tree of its own or declines.
fn substitute_with(
    e: &Expr,
    map: &BTreeMap<String, Expr>,
    nested: &mut Nested<'_>,
) -> Option<Expr> {
    Some(match e {
        Expr::Identifier(_, name) => match map.get(name) {
            Some(replacement) => replacement.clone(),
            None => e.clone(),
        },
        Expr::Literal(_, _)
        | Expr::RecordSelector(_, _)
        | Expr::Extent(_, _) => e.clone(),
        // `ordinal` is the position of the row the step reads, which
        // the node the step becomes binds beside the row.
        Expr::Ordinal(_) => ordinal_ref(),
        // `current` is the row itself, and none of `spec.md` §3's
        // eleven constructors carries it. There is nothing to build,
        // so this is not missing coverage.
        Expr::Current(_) => {
            return decline("a query that reads `current`");
        }
        Expr::Apply(t, f, a, span) => {
            let f = substitute_with(f, map, nested)?;
            let a = substitute_with(a, map, nested)?;
            Expr::Apply(t.clone(), Box::new(f), Box::new(a), span.clone())
        }
        Expr::Aggregate(t, a, b, span) => {
            let a1 = substitute_with(a, map, nested)?;
            let b1 = substitute_with(b, map, nested)?;
            Expr::Aggregate(t.clone(), Box::new(a1), Box::new(b1), span.clone())
        }
        Expr::Tuple(t, items) => Expr::Tuple(
            t.clone(),
            items
                .iter()
                .map(|i| substitute_with(i, map, nested))
                .collect::<Option<Vec<_>>>()?,
        ),
        Expr::List(t, items) => Expr::List(
            t.clone(),
            items
                .iter()
                .map(|i| substitute_with(i, map, nested))
                .collect::<Option<Vec<_>>>()?,
        ),
        Expr::Raise(t, a, span) => {
            let a = substitute_with(a, map, nested)?;
            Expr::Raise(t.clone(), Box::new(a), span.clone())
        }
        // A query in an expression is a tree of its own; `nested` is
        // what makes one, and declines where nothing is expecting it.
        Expr::From(t, steps) => nested(t, steps)?,
        // A `let` binds names of its own, and a name it binds is not
        // the binder it happens to share a spelling with, so the
        // substitution stops at it. Each declaration is in the scope
        // the ones before it made, which is why the map narrows as the
        // list is walked.
        Expr::Let(t, decls, body) => {
            let mut scope = map.clone();
            let mut bound = Vec::with_capacity(decls.len());
            for decl in decls {
                // A `fun` is in scope in its own body, and a type or a
                // datatype is not a value at all.
                let Decl::NonRecVal(b) = decl else {
                    return decline("a `let` that binds a function");
                };
                let mut bind = b.as_ref().clone();
                bind.expr = substitute_with(&b.expr, &scope, nested)?;
                bound.push(Decl::NonRecVal(Box::new(bind)));
                for name in bound_by(&b.pat) {
                    scope.remove(&name);
                }
            }
            let body = substitute_with(body, &scope, nested)?;
            Expr::Let(t.clone(), bound, Box::new(body))
        }
        // An arm's pattern binds for that arm alone, so each is
        // substituted in a scope of its own.
        Expr::Case(t, subject, arms, span) => {
            let subject = substitute_with(subject, map, nested)?;
            Expr::Case(
                t.clone(),
                Box::new(subject),
                substitute_arms(arms, map, nested)?,
                span.clone(),
            )
        }
        Expr::Fn(t, arms, span) => Expr::Fn(
            t.clone(),
            substitute_arms(arms, map, nested)?,
            span.clone(),
        ),
        _ => return decline("an expression that is not walked"),
    })
}

/// Substitutes in the arms of a `case` or a `fn`, each in the scope its
/// own pattern leaves.
fn substitute_arms(
    arms: &[Match],
    map: &BTreeMap<String, Expr>,
    nested: &mut Nested<'_>,
) -> Option<Vec<Match>> {
    arms.iter()
        .map(|arm| {
            let mut scope = map.clone();
            for name in bound_by(&arm.pat) {
                scope.remove(&name);
            }
            Some(Match {
                pat: arm.pat.clone(),
                expr: substitute_with(&arm.expr, &scope, nested)?,
            })
        })
        .collect()
}

/// Returns the names a pattern binds, which a substitution must not
/// reach past.
fn bound_by(pat: &Pat) -> Vec<String> {
    let mut names = Vec::new();
    pat.for_each_id_pat(&mut |(_, name)| names.push(name.to_string()));
    names
}

#[cfg(test)]
mod tests {
    use crate::shell::Kernel;

    /// Compiles `code` and returns the plan of the tree it translates
    /// to, or `None` where the translator declines.
    fn tree_of(code: &str) -> Option<String> {
        let mut kernel = Kernel::new(&[]);
        // A plan is longer than the default `stringDepth`, which would
        // truncate it.
        kernel
            .process_statement("Sys.set (\"stringDepth\", NONE)", None)
            .expect("sets stringDepth");
        let statement = format!("Sys.planOf ({})", code);
        let output = kernel
            .process_statement(&statement, None)
            .expect("compiles");
        // `Sys.planOf` returns the plan as a string, so the output is
        // `val it = "..." : string`.
        let start = output.find('"')? + 1;
        let end = output.rfind('"')?;
        let text = output[start..end].replace("\\n", "\n");
        // A step list has no newline in it, and a tree always does.
        text.contains('\n').then_some(text)
    }

    /// A filter over a leaf, which is the smallest tree there is. The
    /// binder `i` is gone, and the condition reads the element.
    #[test]
    fn a_filter_over_a_leaf() {
        assert_eq!(
            tree_of("from i in [1, 2, 3] where i > 1").unwrap(),
            "filter [$0 > 1] : int list\n  [1, 2, 3] : int list\n"
        );
    }

    /// A query with no scan iterates over one unit row, which is a
    /// visible leaf its author did not write.
    #[test]
    fn a_query_with_no_scan_has_a_unit_leaf() {
        assert_eq!(
            tree_of("from yield 1").unwrap(),
            "project [1] : int list\n  [()] : unit list\n"
        );
    }

    /// `order`, `skip` and `take` are nodes of their own, and a sort's
    /// output is a list whatever its input was.
    #[test]
    fn order_skip_and_take_are_nodes() {
        let text =
            tree_of("from i in [3, 1, 2] order i skip 1 take 1").unwrap();
        assert_eq!(
            text,
            "take [1] : int list\n  \
             skip [1] : int list\n    \
             sort [$0] : int list\n      \
             [3, 1, 2] : int list\n"
        );
    }

    /// A join concatenates its inputs' components, and the projection
    /// above it is where the names come back.
    #[test]
    fn a_join_concatenates_and_the_projection_names() {
        let text =
            tree_of("from i in [1, 2], j in [3, 4] where i < j yield {i, j}")
                .unwrap();
        assert!(
            text.starts_with(
                "project [{i = #1 $0, j = #2 $0}] : {i:int, j:int} list\n  \
                 filter [#1 $0 < #2 $0] : (int * int) list\n    join : \
                 (int * int) list\n"
            ),
            "{}",
            text
        );
    }

    /// A set operator carries whether it removes duplicates, and the
    /// plan says `all` where it does not.
    #[test]
    fn a_set_operator_says_whether_it_keeps_duplicates() {
        assert!(
            tree_of("from i in [1, 2] union [3]")
                .unwrap()
                .starts_with("union [all] : int list\n"),
        );
        assert!(
            tree_of("from i in [1, 2] union distinct [3]")
                .unwrap()
                .starts_with("union : int list\n"),
        );
    }

    /// It declines rather than guesses, and the plan falls back to the
    /// step list.
    #[test]
    fn it_declines_what_it_cannot_translate() {
        // A user datatype's constructor filters, but extracting what
        // it binds has no total expression: a datatype has no accessor
        // for a constructor's argument, and no value to give the row
        // that does not match.
        assert_eq!(tree_of("from SOME i in [SOME 1, NONE]"), None);
        // `exists` short-circuits a query into a boolean, and none of
        // `spec.md` §3's eleven constructors does that. There is
        // nothing to build, so this decline is permanent.
        assert_eq!(
            tree_of("from i in [1, 2] where exists (from j in [i])"),
            None
        );
    }

    /// A `group` whose single key is not written as a record takes its
    /// name off the expression, and the projection that follows builds
    /// the element it was given, so it has no argument.
    #[test]
    fn a_lone_group_key_takes_its_name_off_the_expression() {
        assert_eq!(
            tree_of("from i in [1, 2] group j = i").unwrap(),
            "project [#i $0] : int list\n  \
             group [i = $0] : {i:int} list\n    \
             [1, 2] : int list\n"
        );
    }

    /// A pattern that can fail filters as well as binds, and the two
    /// halves are separate nodes: a filter over the source, and the
    /// projection over that.
    #[test]
    fn a_pattern_that_can_fail_filters_and_binds() {
        assert_eq!(
            tree_of("from (x, 20) in [(1, 10), (2, 20)]").unwrap(),
            "project [#1 $0] : int list\n  \
             filter [#2 $0 = 20] : (int * int) list\n    \
             [(1, 10), (2, 20)] : (int * int) list\n"
        );
    }

    /// A scan whose pattern destructures binds one name per component,
    /// and the projection that ends the tree is where the names come
    /// back.
    #[test]
    fn a_scan_may_destructure() {
        assert_eq!(
            tree_of("from (i, j) in [(1, 2)]").unwrap(),
            "project [{i = #1 $0, j = #2 $0}] : {i:int, j:int} list\n  \
             [(1, 2)] : (int * int) list\n"
        );
    }

    /// A node that reads `ordinal` binds the position of its row in
    /// its input, as `$ordinal`: here the sorted rows, which is why the
    /// position is the filter's and not the scan's.
    #[test]
    fn a_node_that_reads_ordinal_binds_it() {
        assert_eq!(
            tree_of("from i in [3, 1, 2] order i where ordinal > 0").unwrap(),
            "filter [$ordinal > 0] : int list\n  \
             sort [$0] : int list\n    \
             [3, 1, 2] : int list\n"
        );
    }

    /// A query nested in a `yield` that counts with `ordinal` before
    /// its first row counts the enclosing rows, and reads their
    /// position through a `let`, as it reads the enclosing row.
    #[test]
    fn a_nested_query_reads_the_enclosing_ordinal_through_a_let() {
        assert_eq!(
            tree_of("from x in [10, 20] yield (from i in [1, 2] take ordinal)")
                .unwrap(),
            "project [let val v$0 = $ordinal in r$0[v$0] end] : \
             int list list\n  \
             [10, 20] : int list\n\
             \n\
             r$0[v$0] =\n  \
             take [v$0] : int list\n    \
             [1, 2] : int list\n"
        );
    }

    /// Every tree the translator builds passes the validator.
    #[test]
    fn what_it_builds_is_well_formed() {
        for code in [
            "from i in [1, 2, 3] where i > 1",
            "from i in [1, 2], j in [3, 4] where i < j yield {i, j}",
            "from i in [3, 1, 2] order i skip 1 take 1",
            "from i in [1, 2] union [3]",
            "from yield 1",
            "from i in [3, 1, 2] order i where ordinal > 0",
            "from x in [10, 20] yield (from i in [1, 2] take ordinal)",
        ] {
            let text = tree_of(code).unwrap_or_else(|| {
                panic!("declined: {}", code);
            });
            assert!(
                !text.contains("INVALID"),
                "{} gave an invalid tree: {}",
                code,
                text
            );
        }
    }
}
