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

//! Grounds a relational tree: each leaf that is an unbounded extent
//! is replaced by the collection that a generator bounds it to, and
//! the join tree around it is rebuilt so that what a generator reads
//! is scanned before it. It is morel-java's `RelExpander`.
//!
//! It is a second chance. The step-list grounder runs first, and
//! what it grounds never reaches here; a query that still holds an
//! extent is translated to a tree, grounded on the tree, and lowered
//! back to the steps that run it. Where any of the three declines,
//! the query is left as it was and the extent that survives is
//! reported as an unbounded variable.
//!
//! Grounding on the tree, rather than on the step list, is what lets
//! a scan whose pattern is not a single variable be grounded: a leaf
//! is named after the fact, by one variable or by one per component,
//! and the names are the engine's to reason about rather than the
//! query's to have written.

use crate::compile::core::{
    Expr, JoinKind, Pat, PatField, Rel, Step, StepKind, element_type,
};
use crate::compile::expander::{DatatypeMap, FnEnv, and_all, list_bounds};
use crate::compile::free_finder::free_names_in;
use crate::compile::generator::{Cache, Cardinality, Generator};
use crate::compile::generators::{
    finite_extent, maybe_generator_with_scope, split_conjuncts,
};
use crate::compile::library::BuiltInFunction;
use crate::compile::postfix::peel_type;
use crate::compile::rel_lowerer::{
    component_count, field_at, replace_inputs_with, substitute_name,
};
use crate::compile::span::Span;
use crate::compile::types::{Label, PrimitiveType, Type};
use crate::compile::{fbbt, rel_lowerer, rel_translator};
use crate::eval::val::Val;
use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ptr;
use std::rc::Rc;

/// Prints a line of the grounder's working, where the environment
/// asks for it.
fn debugf(line: impl FnOnce() -> String) {
    if env::var_os("MOREL_REL_DEBUG").is_some() {
        eprintln!("{}", line());
    }
}

thread_local! {
    /// The counter the binders this pass makes are named from. It is
    /// never reset: the compiler resolves a binder by name within a
    /// scope, so two queries of one statement must not share one.
    static NEXT_NAME: Cell<usize> = const { Cell::new(0) };
}

/// Grounds a query on its tree, or returns `None` where it has
/// nothing unbounded to ground, or where the translation, the
/// grounding or the lowering declines.
///
/// A query this pass hands back is grounded on its step list
/// instead, which is the older path and still the wider one.
pub(crate) fn ground(exp: &Expr, datatypes: &DatatypeMap) -> Option<Expr> {
    let Expr::From(t, steps) = exp else {
        return None;
    };
    if !steps.iter().any(step_holds_extent) {
        return None;
    }
    // The names to give the leaves: a tree carries none, and the
    // scans the query wrote are the leaves in the order a walk
    // reaches them. It matters beyond the plan text -- grounding
    // names what it builds after the leaf it bounds, and a group's
    // key record sorts its fields by label, so a generated name
    // puts the rows in a different order.
    let pats: Vec<Pat> = steps
        .iter()
        .filter_map(|step| match &step.kind {
            StepKind::Scan(pat, _, _) => Some(pat.as_ref().clone()),
            _ => None,
        })
        .collect();
    ground_query(t, steps, datatypes, &FnEnv::new(), pats)
}

/// Returns whether a step scans an extent, which is a variable that
/// nothing has bounded.
fn step_holds_extent(step: &Step) -> bool {
    matches!(&step.kind,
        StepKind::Scan(_, source, _) if holds_extent(source))
}

/// Grounds one query: its tree is grounded and lowered back to the
/// steps that run it.
fn ground_query(
    t: &Rc<Type>,
    steps: &[Step],
    datatypes: &DatatypeMap,
    fn_env: &FnEnv,
    pats: Vec<Pat>,
) -> Option<Expr> {
    let Some(tree) = rel_translator::translate(steps, t) else {
        debugf(|| "ground: no tree".to_string());
        return None;
    };
    debugf(|| format!("ground: tree {}", tree));
    let pats = if pats.is_empty() {
        leaf_pats(&tree)
    } else {
        pats
    };
    let mut x = Expander::new(datatypes, fn_env, pats);
    let Some(grounded) = x.expand(&tree, &[]) else {
        debugf(|| format!("ground: declined -- {}", x.reason));
        return None;
    };
    if holds_extent(&grounded) {
        debugf(|| "ground: an extent survived".to_string());
        return None;
    }
    let Some(lowered) = rel_lowerer::lower(&grounded) else {
        debugf(|| "ground: no lowering".to_string());
        return None;
    };
    debugf(|| format!("grounded: {}", lowered));
    Some(rel_lowerer::scalarize(lowered, t))
}

/// Returns whether an expression holds a scan over an extent, which
/// is a variable that nothing has bounded.
fn holds_extent(e: &Expr) -> bool {
    match e {
        Expr::Extent(_, _) => true,
        Expr::Exists(_, steps)
        | Expr::Forall(_, steps)
        | Expr::From(_, steps) => steps.iter().any(step_holds_extent),
        _ => {
            let mut found = false;
            for_each_child(e, &mut |c| found = found || holds_extent(c));
            found
        }
    }
}

/// The names a tree's leaves had, read back from the projection at
/// its root, or empty where the tree does not say.
///
/// A tree carries no names -- a leaf is a bare expression -- but a
/// query with several binders ends in a projection that names its
/// element's components after them. A join concatenates its inputs'
/// components, so component `k` is leaf `k`, and the projection is
/// the map from leaf to name.
///
/// It matters beyond the plan text: grounding names what it builds
/// after the leaf it bounds, a group's key record sorts its fields
/// by label, and a generated label sorts differently from the one
/// the user wrote -- which puts a query's rows in a different order.
fn leaf_pats(tree: &Expr) -> Vec<Pat> {
    let Expr::Rel(_, rel) = tree else {
        return Vec::new();
    };
    let Rel::Project(input, exp) = rel.as_ref() else {
        return Vec::new();
    };
    let Expr::Tuple(t, args) = exp.as_ref() else {
        return Vec::new();
    };
    let Type::Record(_, fields) = peel_type(t) else {
        return Vec::new();
    };
    if fields.len() != args.len() {
        return Vec::new();
    }
    // Which component each output field reads, and what it calls it.
    let mut names: BTreeMap<usize, String> = BTreeMap::new();
    for (arg, label) in args.iter().zip(fields.keys()) {
        let Expr::Apply(_, f, a, _) = arg else {
            return Vec::new();
        };
        let Expr::RecordSelector(_, slot) = f.as_ref() else {
            return Vec::new();
        };
        if !matches!(a.as_ref(), Expr::Input(_, 0)) {
            return Vec::new();
        }
        names.insert(*slot, label.to_string());
    }
    let mut leaves = Vec::new();
    if !collect_leaves(input, &mut leaves) || leaves.len() != names.len() {
        return Vec::new();
    }
    let mut pats = Vec::with_capacity(leaves.len());
    for (i, leaf) in leaves.iter().enumerate() {
        let (Some(name), Some(elem)) =
            (names.get(&i), element_type(&leaf.type_()))
        else {
            return Vec::new();
        };
        pats.push(Pat::Identifier(elem, name.clone()));
    }
    pats
}

/// Gathers a tree's leaves left to right, and reports false where it
/// meets a node that is not a filter or a join -- above one of those
/// the element is no longer the leaves' components, so the
/// projection does not name them.
fn collect_leaves(node: &Expr, leaves: &mut Vec<Expr>) -> bool {
    if let Expr::Rel(_, rel) = node {
        return match rel.as_ref() {
            Rel::Filter(input, _) => collect_leaves(input, leaves),
            Rel::Join(_, _, _, left, right) => {
                collect_leaves(left, leaves) && collect_leaves(right, leaves)
            }
            _ => false,
        };
    }
    leaves.push(node.clone());
    true
}

/// One leaf of a join tree: the collection it scans and the pattern
/// that grounding names it by.
#[derive(Clone)]
struct Leaf {
    exp: Expr,
    pat: Pat,
    extent: bool,
}

/// One step of grounding: an extent to register, named by its leaf,
/// or a constraint to apply.
#[derive(Clone)]
enum GroundStep {
    Extent(usize),
    Constraint(Expr),
}

/// What a join tree looks like from above: the leaves it is made of,
/// the conditions its own nodes impose, written in the leaves'
/// names, and the order a walk reaches them in.
struct Frame {
    leaves: Vec<Leaf>,
    constraints: Vec<Expr>,
    /// The conjunct a constraint came from, so that the filter can
    /// drop what a sealed generator has taken over.
    originals: BTreeMap<String, Expr>,
    order: Vec<GroundStep>,
}

impl Frame {
    fn new() -> Self {
        Frame {
            leaves: Vec::new(),
            constraints: Vec::new(),
            originals: BTreeMap::new(),
            order: Vec::new(),
        }
    }

    /// The expression that denotes the element of the leaves
    /// `lo..lo + n`, in terms of the names they bind.
    fn element(&self, lo: usize, n: usize) -> Expr {
        let args: Vec<Expr> =
            (lo..lo + n).map(|i| pat_exp(&self.leaves[i].pat)).collect();
        tuple_of(args)
    }
}

/// The generators the engine settled on, and which names are still
/// looking for one.
struct Settled {
    cache: Cache,
    /// The names an infinite extent was registered for. A name whose
    /// extent is finite has its generator already, and the engine
    /// does not look for a better one; the rest are asked again
    /// after every constraint.
    infinite: BTreeSet<String>,
}

impl Settled {
    fn best(&self, name: &str) -> Option<&Generator> {
        self.cache.best(name)
    }
}

struct Expander<'a> {
    datatypes: &'a DatatypeMap,
    fn_env: &'a FnEnv,
    /// The patterns to name the leaves with, in the order a walk
    /// reaches them, and how many have been used.
    leaf_pats: Vec<Pat>,
    next_leaf_pat: usize,
    /// Whether to name a leaf whose element is a tuple by one
    /// variable per component. The pattern the user wrote says
    /// which; a tree has erased it, so this tries one and then the
    /// other.
    destructure: bool,
    /// Whether removing a generator's duplicate values would change
    /// the query's answer.
    dedup_observable: bool,
    /// How many components a dropped leaf took off the front of the
    /// element, and how many are left.
    dropped: Option<(usize, usize)>,
    /// The names the query's own leaves bind.
    leaf_names: BTreeSet<String>,
    /// The conditions a sealed generator enforces, which the filter
    /// they came from can drop.
    subsumed: BTreeSet<String>,
    /// A leaf could not be grounded; the attempt is abandoned as
    /// soon as this is set.
    failed: bool,
    /// Why grounding declined, for the diagnostic.
    reason: String,
}

impl<'a> Expander<'a> {
    fn new(
        datatypes: &'a DatatypeMap,
        fn_env: &'a FnEnv,
        leaf_pats: Vec<Pat>,
    ) -> Self {
        Expander {
            datatypes,
            fn_env,
            leaf_pats,
            next_leaf_pat: 0,
            destructure: false,
            dedup_observable: true,
            dropped: None,
            leaf_names: BTreeSet::new(),
            subsumed: BTreeSet::new(),
            failed: false,
            reason: String::new(),
        }
    }

    /// Records why grounding is abandoning the attempt.
    fn fail<T>(&mut self, why: &str) -> Option<T> {
        if !self.failed {
            self.reason = why.to_string();
        }
        self.failed = true;
        None
    }

    /// Forgets what an abandoned attempt recorded.
    fn reset(&mut self, leaf_mark: usize) {
        self.subsumed.clear();
        self.dropped = None;
        self.next_leaf_pat = leaf_mark;
        self.failed = false;
    }

    /// Rewrites a node, carrying the conditions of the filters
    /// passed on the way down, and replacing each extent leaf with
    /// what grounds it.
    fn expand(&mut self, exp: &Expr, conditions: &[Expr]) -> Option<Expr> {
        if self.failed {
            return None;
        }
        let Expr::Rel(_, rel) = exp else {
            if matches!(exp, Expr::Extent(_, _)) {
                return self.bound(exp, conditions);
            }
            return Some(exp.clone());
        };
        match rel.as_ref() {
            // lint: sort until '#}' where '##Rel::'
            Rel::Except(d, args) => {
                let args = self.expand_each(args)?;
                node(Rel::Except(*d, args))
            }
            Rel::Filter(input, condition) => {
                self.expand_filter(input, condition, conditions)
            }
            Rel::Group(input, keys, aggs) => {
                // A group builds its element, so a condition above it
                // says nothing about the element below; but what is
                // below still has to be expanded, or an unbounded
                // leaf survives under it.
                let input = self.expand(input, &[])?;
                node(Rel::Group(Box::new(input), keys.clone(), aggs.clone()))
            }
            Rel::Intersect(d, args) => {
                let args = self.expand_each(args)?;
                node(Rel::Intersect(*d, args))
            }
            Rel::Join(_, _, _, _, _) => self.expand_join_tree(exp, conditions),
            Rel::Project(input, e) => self.expand_project(input, e, conditions),
            // A node that neither changes the element nor drops rows
            // by position passes the conditions down.
            Rel::Skip(input, count) => {
                let input = self.expand(input, conditions)?;
                node(Rel::Skip(Box::new(input), count.clone()))
            }
            Rel::Sort(input, key) => {
                let input = self.expand(input, conditions)?;
                node(Rel::Sort(Box::new(input), key.clone()))
            }
            Rel::Take(input, count) => {
                let input = self.expand(input, conditions)?;
                node(Rel::Take(Box::new(input), count.clone()))
            }
            Rel::Union(d, args) => {
                let args = self.expand_each(args)?;
                node(Rel::Union(*d, args))
            }
            Rel::Unorder(input) => {
                let input = self.expand(input, conditions)?;
                node(Rel::Unorder(Box::new(input)))
            }
        }
    }

    fn expand_each(&mut self, args: &[Expr]) -> Option<Vec<Expr>> {
        let mut out = Vec::with_capacity(args.len());
        for arg in args {
            out.push(self.expand(arg, &[])?);
        }
        Some(out)
    }

    /// Expands a filter: its conjuncts join the conditions carried
    /// down, and what a sealed generator came to enforce comes out
    /// of the filter.
    fn expand_filter(
        &mut self,
        input: &Expr,
        condition: &Expr,
        conditions: &[Expr],
    ) -> Option<Expr> {
        let conjuncts = split_conjuncts(condition);
        // This filter's conjuncts go before the ones already
        // carried, which are from filters above it and so were
        // written later. Order counts: where two constraints could
        // each generate a name, the engine keeps the first, so the
        // query's own order is the one to present them in.
        let mut all = conjuncts.clone();
        all.extend_from_slice(conditions);
        let input = self.expand(input, &all)?;
        // A conjunct that a sealed generator subsumes is now
        // enforced by the collection that replaced the leaf, so the
        // filter need not test it again; if that was all it tested,
        // the filter goes.
        let remaining = self.remaining(&conjuncts, true);
        if remaining.is_empty() {
            return Some(input);
        }
        Some(filter_of(input, and_all(remaining)))
    }

    /// The conjuncts of a filter that still have to be tested once
    /// the leaves below it are grounded: those no sealed generator
    /// subsumed, shifted to the grounded element's fields where
    /// asked.
    fn remaining(&self, conjuncts: &[Expr], shift: bool) -> Vec<Expr> {
        let mut out = Vec::new();
        for conjunct in conjuncts {
            if self.subsumed.contains(&key_of(conjunct)) {
                continue;
            }
            if is_true(conjunct) {
                continue;
            }
            out.push(if shift {
                self.shift_fields(conjunct)
            } else {
                conjunct.clone()
            });
        }
        out
    }

    /// Expands a projection. A projection changes what `$0` means,
    /// and substituting the projection into a condition says the
    /// same thing about the element below it.
    fn expand_project(
        &mut self,
        input: &Expr,
        exp: &Expr,
        conditions: &[Expr],
    ) -> Option<Expr> {
        let pushed: Vec<Expr> =
            conditions.iter().map(|c| subst(c, exp, None)).collect();
        let input = self.expand(input, &pushed)?;
        Some(project_of(input, exp.clone()))
    }

    /// Grounds every extent leaf of a join tree at once, naming the
    /// leaves as the query did and, where that fails, again with
    /// each tuple-typed leaf named by one variable per component.
    fn expand_join_tree(
        &mut self,
        join: &Expr,
        conditions: &[Expr],
    ) -> Option<Expr> {
        let leaf_mark = self.next_leaf_pat;
        if let Some(out) = self.expand_join_tree2(join, conditions, false)
            && !self.failed
        {
            return Some(out);
        }
        // The first attempt got far enough to record what it thought
        // a generator subsumed, or which leaf it dropped. None of
        // that survives the attempt.
        self.reset(leaf_mark);
        if let Some(out) = self.expand_join_tree2(join, conditions, true)
            && !self.failed
        {
            return Some(out);
        }
        self.failed = true;
        None
    }

    fn expand_join_tree2(
        &mut self,
        join: &Expr,
        conditions: &[Expr],
        destructure: bool,
    ) -> Option<Expr> {
        self.destructure = destructure;
        // Whatever a join further up dropped is not this join's
        // business.
        let outer_dropped = self.dropped.take();
        let mut frame = Frame::new();
        self.collect(join, 0, &mut frame);
        let outer_leaf_names = std::mem::take(&mut self.leaf_names);
        for leaf in &frame.leaves {
            for (name, _) in pat_names(&leaf.pat) {
                self.leaf_names.insert(name);
            }
        }
        let element = frame.element(0, frame.leaves.len());
        let mut constraints = frame.constraints.clone();
        for condition in conditions {
            let constraint = subst(condition, &element, None);
            frame
                .originals
                .insert(key_of(&constraint), condition.clone());
            constraints.push(constraint.clone());
            // Above the tree, so after everything in it -- a `where`
            // that follows every scan.
            frame.order.push(GroundStep::Constraint(constraint));
        }
        // A leaf that is a list of numbers bounds its name, and FBBT
        // can carry that to another name. The bound is for FBBT to
        // read and not for the engine to apply -- the leaf enforces
        // it -- so it is written into the constraints and never into
        // the order.
        for leaf in &frame.leaves {
            if let Pat::Identifier(_, _) = &leaf.pat {
                list_bounds(&leaf.pat, &leaf.exp, &mut constraints);
            }
        }
        let extents: Vec<usize> = (0..frame.leaves.len())
            .filter(|i| frame.leaves[*i].extent)
            .collect();
        if extents.is_empty() {
            let out = self.expand_join_inputs(join)?;
            self.leaf_names = outer_leaf_names;
            self.dropped = outer_dropped;
            return Some(out);
        }
        let mut ungrounded: BTreeSet<String> = BTreeSet::new();
        for i in &extents {
            for (name, _) in pat_names(&frame.leaves[*i].pat) {
                ungrounded.insert(name);
            }
        }
        self.correlated_pats(join, 0, &frame, &mut ungrounded);
        // Interleaved, in the order the walk reached them; the
        // conjuncts that strengthening added are not in that order,
        // having no place in the tree, so they go at the end.
        let written: BTreeSet<String> =
            constraints.iter().map(key_of).collect();
        let mut order = frame.order.clone();
        for constraint in self.strengthen(&constraints, &frame, &extents) {
            if !written.contains(&key_of(&constraint)) {
                order.push(GroundStep::Constraint(constraint));
            }
        }
        let settled = self.run_engine(&order, &frame, &ungrounded);
        for i in &extents {
            self.record_subsumed(
                &frame.leaves[*i].pat,
                &settled,
                &frame.originals,
            );
        }
        let out = self.rebuild(join, 0, &frame, &settled, &BTreeMap::new());
        if self.dropped.is_none() {
            self.dropped = outer_dropped;
        }
        self.leaf_names = outer_leaf_names;
        out
    }

    /// Expands the inputs of a join tree that has no extent leaf.
    fn expand_join_inputs(&mut self, join: &Expr) -> Option<Expr> {
        let Expr::Rel(_, rel) = join else {
            return self.expand(join, &[]);
        };
        let Rel::Join(kind, binder, condition, left, right) = rel.as_ref()
        else {
            return self.expand(join, &[]);
        };
        let left = self.expand(left, &[])?;
        let right = self.expand(right, &[])?;
        node(Rel::Join(
            *kind,
            binder.clone(),
            condition.clone(),
            Box::new(left),
            Box::new(right),
        ))
    }

    /// Grounds a leaf that stands alone rather than under a join,
    /// naming it as the query did and, where that fails, again with
    /// a tuple-typed leaf named by one variable per component.
    fn bound(&mut self, leaf: &Expr, conditions: &[Expr]) -> Option<Expr> {
        let leaf_mark = self.next_leaf_pat;
        if let Some(out) = self.bound2(leaf, conditions, false)
            && !self.failed
        {
            return Some(out);
        }
        self.reset(leaf_mark);
        if let Some(out) = self.bound2(leaf, conditions, true)
            && !self.failed
        {
            return Some(out);
        }
        self.failed = true;
        None
    }

    fn bound2(
        &mut self,
        leaf: &Expr,
        conditions: &[Expr],
        destructure: bool,
    ) -> Option<Expr> {
        self.destructure = destructure;
        let mut frame = Frame::new();
        self.add_leaf(leaf, &mut frame);
        let pat = frame.leaves[0].pat.clone();
        let element = pat_exp(&pat);
        let mut constraints = Vec::with_capacity(conditions.len());
        for condition in conditions {
            let constraint = subst(condition, &element, None);
            frame
                .originals
                .insert(key_of(&constraint), condition.clone());
            constraints.push(constraint);
        }
        self.leaf_names = pat_names(&pat).into_iter().map(|(n, _)| n).collect();
        let ungrounded = self.leaf_names.clone();
        // The bounds that strengthening deduced go first, so that a
        // deduced constant bound wins over a same-side bound that
        // reads a name still looking for a generator.
        let mut order = vec![GroundStep::Extent(0)];
        for c in self
            .strengthen(&constraints, &frame, &[0])
            .into_iter()
            .chain(constraints.iter().cloned())
        {
            order.push(GroundStep::Constraint(c));
        }
        let settled = self.run_engine(&order, &frame, &ungrounded);
        self.record_subsumed(&pat, &settled, &frame.originals);
        // A leaf whose type is finite needs no generator; it is a
        // finite collection like any other.
        let elem = element_type(&leaf.type_())?;
        if let Some(collection) = finite_extent(&elem, self.datatypes) {
            return Some(collection);
        }
        self.bounded(&pat, &settled, &BTreeMap::new())
    }

    /// Names the leaves of a join tree and gathers the conditions
    /// its nodes impose, in the order a walk reaches them.
    fn collect(&mut self, node: &Expr, lo: usize, frame: &mut Frame) {
        match node {
            Expr::Rel(_, rel) => match rel.as_ref() {
                // A filter between two joins constrains the leaves
                // below it just as a `where` between two scans
                // constrains the patterns before it.
                Rel::Filter(input, condition) => {
                    self.collect(input, lo, frame);
                    let n = frame.leaves.len() - lo;
                    let element = frame.element(lo, n);
                    for conjunct in split_conjuncts(condition) {
                        let constraint = subst(&conjunct, &element, None);
                        frame.originals.insert(key_of(&constraint), conjunct);
                        frame.constraints.push(constraint.clone());
                        frame.order.push(GroundStep::Constraint(constraint));
                    }
                }
                Rel::Join(_, _, condition, left, right) => {
                    self.collect(left, lo, frame);
                    let mid = frame.leaves.len();
                    self.collect(right, mid, frame);
                    let hi = frame.leaves.len();
                    if !is_true(condition) {
                        let constraint = subst(
                            condition,
                            &frame.element(lo, mid - lo),
                            Some(&frame.element(mid, hi - mid)),
                        );
                        frame.constraints.push(constraint.clone());
                        frame.order.push(GroundStep::Constraint(constraint));
                    }
                }
                _ => self.add_leaf(node, frame),
            },
            _ => self.add_leaf(node, frame),
        }
    }

    fn add_leaf(&mut self, leaf: &Expr, frame: &mut Frame) {
        let pat = self.element_pat(leaf);
        let extent = matches!(leaf, Expr::Extent(_, _));
        frame.leaves.push(Leaf {
            exp: leaf.clone(),
            pat,
            extent,
        });
        if extent {
            frame.order.push(GroundStep::Extent(frame.leaves.len() - 1));
        }
    }

    /// Creates the pattern that the engine keys on for a leaf's
    /// element: the one the query wrote, where the tree handed it
    /// over, and otherwise a fresh one.
    fn element_pat(&mut self, leaf: &Expr) -> Pat {
        let elem =
            element_type(&leaf.type_()).unwrap_or_else(|| leaf.type_().clone());
        if !self.destructure && self.next_leaf_pat < self.leaf_pats.len() {
            let pat = self.leaf_pats[self.next_leaf_pat].clone();
            self.next_leaf_pat += 1;
            if pat.type_() == elem {
                return pat;
            }
            // The walk and the scans disagree about which leaf is
            // which, so the rest of the names are not to be trusted
            // either.
            self.leaf_pats.clear();
        }
        self.pat(&elem)
    }

    /// Creates a pattern for a type: a tuple of variables where a
    /// tuple-typed leaf is to be destructured, otherwise one
    /// variable.
    fn pat(&mut self, t: &Rc<Type>) -> Pat {
        if self.destructure
            && let Type::Tuple(args) = peel_type(t)
        {
            let pats: Vec<Pat> = args.iter().map(|a| self.pat(a)).collect();
            return Pat::Tuple(t.clone(), pats);
        }
        ground_pat(t)
    }

    /// Registers the extents and applies the constraints in order,
    /// as the step-list grounder does: after every constraint, each
    /// extent name is asked again, and the last generator found for
    /// a name is the one it keeps.
    fn run_engine(
        &mut self,
        order: &[GroundStep],
        frame: &Frame,
        ungrounded: &BTreeSet<String>,
    ) -> Settled {
        let mut settled = Settled {
            cache: Cache::new(),
            infinite: BTreeSet::new(),
        };
        let mut registered: Vec<(String, Rc<Type>, Pat, bool)> = Vec::new();
        let mut constraints: Vec<Expr> = Vec::new();
        let outer: BTreeSet<String> = BTreeSet::new();
        for step in order {
            match step {
                GroundStep::Extent(i) => {
                    let leaf = &frame.leaves[*i];
                    debugf(|| format!("  extent: {:?}", leaf.pat));
                    // An unbounded scan yields the distinct values
                    // of the variables its pattern binds, in their
                    // natural order, so the collection it stands for
                    // is a list.
                    let ordered =
                        matches!(leaf.exp.type_().as_ref(), Type::List(_));
                    self.register_extent(
                        &mut settled,
                        &leaf.pat,
                        ordered,
                        &mut registered,
                    );
                }
                GroundStep::Constraint(c) => {
                    debugf(|| format!("  constraint: {}", c));
                    constraints.push(c.clone());
                    // Every extent name is asked again after every
                    // constraint, and the generator found last is
                    // the one kept: a later constraint can improve
                    // on an earlier one, as a constant bound that
                    // strengthening derived improves on a bound that
                    // reads a name still looking for a generator.
                    for (name, t, pat, ordered) in &registered {
                        if !settled.infinite.contains(name) {
                            continue;
                        }
                        maybe_generator_with_scope(
                            &mut settled.cache,
                            pat,
                            name,
                            t,
                            *ordered,
                            &constraints,
                            self.fn_env,
                            self.datatypes,
                            &outer,
                            &settled.infinite,
                            ungrounded,
                        );
                    }
                }
            }
        }
        settled
    }

    /// Gives each name an extent scans a generator of its own where
    /// its type is finite. A tuple pattern over an unbounded extent
    /// also gets one per component, so that a component whose type
    /// is finite -- a `bool` beside an `int` -- is grounded by its
    /// own extent while the other waits for a constraint.
    fn register_extent(
        &self,
        settled: &mut Settled,
        pat: &Pat,
        ordered: bool,
        registered: &mut Vec<(String, Rc<Type>, Pat, bool)>,
    ) {
        match pat {
            Pat::Tuple(_, args) => {
                for arg in args {
                    self.register_extent(settled, arg, ordered, registered);
                }
            }
            _ => {
                for (name, t) in pat_names(pat) {
                    registered.push((
                        name.clone(),
                        t.clone(),
                        pat.clone(),
                        ordered,
                    ));
                    match finite_extent(&t, self.datatypes) {
                        Some(collection) => settled.cache.add(
                            name,
                            Generator::new(
                                pat.clone(),
                                collection,
                                Cardinality::Finite,
                                BTreeSet::new(),
                                true,
                                true,
                                Vec::new(),
                            ),
                        ),
                        None => {
                            settled.infinite.insert(name);
                        }
                    }
                }
            }
        }
    }

    /// Deduces tighter bounds for the leaves, which grounding needs
    /// done first: a pair of comparisons only becomes a range once
    /// FBBT has turned them into one.
    fn strengthen(
        &self,
        constraints: &[Expr],
        frame: &Frame,
        extents: &[usize],
    ) -> Vec<Expr> {
        if constraints.is_empty() {
            return Vec::new();
        }
        let mut unbounded: Vec<(String, Rc<Type>)> = Vec::new();
        for i in extents {
            unbounded.extend(pat_names(&frame.leaves[*i].pat));
        }
        fbbt::strengthen(&unbounded, constraints)
    }

    /// Adds to `pats` the names of every leaf that reads one of
    /// them, and so cannot run until that name has a generator.
    fn correlated_pats(
        &self,
        node: &Expr,
        lo: usize,
        frame: &Frame,
        pats: &mut BTreeSet<String>,
    ) {
        match node {
            Expr::Rel(_, rel) => match rel.as_ref() {
                Rel::Filter(input, _) => {
                    self.correlated_pats(input, lo, frame, pats)
                }
                Rel::Join(_, _, _, left, right) => {
                    self.correlated_pats(left, lo, frame, pats);
                    let mid = lo + leaf_count(left);
                    self.correlated_pats(right, mid, frame, pats);
                }
                _ => self.correlated_leaf(lo, frame, pats),
            },
            _ => self.correlated_leaf(lo, frame, pats),
        }
    }

    fn correlated_leaf(
        &self,
        lo: usize,
        frame: &Frame,
        pats: &mut BTreeSet<String>,
    ) {
        let leaf = &frame.leaves[lo];
        if leaf.extent {
            return;
        }
        if free_names_in(&leaf.exp).iter().any(|n| pats.contains(n)) {
            for (name, _) in pat_names(&leaf.pat) {
                pats.insert(name);
            }
        }
    }

    /// Remembers the conditions that a sealed generator enforces, so
    /// that the filter they came from can drop them.
    fn record_subsumed(
        &mut self,
        pat: &Pat,
        settled: &Settled,
        originals: &BTreeMap<String, Expr>,
    ) {
        for (name, _) in pat_names(pat) {
            let Some(g) = settled.best(&name) else {
                continue;
            };
            if !g.sealed {
                continue;
            }
            for constraint in &g.provenance {
                if let Some(original) = originals.get(&key_of(constraint)) {
                    self.subsumed.insert(key_of(original));
                }
            }
        }
    }

    /// Rebuilds a join tree with each extent leaf replaced by the
    /// collection that bounds it. A leaf whose generator reads
    /// another leaf's element makes the join dependent, its binder
    /// naming what the right side reads.
    fn rebuild(
        &mut self,
        node: &Expr,
        lo: usize,
        frame: &Frame,
        settled: &Settled,
        bound: &BTreeMap<String, Expr>,
    ) -> Option<Expr> {
        if self.failed {
            return None;
        }
        let Expr::Rel(_, rel) = node else {
            return self.rebuild_leaf(lo, frame, settled, bound);
        };
        match rel.as_ref() {
            Rel::Filter(input, condition) => {
                let input = self.rebuild(input, lo, frame, settled, bound)?;
                let remaining =
                    self.remaining(&split_conjuncts(condition), false);
                if remaining.is_empty() {
                    return Some(input);
                }
                Some(filter_of(input, and_all(remaining)))
            }
            Rel::Join(kind, binder, condition, left, right) => self
                .rebuild_join(
                    *kind, binder, condition, left, right, lo, frame, settled,
                    bound,
                ),
            _ => self.rebuild_leaf(lo, frame, settled, bound),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn rebuild_join(
        &mut self,
        kind: JoinKind,
        binder: &Option<String>,
        condition: &Expr,
        left: &Expr,
        right: &Expr,
        lo: usize,
        frame: &Frame,
        settled: &Settled,
        bound: &BTreeMap<String, Expr>,
    ) -> Option<Expr> {
        let mid = lo + leaf_count(left);
        let hi = mid + leaf_count(right);
        if bound.is_empty()
            && let Some(common) =
                self.common_generator(lo, hi, frame, settled, bound)
        {
            return self.scan_common(lo, hi, frame, &common, bound);
        }
        let right_generator =
            if leaf_count(right) == 1 && frame.leaves[mid].extent {
                self.generator(&frame.leaves[mid].pat, settled).cloned()
            } else {
                None
            };
        if let Some(g) = &right_generator
            && !self.free(g, bound).is_empty()
        {
            return self.rebuild_dependent(
                kind, condition, left, lo, mid, frame, settled, bound, g,
            );
        }
        let bounded_leaf = leaf_count(right) == 1 && !frame.leaves[mid].extent;
        if (right_generator.is_some() || (bounded_leaf && binder.is_none()))
            && is_true(condition)
            && self.reads(
                lo,
                mid,
                frame,
                settled,
                bound,
                &frame.leaves[mid].pat,
            )
        {
            // A right side that already reads the left through the
            // join's binder cannot come first; the sides would each
            // read the other.
            return self.rebuild_swapped(
                kind,
                condition,
                left,
                lo,
                mid,
                frame,
                settled,
                bound,
                right_generator.as_ref(),
            );
        }
        let left = self.rebuild(left, lo, frame, settled, bound)?;
        let right = self.rebuild(right, mid, frame, settled, bound)?;
        node(Rel::Join(
            kind,
            binder.clone(),
            Box::new(condition.clone()),
            Box::new(left),
            Box::new(right),
        ))
    }

    /// Rebuilds a node under a join that is not a join: an extent
    /// leaf becomes what bounds it, and anything else is expanded on
    /// its own.
    fn rebuild_leaf(
        &mut self,
        lo: usize,
        frame: &Frame,
        settled: &Settled,
        bound: &BTreeMap<String, Expr>,
    ) -> Option<Expr> {
        let leaf = &frame.leaves[lo];
        if leaf.extent {
            return self.bounded(&leaf.pat.clone(), settled, bound);
        }
        if matches!(&leaf.exp, Expr::Rel(_, _)) {
            let exp = leaf.exp.clone();
            return self.expand(&exp, &[]);
        }
        Some(leaf.exp.clone())
    }

    /// Rebuilds a join whose right side is correlated: it reads
    /// names that the left side binds. The join becomes dependent,
    /// its binder naming the left element, and each name the
    /// generator reads becomes the path that reads it out of that
    /// element.
    #[allow(clippy::too_many_arguments)]
    fn rebuild_dependent(
        &mut self,
        kind: JoinKind,
        condition: &Expr,
        left: &Expr,
        lo: usize,
        mid: usize,
        frame: &Frame,
        settled: &Settled,
        bound: &BTreeMap<String, Expr>,
        g: &Generator,
    ) -> Option<Expr> {
        if !is_true(condition) {
            return self.fail("a dependent join would need a condition");
        }
        let left_element = frame.element(lo, mid - lo);
        let param_type = element_type(&left.type_())?;
        let param = fresh_name();
        let param_exp = Expr::Identifier(param_type, param.clone());
        let mut paths: BTreeMap<String, Expr> = BTreeMap::new();
        for name in self.free(g, bound) {
            // What the generator reads must be bound on the left; a
            // leaf further away would need the join reordered.
            let path = path_to(&left_element, &param_exp, &name)?;
            paths.insert(name, path);
        }
        for (name, value) in bound {
            paths.insert(name.clone(), value.clone());
        }
        let collection = substitute(&g.exp, &paths);
        let left = self.rebuild(left, lo, frame, settled, bound)?;
        node(Rel::Join(
            kind,
            Some(param),
            Box::new(condition.clone()),
            Box::new(left),
            Box::new(collection),
        ))
    }

    /// Rebuilds a join the other way round: the right side grounds
    /// on its own and the left side reads it, so the right comes
    /// first.
    #[allow(clippy::too_many_arguments)]
    fn rebuild_swapped(
        &mut self,
        kind: JoinKind,
        condition: &Expr,
        left: &Expr,
        lo: usize,
        mid: usize,
        frame: &Frame,
        settled: &Settled,
        bound: &BTreeMap<String, Expr>,
        right_generator: Option<&Generator>,
    ) -> Option<Expr> {
        let right_pat = frame.leaves[mid].pat.clone();
        let right_exp = frame.leaves[mid].exp.clone();
        let param_type = element_type(&right_exp.type_())?;
        let param = fresh_name();
        let param_exp = Expr::Identifier(param_type, param.clone());
        let mut bound2 = bound.clone();
        for (name, _) in pat_names(&right_pat) {
            let p = path(&right_pat, &param_exp, &name)?;
            bound2.insert(name, p);
        }
        let left = self.rebuild(left, lo, frame, settled, &bound2)?;
        let bounded_right = match right_generator {
            Some(_) => self.bounded(&right_pat, settled, bound)?,
            None => right_exp,
        };
        // The sides swap, so the components move with them.
        let m = component_count(&bounded_right);
        let k = component_count(&left);
        let swapped = node(Rel::Join(
            kind,
            Some(param),
            Box::new(condition.clone()),
            Box::new(bounded_right),
            Box::new(left),
        ))?;
        // Swapping the inputs moves the components, and with no
        // yield to absorb the swap a projection puts them back where
        // the tree above expects them.
        Some(permute(swapped, m, k))
    }

    /// Returns the generator that binds the names of every leaf
    /// between `lo` and `hi`, if one does.
    fn common_generator(
        &self,
        lo: usize,
        hi: usize,
        frame: &Frame,
        settled: &Settled,
        bound: &BTreeMap<String, Expr>,
    ) -> Option<Generator> {
        let mut common: Option<&Generator> = None;
        for leaf in &frame.leaves[lo..hi] {
            if !leaf.extent {
                return None;
            }
            for (name, _) in pat_names(&leaf.pat) {
                let g = settled.best(&name)?;
                if !self.free(g, bound).is_empty() {
                    return None;
                }
                match common {
                    None => common = Some(g),
                    Some(c) if ptr::eq(c, g) => {}
                    Some(_) => return None,
                }
            }
        }
        let common = common?;
        if matches!(common.pat, Pat::Identifier(_, _)) {
            // A generator that binds one name grounds one leaf,
            // which the ordinary path handles.
            return None;
        }
        Some(common.clone())
    }

    /// Grounds a join tree that one generator binds every leaf of:
    /// the leaves and the join between them become one scan of that
    /// generator, read through the paths its pattern gives each
    /// name.
    fn scan_common(
        &mut self,
        lo: usize,
        hi: usize,
        frame: &Frame,
        common: &Generator,
        bound: &BTreeMap<String, Expr>,
    ) -> Option<Expr> {
        let collection = substitute(&common.exp, bound);
        let element = frame.element(lo, hi - lo);
        if self.dedup_observable && !common.unique {
            // A generator may repeat a value where an unbounded scan
            // yields each assignment once, so it is scanned under
            // its own pattern, deduplicated, and ordered by the
            // record of its variables. That order is the query's
            // answer, not a detail.
            let vars = pat_names(&common.pat);
            let scanned = self.scanned(collection, common)?;
            let deduped = dedup_row(scanned, &common.pat, &vars)?;
            let row = input_of(&deduped)?;
            let renamed = rename(&element, &row, &record_or_atom_pat(&vars))?;
            return Some(project_of(deduped, renamed));
        }
        let row = input_of(&collection)?;
        if !destructurable(&common.pat) || common.extra_filter.is_some() {
            // The pattern can fail, and a projection reads every row
            // where the pattern matches only some. Scanning it
            // filters, and the element is already written in terms
            // of the names it binds.
            let scanned = self.scanned(collection, common)?;
            let row = input_of(&scanned)?;
            let renamed = rename(&element, &row, &common.pat)?;
            return Some(project_of(scanned, renamed));
        }
        let renamed = rename(&element, &row, &common.pat)?;
        Some(project_of(collection, renamed))
    }

    /// Returns whether any extent leaf between `lo` and `hi` has a
    /// generator that reads a name the given pattern binds.
    fn reads(
        &self,
        lo: usize,
        hi: usize,
        frame: &Frame,
        settled: &Settled,
        bound: &BTreeMap<String, Expr>,
        pat: &Pat,
    ) -> bool {
        let names: BTreeSet<String> =
            pat_names(pat).into_iter().map(|(n, _)| n).collect();
        for leaf in &frame.leaves[lo..hi] {
            if !leaf.extent {
                continue;
            }
            for (name, _) in pat_names(&leaf.pat) {
                let Some(g) = settled.best(&name) else {
                    continue;
                };
                if self.free(g, bound).iter().any(|f| names.contains(f)) {
                    return true;
                }
            }
        }
        false
    }

    /// Returns the generator of a leaf named by a single variable.
    fn generator<'s>(
        &self,
        pat: &Pat,
        settled: &'s Settled,
    ) -> Option<&'s Generator> {
        match pat {
            Pat::Identifier(_, name) => settled.best(name),
            _ => None,
        }
    }

    /// Returns the collection that bounds a leaf. A leaf named by a
    /// tuple of variables has a generator per component, each
    /// bounded by a different constraint, so what bounds the leaf is
    /// their product.
    fn bounded(
        &mut self,
        pat: &Pat,
        settled: &Settled,
        bound: &BTreeMap<String, Expr>,
    ) -> Option<Expr> {
        let mut product: Option<Expr> = None;
        for (name, t) in pat_names(pat) {
            let Some(g) = settled.best(&name).cloned() else {
                return self.fail(&format!("no generator for {}", name));
            };
            if !self.free(&g, bound).is_empty() {
                // What bounds this name reads something that is not
                // bound yet.
                return self.fail(&format!(
                    "the generator for {} reads a name that nothing has bound",
                    name
                ));
            }
            let component = self.project(&g, &name, bound)?;
            // A generator whose collection does not have the name's
            // own element type says something this pass cannot use:
            // a record pattern whose generator yields a tuple, for
            // one. The step-list grounder knows what to do with it.
            if !same_element(&component, &t) {
                return self.fail(&format!(
                    "the generator for {} does not have its type",
                    name
                ));
            }
            product = Some(match product {
                None => component,
                Some(p) => node(Rel::Join(
                    JoinKind::Inner,
                    None,
                    Box::new(true_literal()),
                    Box::new(p),
                    Box::new(component),
                ))?,
            });
        }
        let product = product?;
        // A join's element is one component per name, in the order
        // the names were joined; the leaf's is whatever shape its
        // pattern has. A pattern that nests -- `(b, (c, i))` -- puts
        // the components back the way the tree above reads them.
        let names = pat_names(pat);
        if names.len() < 2 {
            return self.typed(product, &pat.type_());
        }
        let row = input_of(&product)?;
        let mut binds: BTreeMap<String, Expr> = BTreeMap::new();
        for (i, (name, _)) in names.iter().enumerate() {
            binds.insert(name.clone(), field_at(&row, i));
        }
        let element = substitute(&pat_exp(pat), &binds);
        let flat =
            tuple_of((0..names.len()).map(|i| field_at(&row, i)).collect());
        if key_of(&element) == key_of(&flat) {
            return self.typed(product, &pat.type_());
        }
        let out = project_of(product, element);
        self.typed(out, &pat.type_())
    }

    /// Gives a collection the leaf's element type, or declines
    /// where what grounds the leaf is not of that type at all.
    ///
    /// A generator deduced from a constraint has the type the
    /// constraint spoke of, which may abbreviate the leaf's -- a
    /// range over `nat` is a range over the `int` that `nat` names.
    /// The leaf's own type is the one the query declared, so it is
    /// the one the values keep.
    fn typed(&mut self, collection: Expr, t: &Rc<Type>) -> Option<Expr> {
        if !same_element(&collection, t) {
            return self
                .fail("what grounds a leaf does not have the leaf's type");
        }
        match element_type(&collection.type_()) {
            Some(elem) if elem == *t => Some(collection),
            _ => Some(retype(collection, t)),
        }
    }

    /// Projects a generator's collection down to one leaf's element.
    fn project(
        &mut self,
        g: &Generator,
        name: &str,
        bound: &BTreeMap<String, Expr>,
    ) -> Option<Expr> {
        let exp = substitute(&g.exp, bound);
        if let Pat::Identifier(_, _) = &g.pat {
            return Some(self.dedup(g, name, exp));
        }
        let row = input_of(&exp)?;
        let element = path(&g.pat, &row, name)?;
        // What else the generator's pattern binds, and where each
        // stands. A name the query already bound has to be tested,
        // or the rows that disagree with it come through. A name
        // that nothing bound is the generator's own and is projected
        // away -- which can leave the same value twice, so it is
        // deduplicated.
        let mut tested: Vec<Expr> = Vec::new();
        let mut projects_away = false;
        for (other, t) in pat_names(&g.pat) {
            if other == name {
                continue;
            }
            let at = path(&g.pat, &row, &other)?;
            if let Some(value) = bound.get(&other) {
                tested.push(eq_exp(at, value.clone(), &t));
            } else if self.leaf_names.contains(&other) {
                // Another leaf of this query binds it. Reading it
                // here would need a dependent join, so the name is
                // projected away and the generator produces more
                // rows than the constraint allows -- which is no
                // matter while the filter above still tests it, and
                // every matter once a sealed generator has taken it
                // off.
                projects_away = true;
                self.subsumed.clear();
            } else if reads_free(g, &other) {
                // A name the constraint read that no leaf of this
                // query binds is bound in an enclosing scope, and a
                // row that disagrees with it is not a match.
                tested.push(eq_exp(
                    at,
                    Expr::Identifier(t.clone(), other.clone()),
                    &t,
                ));
            } else {
                projects_away = true;
            }
        }
        if tested.is_empty()
            && !projects_away
            && destructurable(&g.pat)
            && g.extra_filter.is_none()
        {
            // Nothing to test and nothing to drop, and the pattern
            // cannot fail, so reading the name out of each row says
            // it all.
            return Some(project_of(exp, element));
        }
        // Otherwise scan the pattern, which also filters where it
        // can fail, and read the name out.
        let mut scanned = self.scanned(exp, g)?;
        if !tested.is_empty() {
            scanned = filter_of(scanned, and_all(tested));
        }
        let out = project_of(scanned, element);
        if self.dedup_observable && (projects_away || !g.unique) {
            return dedup_named(out, name);
        }
        Some(out)
    }

    /// Deduplicates a generator's collection where its duplicates
    /// would be observable.
    fn dedup(&self, g: &Generator, name: &str, collection: Expr) -> Expr {
        if g.unique || !self.dedup_observable {
            return collection;
        }
        dedup_named(collection.clone(), name).unwrap_or(collection)
    }

    /// A generator's collection scanned under its pattern: the rows
    /// the pattern matches, where it may fail, that also satisfy the
    /// conditions the generator's scan must apply at once.
    fn scanned(&mut self, collection: Expr, g: &Generator) -> Option<Expr> {
        let row = input_of(&collection)?;
        let mut tests: Vec<Expr> = Vec::new();
        pat_test(&g.pat, &row, &mut tests)?;
        if let Some(extra) = &g.extra_filter {
            tests.push(rename(extra, &row, &g.pat)?);
        }
        if tests.is_empty() {
            return Some(collection);
        }
        Some(filter_of(collection, and_all(tests)))
    }

    /// The names a generator reads that something else must bind:
    /// the names of this query's leaves, less those already bound.
    fn free(
        &self,
        g: &Generator,
        bound: &BTreeMap<String, Expr>,
    ) -> Vec<String> {
        g.free_pats
            .iter()
            .filter(|p| !bound.contains_key(*p) && self.leaf_names.contains(*p))
            .cloned()
            .collect()
    }

    /// Moves a condition onto the element a dropped leaf left
    /// behind: `#2 $0` reads the second component, and with the
    /// first gone it is the first, or the whole element where only
    /// one is left.
    fn shift_fields(&self, exp: &Expr) -> Expr {
        let Some((drop, left)) = self.dropped else {
            return exp.clone();
        };
        shift(exp, drop, left)
    }
}

/// Recursively shifts the selectors of an expression.
fn shift(e: &Expr, drop: usize, left: usize) -> Expr {
    if let Expr::Apply(t, f, a, _) = e
        && let Expr::RecordSelector(_, slot) = f.as_ref()
        && let Expr::Input(at, 0) = a.as_ref()
        && *slot >= drop
    {
        if left == 1 {
            return Expr::Input(t.clone(), 0);
        }
        return field_at(&Expr::Input(at.clone(), 0), slot - drop);
    }
    map_expr(e, &|x| shift(x, drop, left))
}

/// Gives a collection a new element type, keeping whether it is a
/// list or a bag.
fn retype(collection: Expr, elem: &Rc<Type>) -> Expr {
    let t = match collection.type_().as_ref() {
        Type::Bag(_) => Type::Bag(elem.clone()),
        _ => Type::List(elem.clone()),
    };
    let t = Rc::new(t);
    match collection {
        Expr::Rel(_, rel) => Expr::Rel(t, rel),
        Expr::Apply(_, f, a, s) => Expr::Apply(t, f, a, s),
        Expr::List(_, items) => Expr::List(t, items),
        other => other,
    }
}

/// Returns whether a collection's element has a type, allowing for
/// an alias, which abbreviates the type it names.
fn same_element(collection: &Expr, t: &Rc<Type>) -> bool {
    match element_type(&collection.type_()) {
        Some(elem) => peel_type(&elem) == peel_type(t),
        None => false,
    }
}

/// Builds a filter, as the relational builder does: a filter over a
/// filter is one filter, their conditions conjoined, the lower one's
/// first.
fn filter_of(input: Expr, condition: Expr) -> Expr {
    if let Expr::Rel(_, rel) = &input
        && let Rel::Filter(inner, lower) = rel.as_ref()
    {
        let merged = and_all(vec![lower.as_ref().clone(), condition.clone()]);
        if let Some(out) = node(Rel::Filter(inner.clone(), Box::new(merged))) {
            return out;
        }
    }
    node(Rel::Filter(Box::new(input.clone()), Box::new(condition)))
        .unwrap_or(input)
}

/// Builds a projection, as the relational builder does: a projection
/// of the element itself is nothing, and a projection over a
/// projection is one projection, the upper expression said over the
/// lower one's.
fn project_of(input: Expr, exp: Expr) -> Expr {
    if matches!(exp, Expr::Input(_, 0)) {
        return input;
    }
    if let Expr::Rel(_, rel) = &input
        && let Rel::Project(inner, lower) = rel.as_ref()
    {
        let merged = subst(&exp, lower, None);
        if let Some(out) = node(Rel::Project(inner.clone(), Box::new(merged))) {
            return out;
        }
    }
    node(Rel::Project(Box::new(input.clone()), Box::new(exp))).unwrap_or(input)
}

/// Projects a join whose inputs were swapped back into the component
/// order the tree above expects: the last `k` first, then the first
/// `m`.
fn permute(join: Expr, m: usize, k: usize) -> Expr {
    let Some(element) = input_of(&join) else {
        return join;
    };
    let mut exps: Vec<Expr> = Vec::with_capacity(m + k);
    for i in 0..k {
        exps.push(field_at(&element, m + i));
    }
    for i in 0..m {
        exps.push(field_at(&element, i));
    }
    project_of(join, tuple_of(exps))
}

/// Takes a collection's rows distinct by the variables a pattern
/// binds, and orders them by the record of those variables.
fn dedup_row(
    collection: Expr,
    pat: &Pat,
    vars: &[(String, Rc<Type>)],
) -> Option<Expr> {
    let row = input_of(&collection)?;
    let mut sorted = vars.to_vec();
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    let mut keys: Vec<(Label, Expr)> = Vec::with_capacity(sorted.len());
    for (name, _) in &sorted {
        keys.push((Label::String(name.clone()), path(pat, &row, name)?));
    }
    let group = node(Rel::Group(Box::new(collection), keys, Vec::new()))?;
    let out = if sorted.len() == 1 {
        let element = input_of(&group)?;
        project_of(group, field_at(&element, 0))
    } else {
        group
    };
    let key = input_of(&out)?;
    node(Rel::Sort(Box::new(out), Box::new(key)))
}

/// Takes a collection's values distinct, in their own order, where a
/// generator may produce one more than once and an unbounded scan
/// yields each assignment once.
fn dedup_named(collection: Expr, name: &str) -> Option<Expr> {
    let element = input_of(&collection)?;
    let group = node(Rel::Group(
        Box::new(collection),
        vec![(Label::String(name.to_string()), element.clone())],
        Vec::new(),
    ))?;
    let row = input_of(&group)?;
    let project = project_of(group, field_at(&row, 0));
    node(Rel::Sort(Box::new(project), Box::new(element)))
}

/// Builds the expression for a node, with the type it derives.
fn node(rel: Rel) -> Option<Expr> {
    let t = rel.derive_type()?;
    Some(Expr::Rel(t, Box::new(rel)))
}

/// The element of a collection, `$0`.
fn input_of(collection: &Expr) -> Option<Expr> {
    Some(Expr::Input(element_type(&collection.type_())?, 0))
}

/// How many leaves a node of a join tree has.
fn leaf_count(node: &Expr) -> usize {
    match node {
        Expr::Rel(_, rel) => match rel.as_ref() {
            Rel::Filter(input, _)
            | Rel::Skip(input, _)
            | Rel::Sort(input, _)
            | Rel::Take(input, _)
            | Rel::Unorder(input) => leaf_count(input),
            Rel::Join(_, _, _, left, right) => {
                leaf_count(left) + leaf_count(right)
            }
            _ => 1,
        },
        _ => 1,
    }
}

/// A fresh binder name.
///
/// The counter is never reset, so that no two binders in a statement
/// share a name: what a plan prints is renumbered by first
/// appearance, but the compiler resolves a binder by name.
fn fresh_name() -> String {
    NEXT_NAME.with(|c| {
        let i = c.get();
        c.set(i + 1);
        format!("v${}", i)
    })
}

fn ground_pat(t: &Rc<Type>) -> Pat {
    Pat::Identifier(t.clone(), fresh_name())
}

/// The names a pattern binds, with their types.
fn pat_names(pat: &Pat) -> Vec<(String, Rc<Type>)> {
    let mut out = Vec::new();
    push_pat_names(pat, &mut out);
    out
}

fn push_pat_names(pat: &Pat, out: &mut Vec<(String, Rc<Type>)>) {
    match pat {
        Pat::Identifier(t, name) => out.push((name.clone(), t.clone())),
        Pat::As(t, name, inner) => {
            out.push((name.clone(), t.clone()));
            push_pat_names(inner, out);
        }
        Pat::Tuple(_, args) | Pat::List(_, args) => {
            args.iter().for_each(|a| push_pat_names(a, out))
        }
        Pat::Record(_, fields, _) => {
            for field in fields {
                match field {
                    PatField::Labeled(_, p) | PatField::Anonymous(p) => {
                        push_pat_names(p, out)
                    }
                }
            }
        }
        Pat::Cons(_, head, tail) => {
            push_pat_names(head, out);
            push_pat_names(tail, out);
        }
        Pat::Constructor(_, _, Some(inner)) => push_pat_names(inner, out),
        _ => {}
    }
}

/// The expression that a pattern's variables denote.
fn pat_exp(pat: &Pat) -> Expr {
    match pat {
        Pat::Tuple(t, args) => {
            Expr::Tuple(t.clone(), args.iter().map(pat_exp).collect())
        }
        Pat::Identifier(t, name) => Expr::Identifier(t.clone(), name.clone()),
        _ => Expr::Identifier(pat.type_(), format!("{:?}", pat)),
    }
}

/// A tuple of expressions, or the one expression.
fn tuple_of(mut exps: Vec<Expr>) -> Expr {
    if exps.len() == 1 {
        return exps.remove(0);
    }
    let types = exps.iter().map(Expr::type_).collect();
    Expr::Tuple(Rc::new(Type::Tuple(types)), exps)
}

/// The expression that reads a pattern's binder out of an element,
/// or `None` if the pattern does not bind it.
fn path(pat: &Pat, element: &Expr, target: &str) -> Option<Expr> {
    match pat {
        Pat::As(_, name, inner) => {
            if name == target {
                Some(element.clone())
            } else {
                path(inner, element, target)
            }
        }
        Pat::Identifier(_, name) if name == target => Some(element.clone()),
        Pat::Tuple(_, args) => args
            .iter()
            .enumerate()
            .find_map(|(i, a)| path(a, &field_at(element, i), target)),
        _ => None,
    }
}

/// The expression that reads a name out of an element, given the
/// expression that says what the element is made of.
fn path_to(element: &Expr, accessor: &Expr, name: &str) -> Option<Expr> {
    match element {
        Expr::Identifier(_, n) if n == name => Some(accessor.clone()),
        Expr::Tuple(_, args) => args
            .iter()
            .enumerate()
            .find_map(|(i, a)| path_to(a, &field_at(accessor, i), name)),
        _ => None,
    }
}

/// Replaces each name of a pattern with the path that reads it out
/// of an element.
fn rename(exp: &Expr, element: &Expr, pat: &Pat) -> Option<Expr> {
    let mut binds: BTreeMap<String, Expr> = BTreeMap::new();
    for (name, _) in pat_names(pat) {
        if let Some(p) = path(pat, element, &name) {
            binds.insert(name, p);
        }
    }
    Some(substitute(exp, &binds))
}

/// Replaces each name of a map with the expression it maps to.
fn substitute(exp: &Expr, map: &BTreeMap<String, Expr>) -> Expr {
    let mut out = exp.clone();
    for (name, value) in map {
        out = substitute_name(&out, name, value);
    }
    out
}

/// The tests a pattern makes on the row it matches, or `None` where
/// the pattern is one this pass cannot test.
fn pat_test(pat: &Pat, row: &Expr, tests: &mut Vec<Expr>) -> Option<()> {
    match pat {
        Pat::Identifier(_, _) | Pat::Wildcard(_) => Some(()),
        Pat::As(_, _, inner) => pat_test(inner, row, tests),
        Pat::Literal(t, value) => {
            if !matches!(peel_type(t), Type::Primitive(PrimitiveType::Unit)) {
                tests.push(eq_exp(row.clone(), literal(t, value), t));
            }
            Some(())
        }
        Pat::Tuple(_, args) => {
            for (i, a) in args.iter().enumerate() {
                pat_test(a, &field_at(row, i), tests)?;
            }
            Some(())
        }
        _ => None,
    }
}

fn literal(t: &Rc<Type>, value: &Val) -> Expr {
    Expr::Literal(t.clone(), value.clone())
}

/// Returns whether a pattern cannot fail to match: a variable, a
/// wildcard, or a tuple of those.
fn destructurable(pat: &Pat) -> bool {
    match pat {
        Pat::As(_, _, inner) => destructurable(inner),
        Pat::Identifier(_, _) | Pat::Wildcard(_) => true,
        Pat::Tuple(_, args) => args.iter().all(destructurable),
        _ => false,
    }
}

/// The pattern that a record of variables, or the one variable, is
/// read under.
fn record_or_atom_pat(vars: &[(String, Rc<Type>)]) -> Pat {
    if vars.len() == 1 {
        return Pat::Identifier(vars[0].1.clone(), vars[0].0.clone());
    }
    let mut sorted = vars.to_vec();
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    let types = sorted.iter().map(|(_, t)| t.clone()).collect();
    let pats = sorted
        .iter()
        .map(|(n, t)| Pat::Identifier(t.clone(), n.clone()))
        .collect();
    Pat::Tuple(Rc::new(Type::Tuple(types)), pats)
}

/// Returns whether a constraint the generator came from reads a
/// name: the name is then bound outside the generator, not by it.
fn reads_free(g: &Generator, name: &str) -> bool {
    g.provenance.iter().any(|c| free_names_in(c).contains(name))
}

/// Replaces `$0` and `$1`, the elements of a node's inputs, with
/// expressions, and folds the selectors that then read a component
/// off a tuple that holds it.
fn subst(exp: &Expr, e0: &Expr, e1: Option<&Expr>) -> Expr {
    let out = replace_inputs_with(exp, &|ordinal| match ordinal {
        0 => Some(e0.clone()),
        1 => e1.cloned(),
        _ => None,
    });
    fold_selectors(&out)
}

/// Reads a component off the tuple that holds it: `#1 (a, b)` is
/// `a`.
fn fold_selectors(e: &Expr) -> Expr {
    if let Expr::Apply(_, f, a, _) = e
        && let Expr::RecordSelector(_, slot) = f.as_ref()
        && let Expr::Tuple(_, args) = a.as_ref()
        && *slot < args.len()
    {
        return fold_selectors(&args[*slot]);
    }
    map_expr(e, &fold_selectors)
}

/// Builds an equality test between two expressions of a type.
fn eq_exp(lhs: Expr, rhs: Expr, t: &Rc<Type>) -> Expr {
    let eq = match peel_type(t) {
        Type::Primitive(PrimitiveType::Bool) => BuiltInFunction::BoolEq,
        Type::Primitive(PrimitiveType::Char) => BuiltInFunction::CharEq,
        Type::Primitive(PrimitiveType::Int) => BuiltInFunction::IntEq,
        Type::Primitive(PrimitiveType::Real) => BuiltInFunction::RealEq,
        Type::Primitive(PrimitiveType::String) => BuiltInFunction::StringEq,
        _ => BuiltInFunction::GEq,
    };
    let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let pair_t = Rc::new(Type::Tuple(vec![t.clone(), t.clone()]));
    let fn_t = Rc::new(Type::Fn(pair_t.clone(), bool_t.clone()));
    Expr::Apply(
        bool_t,
        Box::new(Expr::Literal(fn_t, Val::Fn(eq))),
        Box::new(Expr::Tuple(pair_t, vec![lhs, rhs])),
        Span::new(""),
    )
}

fn true_literal() -> Expr {
    Expr::Literal(
        Rc::new(Type::Primitive(PrimitiveType::Bool)),
        Val::Bool(true),
    )
}

fn is_true(e: &Expr) -> bool {
    matches!(e, Expr::Literal(_, Val::Bool(true)))
}

/// The key an expression is remembered by, where the grounder needs
/// to say "this conjunct again". Two conjuncts that render alike say
/// the same thing, which is all the grounder asks of them.
fn key_of(e: &Expr) -> String {
    e.to_string()
}

/// Rebuilds an expression with a function applied to each of its
/// immediate sub-expressions, through the nodes of a tree.
fn map_expr(e: &Expr, f: &dyn Fn(&Expr) -> Expr) -> Expr {
    let parts = |ps: &[(Label, Expr)]| {
        ps.iter()
            .map(|(l, x)| (l.clone(), f(x)))
            .collect::<Vec<_>>()
    };
    match e {
        Expr::Rel(t, rel) => {
            let rel = match rel.as_ref() {
                // lint: sort until '#}' where '##Rel::'
                Rel::Except(d, args) => {
                    Rel::Except(*d, args.iter().map(f).collect())
                }
                Rel::Filter(input, c) => {
                    Rel::Filter(Box::new(f(input)), Box::new(f(c)))
                }
                Rel::Group(input, keys, aggs) => {
                    Rel::Group(Box::new(f(input)), parts(keys), parts(aggs))
                }
                Rel::Intersect(d, args) => {
                    Rel::Intersect(*d, args.iter().map(f).collect())
                }
                Rel::Join(k, b, c, l, r) => Rel::Join(
                    *k,
                    b.clone(),
                    Box::new(f(c)),
                    Box::new(f(l)),
                    Box::new(f(r)),
                ),
                Rel::Project(input, x) => {
                    Rel::Project(Box::new(f(input)), Box::new(f(x)))
                }
                Rel::Skip(input, x) => {
                    Rel::Skip(Box::new(f(input)), Box::new(f(x)))
                }
                Rel::Sort(input, x) => {
                    Rel::Sort(Box::new(f(input)), Box::new(f(x)))
                }
                Rel::Take(input, x) => {
                    Rel::Take(Box::new(f(input)), Box::new(f(x)))
                }
                Rel::Union(d, args) => {
                    Rel::Union(*d, args.iter().map(f).collect())
                }
                Rel::Unorder(input) => Rel::Unorder(Box::new(f(input))),
            };
            Expr::Rel(t.clone(), Box::new(rel))
        }
        _ => rel_lowerer::map_children(e, f),
    }
}

/// Applies a function to each immediate sub-expression.
fn for_each_child(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    let seen = RefCell::new(Vec::new());
    map_expr(e, &|c| {
        seen.borrow_mut().push(c.clone());
        c.clone()
    });
    for c in seen.into_inner() {
        f(&c);
    }
}
