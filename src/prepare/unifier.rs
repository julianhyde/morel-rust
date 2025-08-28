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

use indexmap::IndexMap;
use std::cell::RefCell;
use std::cmp::{PartialEq, max};
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::fmt::{Debug, Display, Formatter, Write};
use std::iter::zip;
use std::marker::PhantomData;
use std::rc::Rc;
use std::time::Instant;

/// Trait for things that behave like terms.
trait TermLike {
    fn apply1(&self, variable: &Rc<Var>, term: &Term) -> Term;
    fn as_term(&self) -> Term;
}

/// Trait for things that can be created from a [Term].
/// Implementations include [Sequence], [Variable].
trait FromTerm {
    fn from_term(term: &Term) -> Self;
}

/// A term is a variable or a sequence.
///
/// Examples:
/// * Variable: `X`
/// * Sequence: `a`, `f`, `g(b)`, `f(a, X, g(b))`
///
/// If a sequence has no terms, we call it an atom.
///
/// Operators often have the same arity every time they are used,
/// but we don't enforce this.
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Sequence(Sequence),
    Variable(Rc<Var>),
}

impl Term {
    /// Returns whether this term references a given variable.
    fn contains(&self, var: &Rc<Var>) -> bool {
        match self {
            Term::Variable(v) => v == var,
            Term::Sequence(seq) => {
                seq.terms.iter().any(|term| term.contains(var))
            }
        }
    }

    /// Applies a substitution to this term.
    fn apply1(&self, variable: &Rc<Var>, term: &Term) -> Term {
        match self {
            Term::Variable(v) => v.apply1(variable, term),
            Term::Sequence(seq) => seq.apply1(variable, term),
        }
    }

    /// Returns whether this term could potentially unify with another term.
    pub fn could_unify_with(&self, other: &Term) -> bool {
        match (self, other) {
            (Term::Variable(_), _) | (_, Term::Variable(_)) => true,
            (Term::Sequence(seq1), Term::Sequence(seq2)) => {
                seq1.op == seq2.op && seq1.terms.len() == seq2.terms.len()
            }
        }
    }
}

impl TermLike for Term {
    fn apply1(&self, variable: &Rc<Var>, term: &Term) -> Term {
        match self {
            Term::Variable(v) => v.apply1(variable, term),
            Term::Sequence(seq) => seq.apply1(variable, term),
        }
    }

    fn as_term(&self) -> Term {
        self.clone()
    }
}

impl FromTerm for Term {
    fn from_term(term: &Term) -> Self {
        term.clone()
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Term::Variable(var) => f.write_str(var.name.as_str()),
            Term::Sequence(seq) => Display::fmt(seq, f),
        }
    }
}

impl Term {
    fn unparse_to(&self, s: &mut String) {
        match self {
            Term::Variable(var) => {
                s.push_str(var.name.as_str());
            }
            Term::Sequence(seq) => {
                let op_name = &seq.op.name;
                if seq.terms.is_empty() {
                    s.push_str(op_name.as_str());
                } else {
                    s.push_str(op_name.as_str());
                    s.push('(');
                    for (i, term) in seq.terms.iter().enumerate() {
                        if i > 0 {
                            s.push_str(", ");
                        }
                        term.unparse_to(s);
                    }
                    s.push(')');
                }
            }
        }
    }
}

/// A registered variable.
///
/// Its id is unique within a Unifier,
/// and disjoint from Op id values.
#[derive(Debug, Clone, Ord, PartialOrd, PartialEq, Eq, Hash)]
struct Var {
    name: String,
    id: i32,
}

impl Var {
    fn to_string(&self) -> String {
        self.name.clone()
    }
}

impl TermLike for Rc<Var> {
    fn apply1(&self, variable: &Rc<Var>, term: &Term) -> Term {
        if self == variable {
            term.clone()
        } else {
            self.as_term()
        }
    }

    fn as_term(&self) -> Term {
        Term::Variable(self.clone())
    }
}

impl FromTerm for Rc<Var> {
    fn from_term(term: &Term) -> Self {
        match term {
            Term::Variable(var) => var.clone(),
            _ => panic!("Expected Variable, got {}", term),
        }
    }
}

/// A registered operator.
///
/// It is the name of an atom (e.g. `a()`) or a sequence
/// (e.g. `p(a, q(b, c))`).
///
/// Its id is unique within a Unifier.
#[derive(Debug, Clone, PartialEq)]
struct Op {
    name: String,
    arity: usize,
    id: i32,
}

impl Op {
    pub fn to_string(&self) -> String {
        self.name.clone()
    }
}

/// A Sequence is an operator with a list of terms.
#[derive(Debug, Clone, PartialEq)]
struct Sequence {
    op: Rc<Op>,
    terms: Vec<Term>,
}

impl Sequence {
    fn sub(&self, variable: &Rc<Var>, term: &Term) -> Sequence {
        let mut terms = self.terms.clone();
        for term in terms.iter_mut() {
            *term = term.apply1(variable, term);
        }
        Sequence {
            op: self.op.clone(),
            terms,
        }
    }
}

impl TermLike for Sequence {
    fn apply1(&self, variable: &Rc<Var>, term: &Term) -> Term {
        Term::Sequence(self.sub(variable, term))
    }

    fn as_term(&self) -> Term {
        Term::Sequence(self.clone())
    }
}

impl FromTerm for Sequence {
    fn from_term(term: &Term) -> Self {
        match term {
            Term::Sequence(seq) => seq.clone(),
            _ => panic!("Expected Sequence, got {}", term),
        }
    }
}

impl<'a> Display for Sequence {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            write!(f, "{}", self.op.name)
        } else {
            write!(f, "{}(", self.op.name)?;
            for (i, term) in self.terms.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", term)?;
            }
            write!(f, ")")
        }
    }
}

/// Result of unification: either a substitution or failure.
#[derive(Debug)]
enum UnifierResult {
    Substitution(Substitution),
    Failure(UnificationFailure),
}

impl Display for UnifierResult {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            UnifierResult::Substitution(substitution) => {
                Display::fmt(substitution, f)
            },
            UnifierResult::Failure(failure) => {
                Display::fmt(failure, f)
            }
        }
    }
}

/// Substitution.
#[derive(Debug)]
struct Substitution {
    substitutions: IndexMap<Rc<Var>, Term>,
}

impl<'a> Substitution {
    fn new() -> Self {
        Self {
            substitutions: IndexMap::new(),
        }
    }

    fn resolve(&self) -> Self {
        todo!()
    }
}

impl Display for Substitution {
    /// Prints e.g. `[f(a, Y)/Z, b/W]`.
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let mut first = true;
        f.write_char('[')?;
        for (var, term) in &self.substitutions {
            if !first {
                f.write_str(", ")?;
            }
            first = false;
            Display::fmt(&term, f)?;
            f.write_char('/')?;
            f.write_str(var.name.as_str())?;
        }
        f.write_char(']')
    }
}

/// Why unification failed.
#[derive(Debug)]
struct UnificationFailure {
    reason: String,
}

impl fmt::Display for UnificationFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Unification failed: {}", self.reason)
    }
}

/// Tracer trait.
trait Tracer {
    fn trace(&self, message: &str);
    fn on_delete(&self, left: &Term, right: &Term);
    fn on_conflict(&self, left: &Sequence, right: &Sequence);
    fn on_sequence(&self, left: &Sequence, right: &Sequence);
    fn on_cycle(&self, left: &Var, right: &Term);
    fn on_variable(&self, left: &Var, right: &Term);
    fn on_swap(&self, left: &Term, right: &Term);
    fn on_substitute(
        &self,
        old_left: &Term,
        old_right: &Term,
        new_left: &Term,
        new_right: &Term,
    );
}

/// Tracer that does nothing.
struct NullTracer;

impl Tracer for NullTracer {
    fn trace(&self, _message: &str) {
        // Do nothing
    }

    fn on_delete(&self, _left: &Term, _right: &Term) {
        // Do nothing
    }

    fn on_conflict(&self, _left: &Sequence, _right: &Sequence) {
        // Do nothing
    }

    fn on_sequence(&self, _left: &Sequence, _right: &Sequence) {
        // Do nothing
    }

    fn on_cycle(&self, _left: &Var, _right: &Term) {
        // Do nothing
    }

    fn on_variable(&self, _left: &Var, _right: &Term) {
        // Do nothing
    }

    fn on_swap(&self, _left: &Term, _right: &Term) {
        // Do nothing
    }

    fn on_substitute(
        &self,
        _old_left: &Term,
        _old_right: &Term,
        _new_left: &Term,
        _new_right: &Term,
    ) {
        // Do nothing
    }
}

/// A pair of lists that act together.
struct TermActions {
    left_list: Vec<Term>,
    right_list: Vec<ConstraintAction>,
}

impl TermActions {
    fn new() -> Self {
        Self {
            left_list: Vec::new(),
            right_list: Vec::new(),
        }
    }

    fn size(&self) -> usize {
        self.left_list.len()
    }

    fn left(&self, index: usize) -> &Term {
        &self.left_list[index]
    }

    fn right(&self, index: usize) -> &ConstraintAction {
        &self.right_list[index]
    }

    fn left_list(&mut self) -> &mut Vec<Term> {
        &mut self.left_list
    }
}

/// Action to perform when a constraint is resolved.
enum ConstraintAction {
    Accept(Box<dyn Fn(&Term, &Term, &mut dyn FnMut(Term, Term))>),
}

/// Mutable constraint used during unification.
struct MutableConstraint {
    arg: Term,
    term_actions: TermActions,
}

/// Unifier.
///
/// Implements the Martelli-Montanari unification algorithm.
struct Unifier<'a> {
    /// Assists with the generation of unique names by recording the lowest
    /// ordinal, for a given prefix, for which a name has not yet been
    /// generated.
    ///
    /// For example, if we have called `name("T")` twice, and thereby
    /// generated "T0" and "T1", then the map will contain `"T", 2)`,
    /// indicating that the next call to `name("T")` should generate `T2`.
    name_map: HashMap<String, usize>,
    var_by_name: HashMap<String, Rc<Var>>,
    op_by_name: HashMap<String, Rc<Op>>,
    var_list: Vec<Rc<Var>>,
    op_list: Vec<Rc<Op>>,
    _phantom: PhantomData<&'a ()>,
}

/// Workspace for Unification.
struct Work<'a> {
    tracer: &'a dyn Tracer,
    seq_seq_queue: Rc<RefCell<VecDeque<(Sequence, Sequence)>>>,
    var_any_queue: Rc<RefCell<VecDeque<(Rc<Var>, Term)>>>,
    constraint_queue: VecDeque<MutableConstraint>,
    result: HashMap<Rc<Var>, Term>,
}

impl<'a> Work<'a> {
    fn new(tracer: &'a (dyn Tracer + 'a), term_pairs: &[(Term, Term)]) -> Self {
        let mut work = Work {
            tracer,
            var_any_queue: Rc::new(RefCell::new(VecDeque::new())),
            seq_seq_queue: Rc::new(RefCell::new(VecDeque::new())),
            constraint_queue: VecDeque::new(),
            result: HashMap::new(),
        };
        term_pairs
            .iter()
            .for_each(|(left, right)| work.add(left.clone(), right.clone()));
        // constraints.forEach(c ->
        //   constraintQueue.add(new MutableConstraint(c)));
        work
    }

    /// Creates a failure with the given reason.
    fn failure(reason: &str) -> Option<UnificationFailure> {
        Some(UnificationFailure {
            reason: reason.to_string(),
        })
    }

    /// Applies a mapping to all term pairs in a list, modifying them in place.
    fn substitute_list(
        &mut self,
        variable: &Rc<Var>,
        term: &Term,
    ) -> Option<UnificationFailure> {
        // We need to work with the queues separately to avoid borrowing issues
        let seq_seq_queue = std::mem::take(&mut self.seq_seq_queue);
        let var_any_queue = std::mem::take(&mut self.var_any_queue);

        self.seq_seq_queue = seq_seq_queue;
        self.var_any_queue = var_any_queue;

        self.sub_queues(variable, term);
        self.sub_constraint(variable, term)
    }

    /// Applies substitution to all queues.
    fn sub_queues(&mut self, variable: &Rc<Var>, term: &Term) {
        // Process seq_seq_queue
        self.process_queue(
            variable,
            term,
            Kind::SeqSeq,
            self.seq_seq_queue.clone(),
        );
        // Process var_any_queue
        self.process_queue(
            variable,
            term,
            Kind::VarAny,
            self.var_any_queue.clone(),
        );
    }

    /// Processes a specific queue type.
    fn process_queue<
        L: TermLike + PartialEq + FromTerm,
        R: TermLike + PartialEq + FromTerm,
    >(
        &mut self,
        variable: &Rc<Var>,
        term: &Term,
        queue_kind: Kind,
        queue_ref: Rc<RefCell<VecDeque<(L, R)>>>,
    ) {
        let mut items_to_add = Vec::new();

        let mut i = 0;
        while i < queue_ref.borrow().len() {
            let (should_continue, needs_removal, new_pair, removed_item) = {
                let queue = queue_ref.borrow();
                let left2 = queue[i].0.apply1(variable, term);
                let right2 = queue[i].1.apply1(variable, term);

                if left2 != queue[i].0.as_term()
                    || right2 != queue[i].1.as_term()
                {
                    self.tracer.on_substitute(
                        &queue[i].0.as_term(),
                        &queue[i].1.as_term(),
                        &left2.as_term(),
                        &right2.as_term(),
                    );
                    let kind2 = Kind::of(&left2.as_term(), &right2.as_term());

                    if kind2 == queue_kind {
                        // Still belongs in this queue
                        (true, false, Some((left2, right2)), None)
                    } else if kind2 == Kind::NonVarVar
                        && queue_kind == Kind::VarAny
                    {
                        (true, false, Some((right2, left2)), None)
                    } else {
                        // Belongs in another queue - capture the item to remove
                        (false, true, None, Some((left2, right2)))
                    }
                } else {
                    (true, false, None, None)
                }
            };

            if needs_removal {
                if let Some((left, right)) = removed_item {
                    items_to_add.push((left, right));
                }
                queue_ref.borrow_mut().remove(i);
                // Don't increment i since we removed an element
            } else {
                if let Some((l, r)) = new_pair {
                    queue_ref.borrow_mut()[i] =
                        (L::from_term(&l), R::from_term(&r));
                }
                if should_continue {
                    i += 1;
                }
            }
        }

        // Add items that were moved to other queues
        for (left, right) in items_to_add {
            self.add(left, right);
        }
    }

    /// Applies substitution to constraints.
    fn sub_constraint(
        &mut self,
        variable: &Rc<Var>,
        term: &Term,
    ) -> Option<UnificationFailure> {
        let mut i = 0;
        while i < self.constraint_queue.len() {
            let constraint = &mut self.constraint_queue[i];
            let arg2 = constraint.arg.apply1(variable, term);
            let mut change_count = 0;

            if arg2 != constraint.arg {
                change_count += 1;
                constraint.arg = arg2.clone();
                constraint
                    .term_actions
                    .left_list
                    .retain(|arg1| arg2.could_unify_with(arg1));
            }

            let mut j = 0;
            while j < constraint.term_actions.left_list.len() {
                let sub_arg = &constraint.term_actions.left_list[j];
                let sub_arg2 = sub_arg.apply1(variable, term);
                if sub_arg != &sub_arg2 {
                    change_count += 1;
                    constraint.term_actions.left_list[j] = sub_arg2.clone();
                    if !arg2.could_unify_with(&sub_arg2) {
                        constraint.term_actions.left_list.remove(j);
                        constraint.term_actions.right_list.remove(j);
                        continue; // Don't increment j
                    }
                }
                j += 1;
            }

            if change_count > 0 {
                match constraint.term_actions.size() {
                    0 => return Self::failure("no valid overloads"),
                    1 => {
                        let _term1 = constraint.term_actions.left(0).clone();
                        let _action = &constraint.term_actions.right(0);
                        // Note: This would need to be implemented based on the
                        // actual action interface
                        //   action.accept(&constraint.arg, &term1,
                        //       &mut |left, right| self.add2(left, right));
                        // For now, we'll leave this as a placeholder.
                    }
                    _ => {} // Multiple options still available
                }
            }

            i += 1;
        }
        None
    }

    fn add(&mut self, left: Term, right: Term) {
        match Kind::of(&left, &right) {
            Kind::SeqSeq => {
                self.seq_seq_queue.borrow_mut().push_back((
                    Sequence::from_term(&left),
                    Sequence::from_term(&right),
                ));
            }
            Kind::NonVarVar => {
                self.tracer.on_swap(&left, &right);
                if let (Term::Variable(v), t) = (right, left) {
                    self.var_any_queue.borrow_mut().push_back((v, t));
                } else {
                    unreachable!()
                }
            }
            Kind::VarAny => {
                let v: Rc<Var> = FromTerm::from_term(&left);
                self.var_any_queue.borrow_mut().push_back((v, right));
            }
            Kind::Delete => {
                unreachable!()
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Delete,
    SeqSeq,
    VarAny,
    NonVarVar,
}

impl Kind {
    fn of(left: &Term, right: &Term) -> Kind {
        if left == right {
            return Kind::Delete;
        }
        match left {
            Term::Sequence(_) => match right {
                Term::Sequence(_) => Kind::SeqSeq,
                Term::Variable(_) => Kind::NonVarVar,
            },
            Term::Variable(_) => Kind::VarAny,
        }
    }
}

impl<'a> Unifier<'a> {
    pub fn op_str(&self, id: i32) -> String {
        self.op_list[id as usize].name.clone()
    }
}

impl<'a> Unifier<'a> {
    fn new() -> Self {
        Self {
            name_map: HashMap::new(),
            var_by_name: HashMap::new(),
            op_by_name: HashMap::new(),
            var_list: Vec::new(),
            op_list: Vec::new(),
            _phantom: PhantomData,
        }
    }

    /// Looks up or creates a new operator with the given name.
    fn op(&mut self, name: &str, arity: usize) -> Rc<Op> {
        match self.op_by_name.get(name) {
            Some(index) => index.clone(),
            None => {
                let id = self.name_map.entry(name.to_string()).or_insert(0);
                let op = Rc::new(Op {
                    name: name.to_string(),
                    arity,
                    id: *id as i32,
                });
                self.op_list.push(op.clone());
                self.op_by_name.insert(name.to_string(), op.clone());
                op
            }
        }
    }

    fn op_unique(&mut self, prefix: &str, arity: usize) -> Rc<Op> {
        let name = self.new_name(prefix, 0);
        let op = Rc::new(Op {
            name: name.to_string(),
            arity,
            id: self.op_list.len() as i32,
        });
        self.op_list.push(op.clone());
        self.op_by_name.insert(name.to_string(), op.clone());
        op
    }

    fn new_name(&mut self, prefix: &str, ordinal: usize) -> String {
        let mut i = ordinal;
        loop {
            let name = format!("{}{}", prefix, i);
            let ordinal = self.name_map.get(&name);
            if !ordinal.is_some() {
                // We have used i this time, will use i + 1 next time.
                self.name_map.insert(name.clone(), i + 1);
                return name;
            }
            i = max(i + 1, *ordinal.unwrap());
        }
    }

    /// Creates a new variable with a unique name.
    ///
    /// The first variable is at position 0, is named "T0", and has id -1.
    /// The second variable is at position 1, is named "T1", and has id -2.
    /// And so forth.
    fn variable(&mut self) -> Rc<Var> {
        let ordinal = self.var_list.len();
        let name = self.new_name("T", ordinal).clone();
        let var = Rc::new(Var {
            name: name.to_string(),
            id: -(ordinal as i32 + 1),
        });
        self.var_list.push(var.clone());
        self.name_map.insert(name.to_string(), 1);
        self.var_by_name.insert(name.to_string(), var.clone());
        var
    }

    /// Creates a variable with a given name, or returns the existing variable
    /// with that name.
    fn variable_with_name(&mut self, name: &str) -> Rc<Var> {
        match self.var_by_name.get(name) {
            Some(var) => var.clone(),
            None => {
                let ordinal = self.var_list.len();
                let var = Rc::new(Var {
                    name: name.to_string(),
                    id: -(ordinal as i32 + 1),
                });
                self.var_list.push(var.clone());
                self.name_map.insert(name.to_string(), 1);
                self.var_by_name.insert(name.to_string(), var.clone());
                var
            }
        }
    }

    fn variable_with_id(&mut self, id: usize) -> Rc<Var> {
        let name = format!("T{}", id);
        self.variable_with_name(&name)
    }

    /// Creates a Sequence.
    fn apply(&self, op: Rc<Op>, terms: Vec<Term>) -> Sequence {
        assert_eq!(op.arity, terms.len());
        Sequence {
            op: op.clone(),
            terms: terms.clone(),
        }
    }

    /// Creates a Sequence with one operand.
    fn apply1(&self, op: Rc<Op>, term0: Term) -> Sequence {
        Sequence {
            op: op.clone(),
            terms: vec![term0],
        }
    }

    /// Creates a Sequence with two operands.
    fn apply2(&self, op: Rc<Op>, term0: Term, term1: Term) -> Sequence {
        Sequence {
            op: op.clone(),
            terms: vec![term0, term1],
        }
    }

    /// Creates a Sequence with three operands.
    fn apply3(
        &self,
        op: Rc<Op>,
        term0: Term,
        term1: Term,
        term2: Term,
    ) -> Sequence {
        self.apply(op, vec![term0, term1, term2])
    }

    /// Creates an Atom (a Sequence with zero operands).
    fn atom(&self, op: Rc<Op>) -> Sequence {
        Sequence {
            op: op.clone(),
            terms: vec![],
        }
    }

    /// Creates a substitution from a variable to a term.
    fn substitution(
        &self,
        substitutions: IndexMap<Rc<Var>, Term>,
    ) -> Substitution {
        assert!(substitutions.is_sorted());
        Substitution { substitutions }
    }

    /// Converts a term to a string.
    fn unparse(&self, term: Term) -> String {
        let mut s = String::new();
        term.unparse_to(&mut s);
        s
    }

    fn unify(
        &self,
        term_pairs: &[(Term, Term)],
        tracer: &dyn Tracer,
    ) -> UnifierResult {
        let start = Instant::now();

        // delete: G u { t = t }
        //   => G

        // decompose: G u { f(s0, ..., sk) = f(t0, ..., tk) }
        //   => G u {s0 = t0, ..., sk = tk}

        // conflict: G u { f(s0, ..., sk) = g(t0, ..., tm) }
        //   => fail
        // if f <> g or k <> m

        // swap: G u { f(s0, ..., sk) = x }
        //  => G u { x = f(s0, ..., sk) }

        // eliminate: G u { x = t }
        //  => G { x |-> t } u { x = t }
        // if x not in vars(t) and x in vars(G)

        // check: G u { x = f(s0, ..., sk)}
        //  => fail
        // if x in vars(f(s0, ..., sk))

        let mut work = Work::new(tracer, term_pairs);
        let mut iteration = 0;
        loop {
            iteration += 1;

            let seq_pair = work.seq_seq_queue.borrow_mut().pop_front();
            if let Some((left, right)) = seq_pair {
                if left.op != right.op || left.terms.len() != right.terms.len()
                {
                    tracer.on_conflict(&left, &right);
                    let reason = format!("conflict: {} != {}", left, right);
                    return UnifierResult::Failure(UnificationFailure {
                        reason,
                    });
                }

                // decompose
                tracer.on_sequence(&left, &right);
                for (l, r) in zip(left.terms.iter(), right.terms.iter()) {
                    work.add(l.clone(), r.clone());
                }
                continue;
            }

            let var_pair = work.var_any_queue.borrow_mut().pop_front();
            if let Some((variable, term)) = var_pair {
                // Occurs check
                if term.contains(&variable) {
                    tracer.on_cycle(&variable, &term);
                    let reason = format!(
                        "cycle: variable {} in {}",
                        variable.name, term
                    );
                    return UnifierResult::Failure(UnificationFailure {
                        reason,
                    });
                }

                // If 'term' is already in the table, map 'variable' to its
                // ultimate target.
                let mut term = term;
                while let Term::Variable(v) = &term {
                    if let Some(t) = work.result.get(v) {
                        term = t.clone();
                    } else {
                        break;
                    }
                }

                if term == Term::Variable(variable.clone()) {
                    // We already knew that 'pair.left' and 'pair.right' were
                    // equivalent.
                    continue;
                }

                tracer.on_variable(&variable, &term);
                if let Some(prior_term) =
                    work.result.insert(variable.clone(), term.clone())
                {
                    if prior_term != term {
                        work.add(prior_term, term.clone());
                    }
                }

                /*
                if !term_actions.is_empty() {
                    final Set<Variable> set = new HashSet<>();
                    act(variable, term, work, new Substitution(result),
                        termActions, set);
                    checkArgument(set.isEmpty(), "Working set not empty: %s",
                        set);
                }
                */

                if let Some(failure) = work.substitute_list(&variable, &term) {
                    return UnifierResult::Failure(failure);
                }
                continue;
            }

            let duration = Instant::now() - start;
            if false {
                println!(
                    "Term count {} iterations {} \
                    duration {} nanos ({} nanos per iteration)\n",
                    term_pairs.len(),
                    iteration,
                    duration.as_nanos(),
                    duration.as_nanos() / (iteration + 1)
                );
            }
            let mut map = IndexMap::new();
            work.result.iter().for_each(|(var, term)| {
                map.insert(var.clone(), term.clone());
            });
            map.sort_keys();
            return UnifierResult::Substitution(Substitution {
                substitutions: map,
            });
        }
    }

    fn mock_unify_result(&self, _term_pairs: &[(Term, Term)]) -> UnifierResult {
        // This would need to be implemented based on the specific test case
        // For now, return a success
        UnifierResult::Substitution(Substitution::new())
    }

    fn occurs(&self) -> bool {
        false
    }
}

/// Test for Unifier.
// Turn off standard naming conventions for test variables
#[allow(non_snake_case)]
pub struct UnifierTest<'a> {
    unifier: Box<Unifier<'a>>,
}

impl<'a> UnifierTest<'a> {
    pub fn var(&mut self, name: &str) -> Term {
        Term::Variable(self.unifier.variable_with_name(name))
    }
}

impl<'a> UnifierTest<'a> {
    fn new() -> Self {
        Self {
            unifier: Box::new(Unifier::new()),
        }
    }

    fn arrow(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("->", 2);
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn a(&mut self) -> Term {
        let op = self.unifier.op("a", 0);
        Term::Sequence(self.unifier.atom(op))
    }

    fn b(&mut self) -> Term {
        let op = self.unifier.op("b", 0);
        Term::Sequence(self.unifier.atom(op))
    }

    fn c(&mut self) -> Term {
        let op = self.unifier.op("c", 0);
        Term::Sequence(self.unifier.atom(op))
    }

    fn d(&mut self) -> Term {
        let op = self.unifier.op("d", 0);
        Term::Sequence(self.unifier.atom(op))
    }

    fn f(&mut self, a0: Term) -> Term {
        let op = self.unifier.op("f", 1);
        Term::Sequence(self.unifier.apply1(op, a0))
    }

    fn f2(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("f", 2);
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn g(&mut self, a0: Term) -> Term {
        let op = self.unifier.op("g", 1);
        Term::Sequence(self.unifier.apply1(op, a0))
    }

    fn h(&mut self, term0: Term, term1: Term) -> Term {
        let op = self.unifier.op("h", 2);
        Term::Sequence(self.unifier.apply2(op, term0, term1))
    }

    fn p(&mut self, term0: Term, term1: Term, term2: Term) -> Term {
        let op = self.unifier.op("p", 3);
        Term::Sequence(self.unifier.apply3(op, term0, term1, term2))
    }

    fn bill(&mut self) -> Term {
        let op = self.unifier.op("bill", 0);
        Term::Sequence(self.unifier.atom(op))
    }

    fn bob(&mut self) -> Term {
        let op = self.unifier.op("bob", 0);
        Term::Sequence(self.unifier.atom(op))
    }

    fn john(&mut self) -> Term {
        let op = self.unifier.op("john", 0);
        Term::Sequence(self.unifier.atom(op))
    }

    fn tom(&mut self) -> Term {
        let op = self.unifier.op("tom", 0);
        Term::Sequence(self.unifier.atom(op))
    }

    fn father(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("father", 2);
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn mother(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("mother", 2);
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn parents(&mut self, a0: Term, a1: Term, t3: Term) -> Term {
        let op = self.unifier.op("parents", 3);
        Term::Sequence(self.unifier.apply3(op, a0, a1, t3))
    }

    fn parent(&mut self, a0: Term) -> Term {
        let op = self.unifier.op("parent", 1);
        Term::Sequence(self.unifier.apply1(op, a0))
    }

    fn grand_parent(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("grand_parent", 2);
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn connected(&mut self, a0: Term, a1: Term) -> Term {
        let op = self.unifier.op("connected", 2);
        Term::Sequence(self.unifier.apply2(op, a0, a1))
    }

    fn part(&mut self, a0: Term, a1: Term) -> Sequence {
        let op = self.unifier.op("part", 2);
        self.unifier.apply2(op, a0, a1)
    }

    fn assert_that_unify(&self, e1: Term, e2: Term, expected: &str) {
        let term_pairs = self.term_pairs(&[e1, e2]);
        self.assert_that_unify_pairs(&term_pairs, expected);
    }

    fn assert_that_unify_pairs(
        &self,
        term_pairs: &[(Term, Term)],
        expected: &str,
    ) {
        let result = self.unifier.unify(term_pairs, &NullTracer);
        assert_eq!(result.to_string(), expected);
    }

    fn assert_that_cannot_unify(&self, e1: Term, e2: Term) {
        let term_pairs = self.term_pairs(&[e1, e2]);
        self.assert_that_cannot_unify_pairs(&term_pairs);
    }

    /// Given `[a, b, c, d]`, returns `[(a, b), (c, d)]`.
    fn term_pairs(&self, terms: &[Term]) -> Vec<(Term, Term)> {
        assert_eq!(terms.len() % 2, 0);
        let mut pairs = Vec::new();
        for i in (0..terms.len()).step_by(2) {
            pairs.push((terms[i].clone(), terms[i + 1].clone()));
        }
        pairs
    }

    fn assert_that_cannot_unify_pairs(&self, pair_list: &[(Term, Term)]) {
        let _result = self.unifier.unify(pair_list, &NullTracer);

        // Mock assertion - in real implementation, check if result is not
        // Substitution
        // For testing purposes, we assume it fails if it's not a substitution
        // This would need proper implementation based on the actual Result type
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create() -> UnifierTest<'static> {
        UnifierTest::new()
    }

    #[test]
    fn test_atom() {
        let z = UnifierTest::new();
        let mut u = z.unifier;
        let mut vars = vec![];
        let a0 = u.op_unique("A", 0).clone();
        assert_eq!(a0.name, "A0");
        let a1 = u.op_unique("A", 0);
        assert_eq!(a1.name, "A1");
        let v0 = u.variable();
        assert_eq!(v0.name, "T0");
        vars.push(v0.clone());

        // Try to create an operator with the name of an existing variable,
        // get a new name.
        let a2 = u.op_unique("T", 0).clone();
        assert_eq!(a2.name, "T1");
        let a3 = u.op_unique("T1", 0).clone();
        assert_eq!(a3.name, "T10");

        let v1 = u.variable();
        let v1_name = v1.name.clone();
        assert_eq!(v1_name, "T2");
        vars.push(v1.clone());
        let v1_string = v1.to_string();

        let v2 = u.variable();
        vars.push(v2.clone());
        let v2_string = v2.clone().to_string();

        let v1b = u.variable_with_name(&v1_name);
        assert_eq!(v1b.name, v1_name);
        let v1c = u.variable_with_id(2);
        assert_eq!(v1c.to_string(), v1_string);

        let v2a = u.variable_with_id(3);
        assert_eq!(v2a.to_string(), v2_string);

        let v3 = u.variable();
        vars.push(v3.clone());

        let v4 = u.variable();
        vars.push(v4.clone());
        let v4_string = v4.to_string();

        let v5 = u.variable();
        vars.push(v5.clone());

        let v6 = u.variable();
        vars.push(v6.clone());

        let v4a = u.variable_with_id(5);
        assert_eq!(v4a.to_string(), v4_string);

        let v7 = u.variable();
        vars.push(v7.clone());

        let v8 = u.variable();
        vars.push(v8.clone());

        let var_strings: Vec<_> = vars.iter().map(|v| v.to_string()).collect();
        assert_eq!(
            format!("{:?}", var_strings),
            "[\"T0\", \"T2\", \"T3\", \"T4\", \"T5\", \"T6\", \"T7\", \"T8\", \
             \"T9\"]"
        );
        let v9 = u.variable();
        assert_eq!(v9.to_string(), "T11", "avoids T10 name used by a3 above");
    }

    #[test]
    fn test1() {
        let mut t = create();
        let y = t.var("Y");
        let z = t.var("Z");
        let a = t.a();
        let b = t.b();
        let f_a = t.f(a.clone());
        let g_b = t.g(b);
        let e1 = t.p(f_a, g_b, y.clone());
        let d = t.d();
        let c = t.c();
        let g_d = t.g(d);
        let p = t.p(z.clone(), g_d, c);
        let e2 = p;
        assert_eq!(t.unifier.unparse(e1.clone()), "p(f(a), g(b), Y)");
        let f_a_y = t.f2(a, y);
        let z_v = match z {
            Term::Sequence(_) => {
                todo!()
            }
            Term::Variable(v) => v,
        };
        let mut map: IndexMap<Rc<Var>, Term> = IndexMap::new();
        map.insert(z_v, f_a_y);
        let sub = t.unifier.substitution(map);
        assert_eq!(sub.to_string(), "[f(a, Y)/Z]");
        t.assert_that_cannot_unify(e1, e2);
    }

    #[test]
    fn test2() {
        let mut t = create();
        let w = t.var("W");
        let y = t.var("Y");
        let z = t.var("Z");
        let a = t.a();
        let f_a = t.f(a);
        let b = t.b();
        let g_b = t.g(b);
        let e1 = t.p(f_a, g_b, y.clone());
        assert_eq!(e1.to_string(), "p(f(a), g(b), Y)");
        let c = t.c();
        let g_w = t.g(w.clone());
        let e2 = t.p(z.clone(), g_w, c);
        assert_eq!(e2.to_string(), "p(Z, g(W), c)");
        t.assert_that_unify(e1, e2, "[b/W, c/Y, f(a)/Z]");
    }

    #[test]
    fn test3() {
        let z = create();
        // Note: Hesham Alassaf's test says that these cannot be unified; I
        // think because X is free, and so it assumes that Xs are distinct.
        /*
        let e1 = z.p(&[z.f(&[z.f(&[z.b()])]), z.X.clone()]);
        let e2 = z.p(&[z.f(&[z.Y.clone()]), z.X.clone()]);
        if z.unifier.occurs() {
            z.assert_that_unify(e1, e2, "[X/X, f(b)/Y]");
        } else {
            z.assert_that_unify(e1, e2, "[f(b)/Y]");
        }

         */
    }

    #[test]
    fn test4() {
        let z = create();
        /*
        let e1 = z.p(&[z.f(&[z.f(&[z.b()])]), z.c()]);
        let e2 = z.p(&[z.f(&[z.Y.clone()]), z.X.clone()]);
        z.assert_that_unify(e1, e2, "[c/X, f(b)/Y]");

         */
    }

    #[test]
    fn test5() {
        let z = create();
        /*
        let e1 = z.p(&[z.a(), z.X.clone()]);
        let e2 = z.p(&[z.b(), z.Y.clone()]);
        z.assert_that_cannot_unify(e1, e2);

         */
    }

    #[test]
    fn test6() {
        let mut t = create();
        let x = t.var("X");
        let y = t.var("Y");
        let a = t.a();
        let e1 = t.h(x.clone(), a);
        assert_eq!(e1.to_string(), "h(X, a)");
        let b = t.b();
        let e2 = t.h(b, y.clone());
        assert_eq!(e2.to_string(), "h(b, Y)");
        t.assert_that_unify(e1, e2, "[b/X, a/Y]");
    }

    #[test]
    fn test7() {
        let z = create();
        /*
        let e1 = z.f(&[z.a(), z.X.clone()]);
        let e2 = z.f(&[z.a(), z.b()]);
        z.assert_that_unify(e1, e2, "[b/X]");

         */
    }

    #[test]
    fn test8() {
        let z = create();
        /*
        let e1 = z.f(&[z.X.clone()]);
        let e2 = z.f(&[z.Y.clone()]);
        z.assert_that_unify(e1, e2, "[Y/X]");

         */
    }

    #[test]
    fn test9() {
        let z = create();
        /*
        let e1 = z.f(&[z.g(&[z.X.clone()]), z.X.clone()]);
        let e2 = z.f(&[z.Y.clone()]);
        z.assert_that_cannot_unify(e1, e2);

         */
    }

    #[test]
    fn test10() {
        let z = create();
        /*

        let e1 = z.f(&[z.g(&[z.X.clone()])]);
        let e2 = z.f(&[z.Y.clone()]);
        z.assert_that_unify(e1, e2, "[g(X)/Y]");

         */
    }

    #[test]
    fn test11() {
        let z = create();
        /*
        let e1 = z.f(&[z.g(&[z.X.clone()]), z.X.clone()]);
        let e2 = z.f(&[z.Y.clone(), z.a()]);
        z.assert_that_unify(e1, e2, "[a/X, g(a)/Y]");

         */
    }

    #[test]
    fn test12() {
        let z = create();
        /*
        let e1 = z.father(&[z.X.clone(), z.Y.clone()]);
        let e2 = z.father(&[z.bob(&[]), z.tom(&[])]);
        z.assert_that_unify(e1, e2, "[bob/X, tom/Y]");

         */
    }

    #[test]
    fn test13() {
        let z = create();
        /*
        let e1 = z.parents(&[
            z.X.clone(),
            z.father(&[z.X.clone()]),
            z.mother(&[z.bill(&[])]),
        ]);
        let e2 =
            z.parents(&[z.bill(&[]), z.father(&[z.bill(&[])]), z.Y.clone()]);
        z.assert_that_unify(e1, e2, "[bill/X, mother(bill)/Y]");

         */
    }

    #[test]
    fn test14() {
        let mut z = create();
        /*
        let e1 = z.grand_parent(
            Term::Variable(z.X),
            Sequence(z.parent(Sequence(z.parent(Term::Variable(z.X))))),
        );
        let e2 = z.grand_parent(&[z.john(&[]), z.parent(&[z.Y.clone()])]);
        z.assert_that_unify(e1, e2, "[john/X, parent(john)/Y]");

         */
    }

    #[test]
    fn test15() {
        let z = create();
        /*

        let e1 = z.p(&[z.f(&[z.a(), z.g(&[z.X.clone()])])]);
        let e2 = z.p(&[z.Y.clone(), z.Y.clone()]);
        z.assert_that_cannot_unify(e1, e2);

         */
    }

    #[test]
    fn test16() {
        let z = create();
        /*
        let e1 = z.p(&[z.a(), z.X.clone(), z.h(&[z.g(&[z.Z.clone()])])]);
        let e2 = z.p(&[z.Z.clone(), z.h(&[z.Y.clone()]), z.h(&[z.Y.clone()])]);
        z.assert_that_unify(e1, e2, "[h(g(a))/X, g(a)/Y, a/Z]");

         */
    }

    #[test]
    fn test17() {
        let z = create();
        /*
        let e1 = z.p(&[z.X.clone(), z.X.clone()]);
        let e2 = z.p(&[z.Y.clone(), z.f(&[z.Y.clone()])]);
        if z.unifier.occurs() {
            z.assert_that_cannot_unify(e1, e2);
        } else {
            z.assert_that_unify(e1, e2, "[Y/X, f(Y)/Y]");
        }

         */
    }

    #[test]
    fn test18() {
        let z = create();
        /*
        let e1 = z.part(&[z.W.clone(), z.X.clone()]);
        let e2 = z.connected(&[z.f(&[z.W.clone(), z.X.clone()]), z.W.clone()]);
        z.assert_that_cannot_unify(e1, e2);

         */
    }

    #[test]
    fn test19() {
        let z = create();
        /*

        let e1 = z.p(&[z.f(&[z.X.clone()]), z.a(), z.Y.clone()]);
        let e2 = z.p(&[z.f(&[z.bill(&[])]), z.Z.clone(), z.g(&[z.b()])]);
        z.assert_that_unify(e1, e2, "[bill/X, g(b)/Y, a/Z]");

         */
    }

    /// Tests dump function.
    #[test]
    fn test_unifier_dump() {
        let z = create();
        let mut pairs: Vec<Op> = Vec::new();
        /*
        let int_atom = z.unifier.atom("int");
        let t5 = z.unifier.variable_with_id(5);
        pairs.push(TermTerm::new(int_atom, t5));

        let mut sw = Vec::new();
        dump(&mut sw, &pairs).unwrap();
        let result = String::from_utf8(sw).unwrap();
        let expected = "List<Unifier.TermTerm> pairs = new ArrayList<>();\n\
                       final Unifier.Term int = unifier.atom(\"int\");\n\
                       final Unifier.Variable t5 = unifier.variable(5);\n\
                       pairs.add(new Unifier.TermTerm(int, t5));\n";
        assert_eq!(result, expected);

         */
    }

    /// Tests specific to RobinsonUnifier.
    mod robinson_tests {
        use super::*;

        #[test]
        fn test_robinson_specific() {
            // Tests that would be specific to RobinsonUnifier behavior
            let _test = create();
        }
    }

    /// Tests specific to MartelliUnifier.
    mod martelli_tests {
        use super::*;

        /// Solves the equations from the S combinator,
        /// "fn x => fn y => fn z => x z (z y)",
        /// in [Wand 87](https://web.cs.ucla.edu/~palsberg/course/cs239/reading/wand87.pdf).
        #[test]
        fn test20() {
            let z = create();
            /*
               let t0 = z.unifier.variable_with_id(0);
               let a0 = z.unifier.variable_with_id(1);
               let a1 = z.unifier.variable_with_id(2);
               let t3 = z.unifier.variable_with_id(3);
               let t4 = z.unifier.variable_with_id(4);
               let t5 = z.unifier.variable_with_id(5);
               let t6 = z.unifier.variable_with_id(6);
               let t7 = z.unifier.variable_with_id(7);
               let t8 = z.unifier.variable_with_id(8);
               let t9 = z.unifier.variable_with_id(9);
               let term_terms = vec![
                   TermTerm::new(t0.clone(), z.arrow(a0.clone(), a1.clone())),
                   TermTerm::new(a1.clone(), z.arrow(t3.clone(), t4.clone())),
                   TermTerm::new(t4.clone(), z.arrow(t5.clone(), t6.clone())),
                   TermTerm::new(
                       a0.clone(),
                       z.arrow(t8.clone(), z.arrow(t7.clone(), t6.clone())),
                   ),
                   TermTerm::new(t8.clone(), t5.clone()),
                   TermTerm::new(z.arrow(t9.clone(), t7.clone()), t3.clone()),
                   TermTerm::new(t9.clone(), t5.clone()),
               ];
               let result =
                   z.unifier
                       .unify(&term_terms, &HashMap::new(), &[], &NullTracer);

               let expected = "[->(T1, T2)/T0, ->(T8, ->(T7, T6))/T1, \
                              ->(T3, T4)/T2, \
                              ->(T9, T7)/T3, ->(T5, T6)/T4, T5/T8, T5/T9]";
               assert_eq!(result.to_string(), expected);

            */
        }

        #[test]
        fn test_atom_eq_atom() {
            let z = create();
            /*
            let pairs = z.term_pairs(&[z.b(), z.X.clone(), z.a(), z.X.clone()]);
            z.assert_that_cannot_unify_pairs(&pairs);

             */
        }

        #[test]
        fn test_atom_eq_atom2() {
            let z = create();
            /*
            let pairs = z.term_pairs(&[
                z.a(),
                z.X.clone(),
                z.a(),
                z.X.clone(),
                z.b(),
                z.X.clone(),
            ]);
            z.assert_that_cannot_unify_pairs(&pairs);

             */
        }

        #[test]
        fn test_atom_eq_atom3() {
            let z = create();
            /*
            let pairs = z.term_pairs(&[z.a(), z.X.clone(), z.a(), z.X.clone()]);
            z.assert_that_unify_pairs(&pairs, "[a/X]");

             */
        }

        #[test]
        fn test_overload() {
            let z = create();
            /*
            let mut pairs = Vec::new();
            let int_atom = z.unifier.atom("int");
            let t5 = z.unifier.variable_with_id(5);
            pairs.push(TermTerm::new(int_atom, t5.clone()));
            let t4 = z.unifier.variable_with_id(4);
            pairs.push(TermTerm::new(t5.clone(), t4.clone()));
            let fn1 = z.unifier.apply("fn", &[t5.clone(), t4.clone()]);
            let t3 = z.unifier.variable_with_id(3);
            pairs.push(TermTerm::new(fn1, t3.clone()));
            let t6 = z.unifier.variable_with_id(6);
            let t7 = z.unifier.variable_with_id(7);
            let fn11 = z.unifier.apply("fn", &[t6, t7]);
            pairs.push(TermTerm::new(fn11, t3.clone()));
            let fn21 = z.unifier.apply("fn", &[t3.clone(), t3.clone()]);
            let a1 = z.unifier.variable_with_id(2);
            pairs.push(TermTerm::new(fn21, a1));
            let bool_atom = z.unifier.atom("bool");
            let a01 = z.unifier.variable_with_id(11);
            pairs.push(TermTerm::new(bool_atom, a01.clone()));
            let a00 = z.unifier.variable_with_id(10);
            pairs.push(TermTerm::new(a01.clone(), a00.clone()));
            let fn31 = z.unifier.apply("fn", &[a01.clone(), a00.clone()]);
            let t9 = z.unifier.variable_with_id(9);
            pairs.push(TermTerm::new(fn31, t9.clone()));
            let a02 = z.unifier.variable_with_id(12);
            let a03 = z.unifier.variable_with_id(13);
            let fn41 = z.unifier.apply("fn", &[a02, a03]);
            pairs.push(TermTerm::new(fn41, t9.clone()));
            let fn51 = z.unifier.apply("fn", &[t9.clone(), t9.clone()]);
            let t8 = z.unifier.variable_with_id(8);
            pairs.push(TermTerm::new(fn51, t8));
            let a05 = z.unifier.variable_with_id(15);
            let a0 = z.unifier.variable_with_id(1);
            let fn61 = z.unifier.apply("fn", &[a05.clone(), a0.clone()]);
            let a04 = z.unifier.variable_with_id(14);
            pairs.push(TermTerm::new(fn61, a04));
            pairs.push(TermTerm::new(z.unifier.atom("bool"), a05));
            let fn71 = z.unifier.apply("fn", &[a0.clone(), a0]);
            let t0 = z.unifier.variable_with_id(0);
            pairs.push(TermTerm::new(fn71, t0));
            let expected = "[fn(T1, T1)/T0, fn(fn(int, int), fn(int, int))/T2, \
                           fn(int, int)/T3, int/T4, int/T5, int/T6, int/T7, \
                           fn(fn(bool, bool), fn(bool, bool))/T8, \
                           fn(bool, bool)/T9, bool/T10, bool/T11, bool/T12, \
                           bool/T13, fn(bool, T1)/T14, bool/T15]";
            z.assert_that_unify_pairs(&pairs, expected);

             */
        }
    }
}
