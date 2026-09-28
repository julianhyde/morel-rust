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

//! Checks that a relational tree is well-formed.
//!
//! The invariants are `spec.md` §5 on morel-java's `julianhyde/449-tree`
//! branch, and they are the contract a rewrite must preserve. Running
//! this after every rewrite turns a wrong tree into a named error
//! instead of a wrong plan, which is the difference between a failure
//! that says where it is and one that does not.

// Nothing builds a relational tree yet -- the translator is milestone
// R5 of plan.md -- so nothing outside the tests calls this. Remove when
// R5 lands.
#![allow(dead_code)]

use crate::compile::core::{Expr, Rel, element_type};
use crate::compile::free_finder::free_names_in;
use crate::compile::types::{Label, PrimitiveType, Type};
use std::collections::BTreeSet;
use std::rc::Rc;

/// Returns what is wrong with the tree rooted at `exp`, or an empty
/// vector if nothing is.
pub fn validate(exp: &Expr) -> Vec<String> {
    validate_eliminating(exp, &BTreeSet::new())
}

/// Validates as [`validate`] does, and also that the tree reads none
/// of `leaked`, the binders a step's rewrite failed to substitute out.
///
/// Eliminating those names is what a translation *is*: a step list
/// carries its binders in an environment, and a tree has no
/// environment, so a binder becomes an expression over `$0` or it
/// becomes nothing. One left behind is not a plan that reads
/// differently -- it is a plan naming something nothing defines, and
/// it will evaluate to whatever an outer binding of the same name
/// happens to hold.
///
/// The set comes from the translator because scope decides it and the
/// finished tree has none. `from i in [1, 2] yield {h = h}` reads an
/// outer `h` and binds a field called `h`, and the two are the same
/// text in the tree; only the step that rewrote the expression knows
/// which was in scope when.
pub fn validate_eliminating(
    exp: &Expr,
    leaked: &BTreeSet<String>,
) -> Vec<String> {
    let mut errors = Vec::new();
    let mut binders = BTreeSet::new();
    walk(exp, &mut binders, &mut errors);
    for name in free_names_in(exp).intersection(leaked) {
        errors.push(format!(
            "'{}' is read by the tree, and the query bound it: a binder \
             the translation did not eliminate",
            name
        ));
    }
    errors
}

/// Returns what a rewrite broke: invariant 5, that a rewrite preserves
/// the type of the tree's root, in both element type and kind. It is
/// the cheap check that catches most rule bugs, including every rule
/// that forgets a projection.
pub fn validate_rewrite(before: &Expr, after: &Expr) -> Vec<String> {
    let mut errors = validate(after);
    if before.type_() != after.type_() {
        errors.push(format!(
            "rewrite changed the root type, from '{}' to '{}'",
            before.type_(),
            after.type_()
        ));
    }
    errors
}

/// Validates every node reachable from `exp`.
///
/// Descends through the expression shapes a node's arguments are built
/// from. A step list is the representation a tree replaces, so a tree
/// inside one is not something we build, and this does not look there.
fn walk(exp: &Expr, binders: &mut BTreeSet<String>, errors: &mut Vec<String>) {
    match exp {
        Expr::Rel(t, rel) => {
            check_node(t, rel, binders, errors);
            // The inputs are nodes or leaves in their own right. A
            // join's binder is in scope in its right input; `check_node`
            // walks that side itself.
            if !matches!(rel.as_ref(), Rel::Join(_, _, _, _, _)) {
                for child in rel.children() {
                    walk(child, binders, errors);
                }
            }
        }
        Expr::Aggregate(_, a, b, _) | Expr::Apply(_, a, b, _) => {
            walk(a, binders, errors);
            walk(b, binders, errors);
        }
        Expr::Raise(_, a, _) => walk(a, binders, errors),
        Expr::List(_, items) | Expr::Tuple(_, items) => {
            for item in items {
                walk(item, binders, errors);
            }
        }
        Expr::Case(_, a, arms, _) => {
            walk(a, binders, errors);
            for arm in arms {
                walk(&arm.expr, binders, errors);
            }
        }
        Expr::Fn(_, arms, _) => {
            for arm in arms {
                walk(&arm.expr, binders, errors);
            }
        }
        Expr::Let(_, _, body) => walk(body, binders, errors),
        _ => {}
    }
}

/// Checks one node: invariants 1 to 4.
fn check_node(
    t: &Rc<Type>,
    rel: &Rel,
    binders: &mut BTreeSet<String>,
    errors: &mut Vec<String>,
) {
    let op = rel.op_name();

    // Invariants 1 and 2: the node's type is the one the constructor
    // derives, in both element type and kind.
    match rel.derive_type() {
        None => errors.push(format!("{}: an input is not a collection", op)),
        Some(derived) if derived != *t => errors.push(format!(
            "{}: type is '{}' but the node derives '{}'",
            op, t, derived
        )),
        Some(_) => {}
    }

    // Invariant 1, continued: the types an argument must have.
    match rel {
        Rel::Filter(_, condition) => {
            check_primitive(
                op,
                "condition",
                condition,
                PrimitiveType::Bool,
                errors,
            );
        }
        Rel::Join(_, _, condition, _, _) => {
            check_primitive(
                op,
                "condition",
                condition,
                PrimitiveType::Bool,
                errors,
            );
        }
        Rel::Skip(_, n) | Rel::Take(_, n) => {
            check_primitive(op, "count", n, PrimitiveType::Int, errors);
        }
        Rel::Except(_, inputs)
        | Rel::Intersect(_, inputs)
        | Rel::Union(_, inputs) => {
            if inputs.len() < 2 {
                errors.push(format!(
                    "{}: has {} inputs, and needs at least two",
                    op,
                    inputs.len()
                ));
            }
            let mut elements =
                inputs.iter().filter_map(|i| element_type(&i.type_()));
            if let Some(first) = elements.next()
                && let Some(other) = elements.find(|e| *e != first)
            {
                errors.push(format!(
                    "{}: inputs have element types '{}' and '{}', which differ",
                    op, first, other
                ));
            }
        }
        _ => {}
    }

    // Invariant 4: within one node, output labels are distinct. A join
    // has no labels; its components are positional.
    if let Rel::Group(_, keys, aggregates) = rel {
        let mut seen: BTreeSet<&Label> = BTreeSet::new();
        for (label, _) in keys.iter().chain(aggregates.iter()) {
            if !seen.insert(label) {
                errors.push(format!("{}: label '{}' occurs twice", op, label));
            }
        }
    }

    // Invariant 3: scope.
    check_scope(rel, binders, errors);
}

/// Invariant 3. An expression may read `$0`, the element of its node's
/// input, and `$1` in a join; a count is evaluated before the first row
/// and may read neither. A join's binder is in scope in its right input
/// and nowhere else.
fn check_scope(
    rel: &Rel,
    binders: &mut BTreeSet<String>,
    errors: &mut Vec<String>,
) {
    let op = rel.op_name();
    match rel {
        // A count is evaluated once, before any element exists.
        Rel::Skip(_, n) | Rel::Take(_, n) => {
            check_inputs(op, "count", n, &[], errors);
        }
        Rel::Filter(input, e)
        | Rel::Project(input, e)
        | Rel::Sort(input, e) => {
            check_inputs(op, "expression", e, &one(input), errors);
        }
        Rel::Group(input, keys, aggregates) => {
            let allowed = one(input);
            for (_, e) in keys.iter().chain(aggregates.iter()) {
                check_inputs(op, "expression", e, &allowed, errors);
            }
        }
        Rel::Join(kind, binder, condition, left, right) => {
            // The condition sees both elements, whatever the kind.
            let mut allowed = one(left);
            allowed.extend(one(right));
            check_inputs(op, "condition", condition, &allowed, errors);
            if let Some(name) = binder {
                if free_names_in(condition).contains(name) {
                    errors.push(format!(
                        "join: binder '{}' is read by the condition, where \
                         it is not in scope",
                        name
                    ));
                }
                if free_names_in(left).contains(name) {
                    errors.push(format!(
                        "join: binder '{}' is read by the left input, where \
                         it is not in scope",
                        name
                    ));
                }
                // spec.md §5 leaves the rename convention at a scope
                // merge open, and says the validator rejects the
                // collision meanwhile, so that the contract is that it
                // cannot arise.
                if !binders.insert(name.clone()) {
                    errors.push(format!(
                        "join: binder '{}' is already bound by an enclosing \
                         join",
                        name
                    ));
                }
            }
            walk(left, binders, errors);
            walk(right, binders, errors);
            if let Some(name) = binder {
                binders.remove(name);
            }
            let _ = kind;
        }
        Rel::Unorder(_) => {}
        Rel::Except(_, _) | Rel::Intersect(_, _) | Rel::Union(_, _) => {}
    }
}

/// Returns the element type of `input`, or nothing if it is not a
/// collection -- which `check_node` has already reported.
fn one(input: &Expr) -> Vec<Rc<Type>> {
    element_type(&input.type_()).into_iter().collect()
}

/// Reports an input reference that names an input the expression cannot
/// see -- `$1` outside a join, or any `$i` in a count -- or that reads
/// one as a type that is not its element's.
///
/// Stops at a nested node, which rebinds `$0` to its own input
/// (spec.md §2 rule 3); to read the enclosing element inside one, a
/// query binds it to a name first.
fn check_inputs(
    op: &str,
    what: &str,
    exp: &Expr,
    allowed: &[Rc<Type>],
    errors: &mut Vec<String>,
) {
    match exp {
        Expr::Input(t, i) => match allowed.get(*i) {
            None => errors.push(format!(
                "{}: {} reads ${}, which is not in scope",
                op, what, i
            )),
            Some(elem) if elem != t => errors.push(format!(
                "{}: {} reads ${} as '{}', and it is '{}'",
                op, what, i, t, elem
            )),
            Some(_) => {}
        },
        Expr::Rel(_, _) => {}
        Expr::Aggregate(_, a, b, _) | Expr::Apply(_, a, b, _) => {
            check_inputs(op, what, a, allowed, errors);
            check_inputs(op, what, b, allowed, errors);
        }
        Expr::Raise(_, a, _) => check_inputs(op, what, a, allowed, errors),
        Expr::List(_, items) | Expr::Tuple(_, items) => {
            for item in items {
                check_inputs(op, what, item, allowed, errors);
            }
        }
        Expr::Case(_, a, arms, _) => {
            check_inputs(op, what, a, allowed, errors);
            for arm in arms {
                check_inputs(op, what, &arm.expr, allowed, errors);
            }
        }
        Expr::Fn(_, arms, _) => {
            for arm in arms {
                check_inputs(op, what, &arm.expr, allowed, errors);
            }
        }
        Expr::Let(_, _, body) => check_inputs(op, what, body, allowed, errors),
        _ => {}
    }
}

/// Reports an argument whose type is not the primitive it must be.
fn check_primitive(
    op: &str,
    what: &str,
    exp: &Expr,
    expected: PrimitiveType,
    errors: &mut Vec<String>,
) {
    let want = Type::Primitive(expected);
    if *exp.type_() != want {
        errors.push(format!(
            "{}: {} has type '{}' and must be '{}'",
            op,
            what,
            exp.type_(),
            want
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::core::{JoinKind, Kind};
    use crate::compile::span::Span;
    use crate::eval::val::Val;

    fn int() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Int))
    }

    fn string() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::String))
    }

    fn bool_() -> Rc<Type> {
        Rc::new(Type::Primitive(PrimitiveType::Bool))
    }

    fn leaf(elem: Rc<Type>, kind: Kind) -> Expr {
        Expr::Identifier(kind.apply(elem), "r".to_string())
    }

    fn t() -> Expr {
        Expr::Literal(bool_(), Val::Bool(true))
    }

    /// Builds a node with the type it derives, so that the type is
    /// right unless a test makes it wrong on purpose.
    fn node(rel: Rel) -> Expr {
        let t = rel.derive_type().expect("derives a type");
        Expr::Rel(t, Box::new(rel))
    }

    #[test]
    fn a_well_formed_tree_has_nothing_wrong_with_it() {
        let tree = node(Rel::Project(
            Box::new(node(Rel::Filter(
                Box::new(leaf(int(), Kind::List)),
                Box::new(t()),
            ))),
            Box::new(Expr::Input(int(), 0)),
        ));
        assert_eq!(validate(&tree), Vec::<String>::new());
    }

    /// Invariants 1 and 2: a node's type is the one its constructor
    /// derives, in both element type and kind.
    #[test]
    fn node_type_is_the_derived_one() {
        let filter =
            Rel::Filter(Box::new(leaf(int(), Kind::List)), Box::new(t()));
        // The element type is wrong.
        let wrong_element =
            Expr::Rel(Kind::List.apply(string()), Box::new(filter.clone()));
        assert_eq!(
            validate(&wrong_element),
            ["filter: type is 'string list' but the node derives 'int list'"]
        );
        // The kind is wrong: a filter passes its input's kind through.
        let wrong_kind = Expr::Rel(Kind::Bag.apply(int()), Box::new(filter));
        assert_eq!(
            validate(&wrong_kind),
            ["filter: type is 'int bag' but the node derives 'int list'"]
        );
    }

    /// Invariant 1: the types an argument must have.
    #[test]
    fn argument_types() {
        let input = leaf(int(), Kind::List);
        let not_bool = Expr::Literal(int(), Val::Int(1));
        let filter =
            node(Rel::Filter(Box::new(input.clone()), Box::new(not_bool)));
        assert_eq!(
            validate(&filter),
            ["filter: condition has type 'int' and must be 'bool'"]
        );

        let not_int = Expr::Literal(string(), Val::String("2".into()));
        let take = node(Rel::Take(Box::new(input.clone()), Box::new(not_int)));
        assert_eq!(
            validate(&take),
            ["take: count has type 'string' and must be 'int'"]
        );

        // A set operator's inputs must agree on their element type.
        let union = node(Rel::Union(
            false,
            vec![input.clone(), leaf(string(), Kind::List)],
        ));
        assert_eq!(
            validate(&union),
            [
                "union: inputs have element types 'int' and 'string', which \
              differ"
            ]
        );
    }

    /// Invariant 3: a count is evaluated before the first row, so it
    /// can read no element.
    #[test]
    fn a_count_reads_no_element() {
        let skip = node(Rel::Skip(
            Box::new(leaf(int(), Kind::List)),
            Box::new(Expr::Input(int(), 0)),
        ));
        assert_eq!(
            validate(&skip),
            ["skip: count reads $0, which is not in \
                                      scope"]
        );
    }

    /// Invariant 3: `$1` is a join's right element, and there is no
    /// second input anywhere else.
    #[test]
    fn only_a_join_has_a_second_input() {
        let filter = node(Rel::Filter(
            Box::new(leaf(int(), Kind::List)),
            Box::new(Expr::Input(bool_(), 1)),
        ));
        assert_eq!(
            validate(&filter),
            ["filter: expression reads $1, which is not in scope"]
        );

        // In a join it is in scope, and nothing is wrong.
        let join = node(Rel::Join(
            JoinKind::Inner,
            None,
            Box::new(t()),
            Box::new(leaf(int(), Kind::List)),
            Box::new(leaf(string(), Kind::List)),
        ));
        assert_eq!(validate(&join), Vec::<String>::new());
    }

    /// Invariant 3: a join's binder is in scope in its right input and
    /// nowhere else.
    #[test]
    fn a_binder_is_in_scope_in_the_right_input_only() {
        let reads = |name: &str| Expr::Identifier(bool_(), name.to_string());
        let condition_reads_binder = node(Rel::Join(
            JoinKind::Inner,
            Some("v".to_string()),
            Box::new(reads("v")),
            Box::new(leaf(int(), Kind::List)),
            Box::new(leaf(string(), Kind::List)),
        ));
        assert_eq!(
            validate(&condition_reads_binder),
            [
                "join: binder 'v' is read by the condition, where it is not in \
              scope"
            ]
        );

        // Read by the right input, it is in scope.
        let right_reads_binder = node(Rel::Join(
            JoinKind::Inner,
            Some("v".to_string()),
            Box::new(t()),
            Box::new(leaf(int(), Kind::List)),
            Box::new(Expr::Identifier(
                Kind::List.apply(string()),
                "v".to_string(),
            )),
        ));
        assert_eq!(validate(&right_reads_binder), Vec::<String>::new());
    }

    /// The item spec.md §5 leaves open: until a rename convention is
    /// written, a collision is rejected, so the contract is that it
    /// cannot arise.
    #[test]
    fn a_binder_may_not_shadow_an_enclosing_one() {
        let inner = node(Rel::Join(
            JoinKind::Inner,
            Some("v".to_string()),
            Box::new(t()),
            Box::new(leaf(int(), Kind::List)),
            Box::new(leaf(string(), Kind::List)),
        ));
        let outer = node(Rel::Join(
            JoinKind::Inner,
            Some("v".to_string()),
            Box::new(t()),
            Box::new(leaf(bool_(), Kind::List)),
            Box::new(inner),
        ));
        assert_eq!(
            validate(&outer),
            ["join: binder 'v' is already bound by an enclosing join"]
        );
    }

    /// Invariant 1: an input reference is the input's element, so
    /// reading it as another type is ill-formed. Writing a test that
    /// got this wrong is what suggested the check.
    #[test]
    fn an_input_reference_has_its_element_type() {
        let filter = node(Rel::Filter(
            Box::new(leaf(bool_(), Kind::List)),
            // `$0` is a bool here, whatever this says.
            Box::new(Expr::Input(int(), 0)),
        ));
        assert_eq!(
            validate(&filter),
            [
                "filter: condition has type 'int' and must be 'bool'",
                "filter: expression reads $0 as 'int', and it is 'bool'"
            ]
        );
    }

    /// Invariant 4: within one node, output labels are distinct.
    #[test]
    fn labels_are_distinct_within_a_node() {
        let group = node(Rel::Group(
            Box::new(leaf(int(), Kind::Bag)),
            vec![(Label::String("a".to_string()), Expr::Input(int(), 0))],
            vec![(
                Label::String("a".to_string()),
                Expr::Identifier(int(), "n".to_string()),
            )],
        ));
        assert_eq!(validate(&group), ["group: label 'a' occurs twice"]);
    }

    /// Invariant 5: a rewrite preserves the root's type, which is the
    /// cheap check that catches a rule that forgets a projection.
    #[test]
    fn a_rewrite_preserves_the_root_type() {
        let before = node(Rel::Project(
            Box::new(leaf(int(), Kind::List)),
            Box::new(Expr::Identifier(string(), "s".to_string())),
        ));
        // Dropping the projection changes the element type.
        let after = leaf(int(), Kind::List);
        assert_eq!(
            validate_rewrite(&before, &after),
            ["rewrite changed the root type, from 'string list' to 'int list'"]
        );
        assert_eq!(
            validate_rewrite(&before, &before.clone()),
            Vec::<String>::new()
        );
    }

    /// A nested tree rebinds `$0` to its own input, so an occurrence
    /// inside one is not an occurrence in the node that holds it.
    #[test]
    fn a_nested_tree_rebinds_its_input() {
        let nested = node(Rel::Filter(
            Box::new(leaf(bool_(), Kind::List)),
            Box::new(Expr::Input(bool_(), 0)),
        ));
        // The nested tree sits in a count, which may read no element of
        // its own -- and does not, because the `$0` inside it is the
        // nested tree's.
        let skip = node(Rel::Skip(
            Box::new(leaf(int(), Kind::List)),
            Box::new(Expr::Apply(
                int(),
                Box::new(Expr::Identifier(int(), "size".to_string())),
                Box::new(nested),
                Span::new(""),
            )),
        ));
        assert_eq!(validate(&skip), Vec::<String>::new());
    }
}
