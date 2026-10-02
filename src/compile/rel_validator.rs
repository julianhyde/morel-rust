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

use crate::compile::core::{
    Decl, Expr, ORDINAL, RIGHT_ROW, ROW, Rel, Row, element_type,
};
use crate::compile::free_finder::free_names_in;
use crate::compile::rel_lowerer;
use crate::compile::types::{Label, PrimitiveType, Type};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
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
    let mut rows = BTreeSet::from([
        ROW.to_string(),
        RIGHT_ROW.to_string(),
        ORDINAL.to_string(),
    ]);
    rows_of(exp, &mut rows);
    let mut scope = Scope {
        visible: BTreeMap::new(),
        rows,
    };
    walk(exp, &mut scope, "tree", &mut errors);
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

/// The rows in scope at a point in a tree, with their types; and every
/// row any node of the tree binds, which an expression may read only
/// where it is in scope.
struct Scope {
    visible: BTreeMap<String, Rc<Type>>,
    rows: BTreeSet<String>,
}

/// Validates every node reachable from `exp`, and that every row an
/// expression reads is in scope there.
///
/// Descends through the expression shapes a node's arguments are built
/// from. A step list is the representation a tree replaces, so a tree
/// inside one is not something we build, and this does not look there.
fn walk(exp: &Expr, scope: &mut Scope, what: &str, errors: &mut Vec<String>) {
    match exp {
        Expr::Identifier(t, name) if scope.rows.contains(name) => {
            match scope.visible.get(name) {
                None => errors.push(format!(
                    "{} reads '{}', which is not in scope",
                    what, name
                )),
                Some(elem) if elem != t => errors.push(format!(
                    "{} reads '{}' as '{}', and it is '{}'",
                    what, name, t, elem
                )),
                Some(_) => {}
            }
        }
        Expr::Rel(t, rel) => {
            check_node(t, rel, errors);
            check_scope(rel, scope, errors);
        }
        Expr::Aggregate(_, a, b, _) | Expr::Apply(_, a, b, _) => {
            walk(a, scope, what, errors);
            walk(b, scope, what, errors);
        }
        Expr::Raise(_, a, _) => walk(a, scope, what, errors),
        Expr::List(_, items) | Expr::Tuple(_, items) => {
            for item in items {
                walk(item, scope, what, errors);
            }
        }
        Expr::Case(_, a, arms, _) => {
            walk(a, scope, what, errors);
            for arm in arms {
                walk(&arm.expr, scope, what, errors);
            }
        }
        Expr::Fn(_, arms, _) => {
            for arm in arms {
                walk(&arm.expr, scope, what, errors);
            }
        }
        Expr::Let(_, decls, body) => {
            for decl in decls {
                if let Decl::NonRecVal(b) = decl {
                    walk(&b.expr, scope, what, errors);
                }
            }
            walk(body, scope, what, errors)
        }
        _ => {}
    }
}

/// Checks one node: invariants 1, 2 and 4.
fn check_node(t: &Rc<Type>, rel: &Rel, errors: &mut Vec<String>) {
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
        Rel::Filter(_, _, condition) => {
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
    if let Rel::Group(_, _, keys, aggregates) = rel {
        let mut seen: BTreeSet<&Label> = BTreeSet::new();
        for (label, _) in keys.iter().chain(aggregates.iter()) {
            if !seen.insert(label) {
                errors.push(format!("{}: label '{}' occurs twice", op, label));
            }
        }
    }
}

/// Invariant 3. A node's row is in scope in its own expressions and
/// nowhere else, except that a join's left row is in scope in its right
/// input too; a count is evaluated before the first row and reads none
/// of its node's. A row is a name of its own, so a node may not bind
/// one that is in scope already, nor leave one a placeholder.
fn check_scope(rel: &Rel, scope: &mut Scope, errors: &mut Vec<String>) {
    let op = rel.op_name();
    let what = |part: &str| format!("{}: {}", op, part);
    match rel {
        Rel::Skip(input, n) | Rel::Take(input, n) => {
            walk(input, scope, &what("input"), errors);
            walk(n, scope, &what("count"), errors);
        }
        Rel::Filter(row, input, e)
        | Rel::Project(row, input, e)
        | Rel::Sort(row, input, e) => {
            walk(input, scope, &what("input"), errors);
            let saved = bind_row(op, row, input, scope, errors);
            walk(e, scope, &what("expression"), errors);
            scope.visible = saved;
        }
        Rel::Group(row, input, keys, aggregates) => {
            walk(input, scope, &what("input"), errors);
            let saved = bind_row(op, row, input, scope, errors);
            for (_, e) in keys.iter().chain(aggregates.iter()) {
                walk(e, scope, &what("expression"), errors);
            }
            scope.visible = saved;
        }
        Rel::Join(_, rows, condition, left, right) => {
            walk(left, scope, &what("left input"), errors);
            let saved = bind(op, &rows.left, &left.type_(), scope, errors);
            if let Some(ordinal) = &rows.ordinal {
                let int =
                    Type::List(Rc::new(Type::Primitive(PrimitiveType::Int)));
                bind(op, ordinal, &int, scope, errors);
            }
            walk(right, scope, &what("right input"), errors);
            bind(op, &rows.right, &right.type_(), scope, errors);
            walk(condition, scope, &what("condition"), errors);
            scope.visible = saved;
        }
        Rel::Unorder(input) => walk(input, scope, &what("input"), errors),
        Rel::Except(_, inputs)
        | Rel::Intersect(_, inputs)
        | Rel::Union(_, inputs) => {
            for input in inputs {
                walk(input, scope, &what("input"), errors);
            }
        }
    }
}

/// Brings a one-input node's row, and its position where it counts
/// its rows, into scope, and returns the scope as it was before.
fn bind_row(
    op: &str,
    row: &Row,
    input: &Expr,
    scope: &mut Scope,
    errors: &mut Vec<String>,
) -> BTreeMap<String, Rc<Type>> {
    let saved = bind(op, &row.name, input.type_().as_ref(), scope, errors);
    if let Some(ordinal) = &row.ordinal {
        let int = Type::List(Rc::new(Type::Primitive(PrimitiveType::Int)));
        bind(op, ordinal, &int, scope, errors);
    }
    saved
}

/// Brings a name into scope, as the element of a collection of type
/// `collection`, and returns the scope as it was before.
fn bind(
    op: &str,
    name: &str,
    collection: &Type,
    scope: &mut Scope,
    errors: &mut Vec<String>,
) -> BTreeMap<String, Rc<Type>> {
    let saved = scope.visible.clone();
    if name == ROW || name == RIGHT_ROW || name == ORDINAL {
        errors.push(format!("{}: row '{}' is a placeholder", op, name));
    }
    if scope.visible.contains_key(name) {
        errors.push(format!(
            "{}: row '{}' is already bound by an enclosing node",
            op, name
        ));
    }
    if let Some(elem) = element_type(collection) {
        scope.visible.insert(name.to_string(), elem);
    }
    saved
}

/// Returns every row that a node of the tree binds, and the
/// placeholders, which no node of a finished tree binds.
fn rows_of(exp: &Expr, rows: &mut BTreeSet<String>) {
    if let Expr::Rel(_, rel) = exp {
        match rel.as_ref() {
            Rel::Filter(row, _, _)
            | Rel::Group(row, _, _, _)
            | Rel::Project(row, _, _)
            | Rel::Sort(row, _, _) => {
                rows.insert(row.name.clone());
                rows.extend(row.ordinal.clone());
            }
            Rel::Join(_, join_rows, _, _, _) => {
                rows.insert(join_rows.left.clone());
                rows.insert(join_rows.right.clone());
                rows.extend(join_rows.ordinal.clone());
            }
            _ => {}
        }
    }
    let children = RefCell::new(Vec::new());
    let collect = |c: &Expr| {
        children.borrow_mut().push(c.clone());
        c.clone()
    };
    match exp {
        Expr::Rel(_, rel) => {
            rel.map_children(&collect);
        }
        _ => {
            rel_lowerer::map_children(exp, &collect);
        }
    }
    for c in children.into_inner() {
        rows_of(&c, rows);
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
    use crate::compile::core::{JoinKind, JoinRows, Kind, Row};
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
        let rel = rel.bind();
        let t = rel.derive_type().expect("derives a type");
        Expr::Rel(t, Box::new(rel))
    }

    /// The element a node is being built over, `$0`.
    fn row(t: Rc<Type>) -> Expr {
        Expr::Identifier(t, ROW.to_string())
    }

    #[test]
    fn a_well_formed_tree_has_nothing_wrong_with_it() {
        let tree = node(Rel::Project(
            Row::placeholder(),
            Box::new(node(Rel::Filter(
                Row::placeholder(),
                Box::new(leaf(int(), Kind::List)),
                Box::new(t()),
            ))),
            Box::new(row(int())),
        ));
        assert_eq!(validate(&tree), Vec::<String>::new());
    }

    /// Invariants 1 and 2: a node's type is the one its constructor
    /// derives, in both element type and kind.
    #[test]
    fn node_type_is_the_derived_one() {
        let filter = Rel::Filter(
            Row::placeholder(),
            Box::new(leaf(int(), Kind::List)),
            Box::new(t()),
        )
        .bind();
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
        let filter = node(Rel::Filter(
            Row::placeholder(),
            Box::new(input.clone()),
            Box::new(not_bool),
        ));
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
    /// can read no row; and no node binds a placeholder, so nothing in a
    /// finished tree may read one.
    #[test]
    fn a_count_reads_no_element() {
        let skip = node(Rel::Skip(
            Box::new(leaf(int(), Kind::List)),
            Box::new(row(int())),
        ));
        assert_eq!(
            validate(&skip),
            ["skip: count reads '$0', which is not in scope"]
        );
    }

    /// Invariant 3: `$1` is a join's right row, and no other node binds
    /// one.
    #[test]
    fn only_a_join_has_a_second_input() {
        let filter = node(Rel::Filter(
            Row::placeholder(),
            Box::new(leaf(int(), Kind::List)),
            Box::new(Expr::Identifier(bool_(), RIGHT_ROW.to_string())),
        ));
        assert_eq!(
            validate(&filter),
            ["filter: expression reads '$1', which is not in scope"]
        );

        // In a join it is in scope, and nothing is wrong.
        let join = node(Rel::Join(
            JoinKind::Inner,
            JoinRows::placeholder(),
            Box::new(Expr::Apply(
                bool_(),
                Box::new(Expr::Identifier(bool_(), "p".to_string())),
                Box::new(Expr::Tuple(
                    Rc::new(Type::Tuple(vec![int(), string()])),
                    vec![
                        row(int()),
                        Expr::Identifier(string(), RIGHT_ROW.to_string()),
                    ],
                )),
                Span::new(""),
            )),
            Box::new(leaf(int(), Kind::List)),
            Box::new(leaf(string(), Kind::List)),
        ));
        assert_eq!(validate(&join), Vec::<String>::new());
    }

    /// Invariant 3: a join's left row is in scope in its condition and
    /// its right input, and not in its left input.
    #[test]
    fn a_left_row_is_in_scope_in_the_right_input_only() {
        let left_reads_row = node(Rel::Join(
            JoinKind::Inner,
            JoinRows::dependent("v".to_string()),
            Box::new(t()),
            Box::new(Expr::Identifier(
                Kind::List.apply(int()),
                "v".to_string(),
            )),
            Box::new(leaf(string(), Kind::List)),
        ));
        assert_eq!(
            validate(&left_reads_row),
            ["join: left input reads 'v', which is not in scope"]
        );

        // Read by the right input, it is in scope.
        let right_reads_row = node(Rel::Join(
            JoinKind::Inner,
            JoinRows::dependent("v".to_string()),
            Box::new(t()),
            Box::new(leaf(int(), Kind::List)),
            Box::new(Expr::List(
                Kind::List.apply(int()),
                vec![Expr::Identifier(int(), "v".to_string())],
            )),
        ));
        assert_eq!(validate(&right_reads_row), Vec::<String>::new());
    }

    /// A row is a name of its own, so a node may not bind one that an
    /// enclosing node has bound.
    #[test]
    fn a_row_may_not_shadow_an_enclosing_one() {
        let inner = node(Rel::Join(
            JoinKind::Inner,
            JoinRows::dependent("v".to_string()),
            Box::new(t()),
            Box::new(leaf(int(), Kind::List)),
            Box::new(leaf(string(), Kind::List)),
        ));
        let outer = node(Rel::Join(
            JoinKind::Inner,
            JoinRows::dependent("v".to_string()),
            Box::new(t()),
            Box::new(leaf(bool_(), Kind::List)),
            Box::new(inner),
        ));
        assert_eq!(
            validate(&outer),
            ["join: row 'v' is already bound by an enclosing node"]
        );
    }

    /// Invariant 1: a row is its input's element, so reading it as
    /// another type is ill-formed. Writing a test that got this wrong is
    /// what suggested the check.
    #[test]
    fn a_row_has_its_element_type() {
        let filter = node(Rel::Filter(
            Row {
                name: "r0".to_string(),
                ordinal: None,
            },
            Box::new(leaf(bool_(), Kind::List)),
            // The row is a bool here, whatever this says.
            Box::new(Expr::Identifier(int(), "r0".to_string())),
        ));
        assert_eq!(
            validate(&filter),
            [
                "filter: condition has type 'int' and must be 'bool'",
                "filter: expression reads 'r0' as 'int', and it is 'bool'"
            ]
        );
    }

    /// Invariant 4: within one node, output labels are distinct.
    #[test]
    fn labels_are_distinct_within_a_node() {
        let group = node(Rel::Group(
            Row::placeholder(),
            Box::new(leaf(int(), Kind::Bag)),
            vec![(Label::String("a".to_string()), row(int()))],
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
            Row::placeholder(),
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

    /// A nested tree binds a row of its own, so its reading that row is
    /// not a reading by the node that holds it -- here, a count, which
    /// may read no row of its node.
    #[test]
    fn a_nested_tree_binds_a_row_of_its_own() {
        let nested = node(Rel::Filter(
            Row::placeholder(),
            Box::new(leaf(bool_(), Kind::List)),
            Box::new(row(bool_())),
        ));
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
