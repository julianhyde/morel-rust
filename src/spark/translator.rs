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

//! Translates a Morel query, as the core tree holds it, to a Spark
//! plan.
//!
//! Port of morel-java's `SparkTranslator`. Connect's `Relation` is a
//! conventional operator tree, and so is the core tree, so the
//! translation is close to one node for one node. The hinge is the row
//! variable: a Morel query binds one (the `r` of `from r in ...`) and
//! refers to a column as a field of it, which is what Spark calls a
//! subquery alias and a qualified attribute. So the alias goes on the
//! scanned collection, and `#b r` becomes `r.b`.
//!
//! Plan ids are assigned in the order the text prints them -- the
//! outermost node is 0 -- so that a plan's text depends on the query
//! and nothing else.

use crate::compile::core::{Decl, Expr, JoinKind, Pat, Rel, id_name, rename};
use crate::compile::library::BuiltInFunction;
use crate::compile::postfix::peel_type;
use crate::compile::rel_lowerer::{map_children, map_steps};
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::spark::{self as foreign, SparkError};
use crate::eval::val::Val;
use crate::spark::arrow;
use crate::spark::function_table::{
    self, Entry, FunctionTable, Kind, constant_name,
};
use crate::spark::plan::Plan;
use crate::spark::proto::expression::literal::{self, LiteralType};
use crate::spark::proto::expression::{
    self as pexpr, Alias, ExprType, ExpressionString, SortOrder,
    UnresolvedAttribute, UnresolvedFunction,
};
use crate::spark::proto::read::{NamedTable, ReadType};
use crate::spark::proto::relation::RelType;
use crate::spark::proto::{
    self as proto, Aggregate, DataType, Deduplicate, Expression, Filter, Join,
    Limit, LocalRelation, Offset, Project, Read, Relation, RelationCommon,
    SetOperation, Sort, SubqueryAlias, SubqueryExpression, WithRelations,
    aggregate, data_type, join, set_operation, subquery_expression,
};
use crate::spark::schema::{self, option_value_type};
use crate::spark::text_format::java_float;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::result;

type Result<T> = result::Result<T, SparkError>;

/// Translates a query to a plan.
///
/// `query` is a relational node, or the collection the query reads if
/// it reads one whole.
pub fn translate(query: &Expr) -> Result<Plan> {
    let mut translator = Translator {
        functions: FunctionTable::instance(),
        local_row_counts: Vec::new(),
        witnesses: HashMap::new(),
        references: Vec::new(),
        right_rows: HashSet::new(),
        next_plan_id: 0,
    };
    let query = unlet(query);
    let root = translator.rel(&query)?;
    Ok(Plan::new(
        proto::Plan {
            op_type: Some(proto::plan::OpType::Root(root)),
        },
        translator.local_row_counts,
    ))
}

/// Returns the error for something the translator cannot do.
fn unsupported(what: impl AsRef<str>) -> SparkError {
    SparkError::new("UNSUPPORTED", format!("Spark cannot do {}", what.as_ref()))
}

struct Translator {
    functions: &'static FunctionTable,
    local_row_counts: Vec<usize>,
    /// For a row that an outer join may not find, the column that says
    /// whether it was found, by the name the row goes by.
    witnesses: HashMap<String, String>,
    /// The relations that expressions in the query refer to, which
    /// Spark carries beside the root rather than inside it. A
    /// correlated subquery is one.
    references: Vec<Relation>,
    /// The names of the rows that are a join's right row, which a
    /// message calls `$1` where morel-java's tree does.
    right_rows: HashSet<String>,
    next_plan_id: i64,
}

/// Returns a query with the bindings that correlate a subquery
/// substituted away.
///
/// A subquery that reads the enclosing row captures it in a `let`, and
/// names the binding where it means the row: `let val v = d in
/// nonEmpty (... v ...) end`. Spark needs no binding, because a
/// subquery resolves a name against the enclosing relation, and a
/// `let` is in the way of every path that reads an expression, so they
/// come off before anything else looks.
fn unlet(e: &Expr) -> Expr {
    let e = map_deep(e, &unlet);
    if let Expr::Let(_, decls, body) = &e
        && let [Decl::NonRecVal(bind)] = decls.as_slice()
        && let Pat::Identifier(_, name) = &bind.pat
        && let Expr::Identifier(_, value) = &bind.expr
    {
        return rename(body, name, value);
    }
    e
}

/// Applies `f` to each child of `e`, through the nodes of a tree and
/// the steps of a query that the tree declined.
fn map_deep(e: &Expr, f: &dyn Fn(&Expr) -> Expr) -> Expr {
    match e {
        Expr::Rel(t, rel) => {
            Expr::Rel(t.clone(), Box::new(rel.map_children(f)))
        }
        Expr::From(t, steps) => Expr::From(t.clone(), map_steps(steps, f)),
        _ => map_children(e, f),
    }
}

/// Calls `f` for `e` and every expression inside it.
fn visit(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    let children = RefCell::new(Vec::new());
    let _ = map_deep(e, &|c| {
        children.borrow_mut().push(c.clone());
        c.clone()
    });
    for c in children.into_inner() {
        visit(&c, f);
    }
}

/// Returns the name of the operator of an expression, as morel-java's
/// `Op` names it, for a message.
fn op_name(e: &Expr) -> String {
    match e {
        Expr::Literal(t, v) => match (peel_type(t), v) {
            (_, Val::Fn(_)) => "FN_LITERAL",
            (Type::Primitive(PrimitiveType::Unit), _) => "UNIT_LITERAL",
            (Type::Primitive(PrimitiveType::Bool), _) => "BOOL_LITERAL",
            (Type::Primitive(PrimitiveType::Char), _) => "CHAR_LITERAL",
            (Type::Primitive(PrimitiveType::Int), _) => "INT_LITERAL",
            (Type::Primitive(PrimitiveType::Real), _) => "REAL_LITERAL",
            (Type::Primitive(PrimitiveType::String), _) => "STRING_LITERAL",
            _ => "VALUE_LITERAL",
        }
        .to_string(),
        Expr::Identifier(..) => "ID".to_string(),
        Expr::RecordSelector(..) => "RECORD_SELECTOR".to_string(),
        Expr::Current(..) => "CURRENT".to_string(),
        Expr::Ordinal(..) => "ORDINAL".to_string(),
        Expr::Aggregate(..) => "AGGREGATE".to_string(),
        Expr::Apply(..) | Expr::List(..) => "APPLY".to_string(),
        Expr::Case(..) => "CASE".to_string(),
        Expr::Let(..) => "LET".to_string(),
        Expr::Fn(..) => "FN".to_string(),
        Expr::Raise(..) => "RAISE".to_string(),
        Expr::Tuple(..) => "TUPLE".to_string(),
        Expr::From(..) => "FROM".to_string(),
        Expr::Extent(..) => "EXTENT".to_string(),
        Expr::Rel(_, rel) => rel_op_name(rel).to_string(),
    }
}

fn rel_op_name(rel: &Rel) -> &'static str {
    match rel {
        Rel::Except(..) => "EXCEPT",
        Rel::Filter(..) => "FILTER",
        Rel::Group(..) => "GROUP",
        Rel::Intersect(..) => "INTERSECT",
        Rel::Join(..) => "JOIN",
        Rel::Project(..) => "PROJECT",
        Rel::Skip(..) => "SKIP",
        Rel::Sort(..) => "SORT",
        Rel::Take(..) => "TAKE",
        Rel::Unorder(..) => "UNORDER",
        Rel::Union(..) => "UNION",
    }
}

/// Returns the built-in that an expression is the literal of.
fn fn_literal(e: &Expr) -> Option<BuiltInFunction> {
    match e {
        Expr::Literal(_, Val::Fn(f)) => Some(*f),
        _ => None,
    }
}

/// Returns the name a query gave an element, or "" if the compiler
/// named it. A name the query gave has the binder between two `$`s,
/// `$e$3`; any other name with a `$` in it is the compiler's own, and
/// has no name a plan can use.
fn element_name(name: &str) -> String {
    match id_name(name) {
        Some(binder) => binder.to_string(),
        None if name.contains('$') => String::new(),
        None => name.to_string(),
    }
}

/// Returns the field name that a record selector selects.
fn selected_name(slot: usize, arg: &Expr) -> String {
    schema::fields(&arg.type_())
        .and_then(|fields| fields.get(slot).map(|(name, _)| name.clone()))
        .unwrap_or_else(|| {
            panic!("no field {} in {}", slot, arg.type_());
        })
}

/// If `e` is `#f arg`, returns the slot and the argument.
fn selector(e: &Expr) -> Option<(usize, &Expr)> {
    match e {
        Expr::Apply(_, f, arg, _) => match f.as_ref() {
            Expr::RecordSelector(_, slot) => Some((*slot, arg)),
            _ => None,
        },
        _ => None,
    }
}

/// Returns the arguments of a call: a tuple's fields, or the one
/// argument of a one-argument call.
fn arguments(arg: &Expr) -> Vec<&Expr> {
    match arg {
        Expr::Tuple(_, args) => args.iter().collect(),
        _ => vec![arg],
    }
}

/// Peels a call down to the function it calls, adding the arguments it
/// meets to `args` in the order they were written.
///
/// A built-in takes its arguments one way or the other: `String.substring
/// (s, 0, 2)` is one application of a tuple, and `String.isPrefix "S"
/// s` is two applications, one per argument. Both arrive here as the
/// same list, which is what the function table's templates number.
fn flatten<'a>(e: &'a Expr, args: &mut Vec<&'a Expr>) -> &'a Expr {
    match e {
        Expr::Apply(_, f, arg, _) => {
            let f = flatten(f, args);
            args.extend(arguments(arg));
            f
        }
        _ => e,
    }
}

/// Returns the names of a node's input's components: a join's two
/// sides, or nothing at all, since only a join concatenates rows.
fn parts(input: &Expr) -> Vec<String> {
    let Expr::Rel(_, rel) = input else {
        return Vec::new();
    };
    match rel.as_ref() {
        Rel::Join(_, rows, ..) => {
            vec![element_name(&rows.left), element_name(&rows.right)]
        }
        // These pass their element through, so a node above one still
        // reads the components of whatever join is below it.
        Rel::Filter(_, input, _)
        | Rel::Sort(_, input, _)
        | Rel::Skip(input, _)
        | Rel::Take(input, _)
        | Rel::Unorder(input) => parts(input),
        _ => Vec::new(),
    }
}

/// Returns the alias that qualifies a field read out of `e`, or `None`
/// if `e` is not something a field can be read from.
///
/// A field of the row is qualified by the row's own name. A field of a
/// component of the row -- what a projection over a join reads -- is
/// qualified by the name of the input that contributed it, which
/// `parts` lists in order.
fn qualifier(e: &Expr, parts: &[String]) -> Option<String> {
    match e {
        // A row the compiler named, as a projection's output is, has
        // no alias in the plan, so a column of it is unqualified.
        Expr::Identifier(_, name) => Some(element_name(name)),
        _ => match selector(e) {
            Some((slot, Expr::Identifier(..))) if slot < parts.len() => {
                Some(parts[slot].clone())
            }
            _ => None,
        },
    }
}

/// Returns whether a node is a projection that reads the whole of its
/// input: the one field of a one-field row, which leaves the relation
/// as it was.
fn is_whole_of_input(rel: &Rel) -> Option<&Expr> {
    let Rel::Project(_, input, e) = rel else {
        return None;
    };
    let (slot, Expr::Identifier(..)) = selector(e)? else {
        return None;
    };
    let element_type = schema::element_type(&input.type_())?;
    let fields = match peel_type(&element_type) {
        Type::Record(..) | Type::Tuple(..) => schema::fields(&element_type)?,
        _ => return None,
    };
    let (_, arg) = selector(e)?;
    (fields.len() == 1 && fields[0].0 == selected_name(slot, arg))
        .then_some(input)
}

/// Returns the column that an expression reads of a row, or `None`.
fn column_of(e: &Expr, row: &str) -> Option<String> {
    match selector(e) {
        Some((slot, arg @ Expr::Identifier(_, name))) if name == row => {
            Some(selected_name(slot, arg))
        }
        _ => None,
    }
}

/// Returns whether a built-in is `=`.
fn is_equals(f: BuiltInFunction) -> bool {
    matches!(f.name(), "=" | "op =")
}

/// Returns a column of the right row's join key, or `None` if the
/// condition has none.
///
/// This is the column that says whether a left join found the row: a
/// key cannot be null in a row that matched, because a null key
/// matches nothing, so asking whether it is null asks exactly the right
/// question. The types cannot answer it: a catalog column is a plain
/// type whether or not it holds nulls.
fn key_column(condition: &Expr, right_row: &str) -> Option<String> {
    let Expr::Apply(_, f, arg, _) = condition else {
        return None;
    };
    let f = fn_literal(f)?;
    let args = arguments(arg);
    if f == BuiltInFunction::BoolAndAlso {
        // Any conjunct may hold the key.
        return args.iter().find_map(|a| key_column(a, right_row));
    }
    if is_equals(f) {
        return args.iter().find_map(|a| column_of(a, right_row));
    }
    None
}

fn common(plan_id: i64) -> Option<RelationCommon> {
    Some(RelationCommon {
        plan_id: Some(plan_id),
        ..Default::default()
    })
}

fn relation(plan_id: i64, rel_type: RelType) -> Relation {
    Relation {
        common: common(plan_id),
        rel_type: Some(rel_type),
    }
}

fn expression(t: ExprType) -> Expression {
    Expression {
        common: None,
        expr_type: Some(t),
    }
}

fn attribute(identifier: String) -> Expression {
    expression(ExprType::UnresolvedAttribute(UnresolvedAttribute {
        unparsed_identifier: identifier,
        plan_id: None,
        is_metadata_column: Some(false),
    }))
}

fn literal(t: LiteralType) -> Expression {
    expression(ExprType::Literal(pexpr::Literal {
        literal_type: Some(t),
    }))
}

/// Builds a call to a Spark function.
fn call(name: &str, args: Vec<Expression>) -> Expression {
    expression(ExprType::UnresolvedFunction(UnresolvedFunction {
        function_name: name.to_string(),
        arguments: args,
        ..Default::default()
    }))
}

fn alias(e: Expression, name: &str) -> Expression {
    expression(ExprType::Alias(Box::new(Alias {
        expr: Some(Box::new(e)),
        name: vec![name.to_string()],
        metadata: None,
    })))
}

/// Names an expression, unless it already reads the field of that
/// name: a key called `deptno` that reads `deptno` needs no alias, and
/// an aggregate always does.
fn named(e: Expression, name: &str) -> Expression {
    if let Some(ExprType::UnresolvedAttribute(a)) = &e.expr_type {
        let id = &a.unparsed_identifier;
        if id.ends_with(&format!(".{}", name)) || id == name {
            return e;
        }
    }
    alias(e, name)
}

/// Returns the value of a decimal literal as Spark wants it: its plain
/// digits, precision and scale, with a scale that Spark allows (Spark
/// has no negative scale, so `2E+3` becomes `2000`).
fn decimal_parts(e: &Expr) -> Option<(String, i32, i32)> {
    let Expr::Literal(_, Val::Decimal(d)) = e else {
        return None;
    };
    let (neg, digits, exp) = d.parts();
    let (unscaled, scale) = if digits.is_empty() {
        ("0".to_string(), 0)
    } else if exp >= 0 {
        (format!("{}{}", digits, "0".repeat(exp as usize)), 0)
    } else {
        (digits.to_string(), -exp)
    };
    let precision = unscaled.len() as i32;
    let mut plain = String::new();
    if neg {
        plain.push('-');
    }
    if scale == 0 {
        plain.push_str(&unscaled);
    } else if (scale as usize) < unscaled.len() {
        let point = unscaled.len() - scale as usize;
        plain.push_str(&unscaled[..point]);
        plain.push('.');
        plain.push_str(&unscaled[point..]);
    } else {
        plain.push_str("0.");
        plain.push_str(&"0".repeat(scale as usize - unscaled.len()));
        plain.push_str(&unscaled);
    }
    Some((plain, precision.max(scale + 1), scale))
}

/// Returns whether a Spark name is a word, and so written as a call,
/// rather than a symbol written between its arguments.
fn is_word(name: &str) -> bool {
    name.chars().next().is_some_and(char::is_alphabetic)
}

impl Translator {
    fn next(&mut self) -> i64 {
        let id = self.next_plan_id;
        self.next_plan_id += 1;
        id
    }

    /// Returns the name a built-in goes by: the table's name for it,
    /// which is the name a program writes.
    fn name(&self, f: BuiltInFunction) -> String {
        match self.functions.get(f) {
            Some(entry) => entry.morel.clone(),
            None => f.name().to_string(),
        }
    }

    fn entry(&self, f: BuiltInFunction) -> Option<&'static Entry> {
        self.functions.get(f)
    }

    /// Returns the name a variable goes by in a message: a row by the
    /// name of its binder, or, if the compiler named it, by the name
    /// morel-java's tree gives it, `$0` or `$1`.
    fn variable_name(&self, name: &str) -> String {
        match id_name(name) {
            Some(binder) => binder.to_string(),
            None if name.contains('$') => {
                if self.right_rows.contains(name) {
                    "$1".to_string()
                } else {
                    "$0".to_string()
                }
            }
            None => name.to_string(),
        }
    }

    /// Translates a relational node, wrapping it where its own
    /// expressions refer to relations: Spark keeps those beside the
    /// node, not inside it, and the wrapper is what holds them. The
    /// wrapper takes the plan id above the node's.
    fn rel(&mut self, e: &Expr) -> Result<Relation> {
        let Expr::Rel(_, rel) = e else {
            // The query is the collection itself -- `from e in emps`,
            // with no step but the scan -- so the plan is the read.
            return self.leaf(e);
        };
        if let Some(input) = is_whole_of_input(rel) {
            // Morel distinguishes a bag of one-field records from a bag
            // of values, and a projection turns the one into the other.
            // Spark does not: a relation always has named columns, so
            // the projection is nothing to do, and takes no plan id.
            return self.rel(input);
        }
        if !self.refers_to_relation(rel) {
            let id = self.next();
            return self.rel_node(e, rel, id);
        }
        let wrapper_id = self.next();
        let enclosing = std::mem::take(&mut self.references);
        let id = self.next();
        let node = self.rel_node(e, rel, id)?;
        let own = std::mem::replace(&mut self.references, enclosing);
        Ok(relation(
            wrapper_id,
            RelType::WithRelations(Box::new(WithRelations {
                root: Some(Box::new(node)),
                references: own,
            })),
        ))
    }

    /// Returns whether a node's own expressions ask a question of a
    /// query.
    fn refers_to_relation(&self, rel: &Rel) -> bool {
        match rel {
            Rel::Filter(_, _, e) | Rel::Project(_, _, e) => {
                self.contains_subquery(e)
            }
            _ => false,
        }
    }

    /// Returns whether an expression asks a question of a query. The
    /// function table says which built-ins do.
    fn contains_subquery(&self, e: &Expr) -> bool {
        let mut found = false;
        visit(e, &mut |e| {
            if let Expr::Apply(_, f, _, _) = e
                && let Some(f) = fn_literal(f)
                && let Some(entry) = self.entry(f)
                && entry.kind == Kind::Subquery
            {
                found = true;
            }
        });
        found
    }

    /// Translates one relational node, under a given plan id.
    fn rel_node(
        &mut self,
        e: &Expr,
        rel: &Rel,
        plan_id: i64,
    ) -> Result<Relation> {
        let rel_type = match rel {
            Rel::Filter(row, input, condition) => {
                let input2 = self.input(input, &row.name)?;
                let condition = self.exp(condition, &parts(input))?;
                RelType::Filter(Box::new(Filter {
                    input: Some(Box::new(input2)),
                    condition: Some(condition),
                }))
            }
            Rel::Project(row, input, exp) => {
                let input2 = self.input(input, &row.name)?;
                let expressions =
                    self.projections(exp, &parts(input), &e.type_())?;
                RelType::Project(Box::new(Project {
                    input: Some(Box::new(input2)),
                    expressions,
                }))
            }
            Rel::Group(row, input, keys, aggregates) => {
                let group_parts = parts(input);
                if aggregates.is_empty() {
                    // Grouping without aggregating asks only for distinct
                    // rows, which Spark does by projecting the keys and
                    // deduplicating them. One node becomes two, so the
                    // inner one takes the next plan id.
                    let key_id = self.next();
                    let key_input = self.input(input, &row.name)?;
                    let mut expressions = Vec::new();
                    for (name, key) in keys {
                        let k = self.exp(key, &group_parts)?;
                        expressions.push(named(k, &name.to_string()));
                    }
                    RelType::Deduplicate(Box::new(Deduplicate {
                        input: Some(Box::new(relation(
                            key_id,
                            RelType::Project(Box::new(Project {
                                input: Some(Box::new(key_input)),
                                expressions,
                            })),
                        ))),
                        column_names: Vec::new(),
                        all_columns_as_keys: Some(true),
                        within_watermark: Some(false),
                    }))
                } else {
                    let input2 = self.input(input, &row.name)?;
                    let mut grouping_expressions = Vec::new();
                    for (name, key) in keys {
                        let k = self.exp(key, &group_parts)?;
                        grouping_expressions.push(named(k, &name.to_string()));
                    }
                    let mut aggregate_expressions = Vec::new();
                    for (name, agg) in aggregates {
                        let a = self.aggregate(agg, &group_parts)?;
                        aggregate_expressions.push(named(a, &name.to_string()));
                    }
                    RelType::Aggregate(Box::new(Aggregate {
                        input: Some(Box::new(input2)),
                        group_type: aggregate::GroupType::Groupby as i32,
                        grouping_expressions,
                        aggregate_expressions,
                        pivot: None,
                        grouping_sets: Vec::new(),
                    }))
                }
            }
            Rel::Sort(row, input, key) => {
                let input2 = self.input(input, &row.name)?;
                let mut order = Vec::new();
                self.sort_order(key, false, &parts(input), &mut order)?;
                // A query orders its whole result, not each partition.
                RelType::Sort(Box::new(Sort {
                    input: Some(Box::new(input2)),
                    order,
                    is_global: Some(true),
                }))
            }
            Rel::Take(input, count) => {
                let input2 = self.rel(input)?;
                RelType::Limit(Box::new(Limit {
                    input: Some(Box::new(input2)),
                    limit: Self::count(count, "take")?,
                }))
            }
            Rel::Skip(input, count) => {
                let input2 = self.rel(input)?;
                RelType::Offset(Box::new(Offset {
                    input: Some(Box::new(input2)),
                    offset: Self::count(count, "skip")?,
                }))
            }
            Rel::Union(distinct, inputs)
            | Rel::Intersect(distinct, inputs)
            | Rel::Except(distinct, inputs) => {
                let op = rel_op_name(rel);
                if inputs.len() != 2 {
                    // Spark's set operation takes two inputs; Morel's
                    // takes any number.
                    return Err(unsupported(format!(
                        "{} of {} inputs",
                        op,
                        inputs.len()
                    )));
                }
                let left = self.rel(&inputs[0])?;
                let right = self.rel(&inputs[1])?;
                let set_op_type = match rel {
                    Rel::Union(..) => set_operation::SetOpType::Union,
                    Rel::Intersect(..) => set_operation::SetOpType::Intersect,
                    _ => set_operation::SetOpType::Except,
                };
                // Morel's set operators are over bags and keep every
                // row, unless the query asked for distinct.
                RelType::SetOp(Box::new(SetOperation {
                    left_input: Some(Box::new(left)),
                    right_input: Some(Box::new(right)),
                    set_op_type: set_op_type as i32,
                    is_all: Some(!distinct),
                    by_name: Some(false),
                    allow_missing_columns: Some(false),
                }))
            }
            Rel::Join(kind, rows, condition, left, right) => {
                self.right_rows.insert(rows.right.clone());
                if *kind == JoinKind::Left
                    && let Some(key) = key_column(condition, &rows.right)
                {
                    self.witnesses.insert(element_name(&rows.right), key);
                }
                let left2 = self.input(left, &rows.left)?;
                let right2 = self.input(right, &rows.right)?;
                let join_condition = self.exp(condition, &[])?;
                let join_type = match kind {
                    JoinKind::Inner => join::JoinType::Inner,
                    JoinKind::Left => join::JoinType::LeftOuter,
                    JoinKind::Right => join::JoinType::RightOuter,
                    JoinKind::Full => join::JoinType::FullOuter,
                };
                RelType::Join(Box::new(Join {
                    left: Some(Box::new(left2)),
                    right: Some(Box::new(right2)),
                    join_condition: Some(join_condition),
                    join_type: join_type as i32,
                    using_columns: Vec::new(),
                    join_data_type: None,
                }))
            }
            Rel::Unorder(..) => {
                return Err(unsupported(format!(
                    "relational operator {}",
                    rel_op_name(rel)
                )));
            }
        };
        Ok(relation(plan_id, rel_type))
    }

    /// Translates a node's input. A relational input translates as
    /// itself; anything else is the collection the query scans, and
    /// takes the row variable's name as its alias.
    fn input(&mut self, e: &Expr, row: &str) -> Result<Relation> {
        if matches!(e, Expr::Rel(..)) {
            return self.rel(e);
        }
        let plan_id = self.next();
        let leaf = self.leaf(e)?;
        Ok(relation(
            plan_id,
            RelType::SubqueryAlias(Box::new(SubqueryAlias {
                input: Some(Box::new(leaf)),
                alias: element_name(row),
                qualifier: Vec::new(),
            })),
        ))
    }

    /// Translates the collection a query scans.
    fn leaf(&mut self, e: &Expr) -> Result<Relation> {
        let plan_id = self.next();
        if let Expr::List(t, elements) = e {
            let mut rows = Vec::new();
            for element in elements {
                rows.push(Self::value(element)?);
            }
            return self.local_relation(plan_id, &rows, t);
        }
        if let Some(table) = catalog_table(e) {
            return Ok(relation(
                plan_id,
                RelType::Read(Read {
                    read_type: Some(ReadType::NamedTable(NamedTable {
                        unparsed_identifier: table,
                        options: HashMap::new(),
                    })),
                    is_streaming: false,
                }),
            ));
        }
        if let Expr::Literal(t, Val::List(rows)) = e {
            // A collection the query reached through a name rather than
            // writing out, and not a table of a catalog: its rows cross
            // as a local relation, as an inline collection's do.
            return self.local_relation(plan_id, rows, t);
        }
        Err(unsupported(format!("collection {}", op_name(e))))
    }

    /// Returns the Morel value of a constant expression: a row of an
    /// inline collection, which Spark carries as data rather than as
    /// expressions.
    fn value(e: &Expr) -> Result<Val> {
        match e {
            Expr::Literal(_, v) => Ok(v.clone()),
            Expr::Tuple(_, args) => {
                let mut values = Vec::new();
                for arg in args {
                    values.push(Self::value(arg)?);
                }
                Ok(Val::List(Rc::new(values)))
            }
            _ => Err(unsupported(format!("a row that is {}", op_name(e)))),
        }
    }

    /// Translates a collection of rows as a local relation: the rows as
    /// an Arrow batch, and the schema that says what the bytes mean.
    fn local_relation(
        &mut self,
        plan_id: i64,
        rows: &[Val],
        collection_type: &Type,
    ) -> Result<Relation> {
        let element_type = schema::element_type(collection_type)
            .unwrap_or_else(|| Rc::new(collection_type.clone()));
        self.local_row_counts.push(rows.len());
        let data = arrow::encode(rows, &element_type)?;
        let schema = schema::schema_json(&element_type)?;
        Ok(relation(
            plan_id,
            RelType::LocalRelation(LocalRelation {
                data: Some(data),
                schema: Some(schema),
            }),
        ))
    }

    /// Returns how many rows a `take` or a `skip` counts. Spark wants a
    /// number, so a count that is not a literal cannot be pushed down.
    fn count(e: &Expr, what: &str) -> Result<i32> {
        match e {
            Expr::Literal(_, Val::Int(n)) => Ok(*n),
            _ => Err(unsupported(format!("{} of {}", what, op_name(e)))),
        }
    }

    /// Translates the expression a `yield` computes into one Spark
    /// expression per output field. A field whose value is the input
    /// field of the same name needs no alias; anything else is aliased
    /// to the output name.
    fn projections(
        &mut self,
        e: &Expr,
        parts: &[String],
        t: &Type,
    ) -> Result<Vec<Expression>> {
        let Expr::Tuple(_, args) = e else {
            // A query can yield one unnamed column -- `yield d.dname` --
            // and then there is no record of names to draw an alias
            // from.
            return Ok(vec![self.exp(e, parts)?]);
        };
        let names: Vec<String> = schema::element_type(t)
            .and_then(|e| schema::fields(&e))
            .map(|fields| fields.into_iter().map(|(n, _)| n).collect())
            .unwrap_or_default();
        let mut expressions = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            let name = &names[i];
            let expression = self.exp(arg, parts)?;
            let field_name = selector(arg).map(|(s, a)| selected_name(s, a));
            if field_name.as_deref() == Some(name.as_str()) {
                expressions.push(expression);
            } else {
                expressions.push(alias(expression, name));
            }
        }
        Ok(expressions)
    }

    /// Translates an expression.
    fn exp(&mut self, e: &Expr, parts: &[String]) -> Result<Expression> {
        match e {
            Expr::Apply(t, f, arg, _) => {
                if let Expr::RecordSelector(_, slot) = f.as_ref() {
                    if matches!(arg.as_ref(), Expr::Identifier(..))
                        && !parts.is_empty()
                        && *slot < parts.len()
                    {
                        // A whole input of a join, not a column of one:
                        // `yield {d.dname, e}` asks for all of `e`.
                        return self.component(&parts[*slot], t);
                    }
                    if let Some(q) = qualifier(arg, parts) {
                        let name = selected_name(*slot, arg);
                        return Ok(attribute(if q.is_empty() {
                            name
                        } else {
                            format!("{}.{}", q, name)
                        }));
                    }
                }
                let mut args = Vec::new();
                let fun = flatten(e, &mut args);
                if let Some(builtin) = fn_literal(fun) {
                    return self.function(builtin, &args, parts);
                }
                Err(unsupported(format!("call to {}", op_name(f))))
            }
            Expr::Literal(t, v) => match (peel_type(t), v) {
                (_, Val::Bool(b)) => Ok(literal(LiteralType::Boolean(*b))),
                (_, Val::Int(i)) => Ok(literal(LiteralType::Integer(*i))),
                (_, Val::Real(r)) => {
                    Ok(literal(LiteralType::Double(*r as f64)))
                }
                (Type::Primitive(PrimitiveType::String), Val::String(s)) => {
                    Ok(literal(LiteralType::String(s.to_string())))
                }
                (_, Val::Decimal(_)) => {
                    // A `decimal` literal. Morel's decimal is
                    // arbitrary-precision, and Spark's is not, so the
                    // literal carries the narrowest decimal type that
                    // holds the value -- the type Spark's own parser
                    // gives the same literal written as SQL.
                    let (value, precision, scale) =
                        decimal_parts(e).expect("decimal");
                    Ok(literal(LiteralType::Decimal(literal::Decimal {
                        value,
                        precision: Some(precision),
                        scale: Some(scale),
                    })))
                }
                _ => Err(unsupported(format!("expression {}", op_name(e)))),
            },
            Expr::Identifier(_, name) => {
                // A name that is not a column of the query: a plan's
                // parameter, say, or a value the resolver could not
                // replace with what it holds. Naming it says which.
                Err(unsupported(format!(
                    "the variable {}",
                    self.variable_name(name)
                )))
            }
            _ => Err(unsupported(format!("expression {}", op_name(e)))),
        }
    }

    /// Translates a call to a built-in.
    fn function(
        &mut self,
        f: BuiltInFunction,
        args: &[&Expr],
        parts: &[String],
    ) -> Result<Expression> {
        let Some(entry) = self.entry(f) else {
            return Err(unsupported(format!(
                "built-in {}, which the table omits",
                f.name()
            )));
        };
        match entry.kind {
            Kind::Rewritten => {
                // The template is SQL, so its arguments must be SQL too,
                // and so must anything inside them.
                let s = function_table::expand(&entry.spark, |i| {
                    self.sql(args[i], parts)
                })?;
                Ok(expression(ExprType::ExpressionString(ExpressionString {
                    expression: s,
                })))
            }
            Kind::Subquery => self.subquery(f, args, parts),
            Kind::Direct => {
                let mut arguments = Vec::new();
                for arg in args {
                    arguments.push(self.exp(arg, parts)?);
                }
                Ok(call(&entry.spark, arguments))
            }
            _ => Err(unsupported(format!(
                "{}, which the table calls {}",
                self.name(f),
                entry.kind.lower()
            ))),
        }
    }

    /// Translates an aggregate function over a group: the function the
    /// table names, applied to what the query aggregates. An aggregate
    /// with no argument counts rows, and Spark counts them by counting a
    /// constant.
    fn aggregate(
        &mut self,
        agg: &Expr,
        parts: &[String],
    ) -> Result<Expression> {
        let Expr::Aggregate(_, f, arg, _) = agg else {
            return Err(unsupported(format!("aggregate {}", op_name(agg))));
        };
        let Some(builtin) = fn_literal(f) else {
            return Err(unsupported(format!("aggregate {}", op_name(f))));
        };
        let Some(entry) = self.entry(builtin) else {
            return Err(unsupported(format!(
                "aggregate {}, which the table omits",
                builtin.name()
            )));
        };
        if entry.kind != Kind::Aggregate {
            return Err(unsupported(format!(
                "{} over a group, which the table calls {}",
                self.name(builtin),
                entry.kind.lower()
            )));
        }
        let is_unit = matches!(
            arg.as_ref(),
            Expr::Literal(t, _)
                if matches!(peel_type(t), Type::Primitive(PrimitiveType::Unit))
        );
        let argument = if is_unit {
            literal(LiteralType::Integer(1))
        } else {
            self.exp(arg, parts)?
        };
        Ok(call(&entry.spark, vec![argument]))
    }

    /// Translates the keys a query orders by, which are a tuple when
    /// there is more than one, and each of which may be wrapped in
    /// `DESC`. Spark puts nulls where that direction puts them: last
    /// when descending, first when ascending.
    fn sort_order(
        &mut self,
        e: &Expr,
        descending: bool,
        parts: &[String],
        order: &mut Vec<SortOrder>,
    ) -> Result<()> {
        if let Expr::Apply(_, f, arg, _) = e
            && fn_literal(f) == Some(BuiltInFunction::DescendingDesc)
        {
            return self.sort_order(arg, !descending, parts, order);
        }
        if let Expr::Tuple(_, args) = e {
            for arg in args {
                self.sort_order(arg, descending, parts, order)?;
            }
            return Ok(());
        }
        let child = self.exp(e, parts)?;
        use pexpr::sort_order::{NullOrdering, SortDirection};
        order.push(SortOrder {
            child: Some(Box::new(child)),
            direction: if descending {
                SortDirection::Descending
            } else {
                SortDirection::Ascending
            } as i32,
            null_ordering: if descending {
                NullOrdering::SortNullsLast
            } else {
                NullOrdering::SortNullsFirst
            } as i32,
        });
        Ok(())
    }

    /// Translates a call that asks a question of a query: whether it has
    /// a row, whether it holds a value, or what its one value is. The
    /// query goes beside the root, under a plan id of its own, and the
    /// expression quotes that id.
    fn subquery(
        &mut self,
        f: BuiltInFunction,
        args: &[&Expr],
        parts: &[String],
    ) -> Result<Expression> {
        use subquery_expression::SubqueryType;
        let _ = parts;
        let (relation, subquery_type, negated) = match f {
            BuiltInFunction::ListElem | BuiltInFunction::ListNotElem => {
                let id = self.next();
                (
                    self.elem_relation(args[1], args[0], id)?,
                    SubqueryType::Exists,
                    f == BuiltInFunction::ListNotElem,
                )
            }
            BuiltInFunction::RelationalOnly => {
                (self.relation(args[0])?, SubqueryType::Scalar, false)
            }
            BuiltInFunction::RelationalNonEmpty
            | BuiltInFunction::RelationalEmpty
            | BuiltInFunction::ListNull => (
                self.relation(args[0])?,
                SubqueryType::Exists,
                // Spark has no NOT EXISTS of its own; `empty` is
                // `exists` denied.
                f != BuiltInFunction::RelationalNonEmpty,
            ),
            _ => {
                return Err(unsupported(format!(
                    "{}, which the table calls a subquery",
                    self.name(f)
                )));
            }
        };
        let plan_id = relation
            .common
            .as_ref()
            .and_then(|c| c.plan_id)
            .unwrap_or(0);
        self.references.push(relation);
        let e = expression(ExprType::SubqueryExpression(SubqueryExpression {
            plan_id,
            subquery_type: subquery_type as i32,
            table_arg_options: None,
        }));
        Ok(if negated { call("not", vec![e]) } else { e })
    }

    /// Translates the query a subquery expression asks about.
    fn relation(&mut self, e: &Expr) -> Result<Relation> {
        if !matches!(e, Expr::Rel(..)) {
            return Err(unsupported(format!("a subquery over {}", op_name(e))));
        }
        self.rel(e)
    }

    /// Translates the collection of an `elem` as the relation of an
    /// EXISTS subquery: not the values the query yields, but the rows
    /// that hold the value asked about.
    ///
    /// Spark Connect 4.0 has no IN subquery, so `x elem q` becomes
    /// `exists q where v = x`, where v is what q yields. Where q filters
    /// already, the equality joins that condition rather than standing
    /// in a second filter above it.
    fn elem_relation(
        &mut self,
        collection: &Expr,
        value: &Expr,
        plan_id: i64,
    ) -> Result<Relation> {
        let Expr::Rel(_, rel) = collection else {
            return Err(unsupported(format!(
                "elem over {}",
                op_name(collection)
            )));
        };
        let Rel::Project(row, input, exp) = rel.as_ref() else {
            return Err(unsupported(format!("elem over {}", rel_op_name(rel))));
        };
        let parts = parts(input);
        let projected = self.exp(exp, &parts)?;
        let asked = self.exp(value, &parts)?;
        let equality = call("==", vec![projected, asked]);
        let filter = match input.as_ref() {
            Expr::Rel(_, inner)
                if matches!(inner.as_ref(), Rel::Filter(..)) =>
            {
                let Rel::Filter(filter_row, filter_input, condition) =
                    inner.as_ref()
                else {
                    unreachable!()
                };
                let input2 = self.input(filter_input, &filter_row.name)?;
                let c = self.exp(condition, &parts)?;
                Filter {
                    input: Some(Box::new(input2)),
                    condition: Some(call("and", vec![c, equality])),
                }
            }
            _ => Filter {
                input: Some(Box::new(self.input(input, &row.name)?)),
                condition: Some(equality),
            },
        };
        Ok(relation(plan_id, RelType::Filter(Box::new(filter))))
    }

    /// Translates a reference to a whole input of a join: a struct of its
    /// columns, and, where the input may be absent, null instead of the
    /// struct when it was.
    ///
    /// Spark gives an absent side a row of nulls rather than an absent
    /// row, so the only way to tell is to ask whether a column that
    /// cannot be null is null. A row all of whose columns are optional
    /// has no such column, and the two cases are then the same bytes, so
    /// such a join is refused.
    fn component(&mut self, alias_name: &str, t: &Type) -> Result<Expression> {
        let value_type = option_value_type(t)?;
        let row_type = value_type.clone().unwrap_or_else(|| Rc::new(t.clone()));
        let fields = match peel_type(&row_type) {
            Type::Record(..) | Type::Tuple(..) => {
                schema::fields(&row_type).unwrap_or_default()
            }
            _ => {
                return Err(unsupported(format!(
                    "a whole input of type {}",
                    row_type
                )));
            }
        };
        let arguments = fields
            .iter()
            .map(|(name, _)| {
                alias(attribute(format!("{}.{}", alias_name, name)), name)
            })
            .collect();
        let struct_exp = call("struct", arguments);
        if value_type.is_none() {
            return Ok(struct_exp);
        }
        let Some(witness) = self.witnesses.get(alias_name).cloned() else {
            return Err(unsupported(
                "a row of this join that may be absent, because nothing \
                 in the join's condition says whether a row was found",
            ));
        };
        let null = literal(LiteralType::Null(DataType {
            kind: Some(data_type::Kind::Null(data_type::Null::default())),
        }));
        Ok(call(
            "when",
            vec![
                call(
                    "isNull",
                    vec![attribute(format!("{}.{}", alias_name, witness))],
                ),
                null,
                struct_exp,
            ],
        ))
    }

    /// Renders an expression as SQL, for a template to put its
    /// arguments into.
    ///
    /// Every compound expression is parenthesized, whatever its
    /// operator: the text goes to Spark's parser, and parenthesizing
    /// unconditionally is both shorter to write and safer to read than
    /// a table of precedences.
    fn sql(&mut self, e: &Expr, parts: &[String]) -> Result<String> {
        match e {
            Expr::Literal(_, Val::Bool(b)) => return Ok(b.to_string()),
            Expr::Literal(_, Val::Int(i)) => return Ok(i.to_string()),
            Expr::Literal(_, Val::Real(r)) => {
                return Ok(java_float(*r));
            }
            Expr::Literal(_, Val::Decimal(_)) => {
                // `BD` is how SQL spells a decimal literal; without it,
                // Spark would read `2` as an int and `2.5` as a double.
                let (value, _, _) = decimal_parts(e).expect("decimal");
                return Ok(format!("{}BD", value));
            }
            Expr::Literal(t, Val::String(s))
                if matches!(
                    peel_type(t),
                    Type::Primitive(PrimitiveType::String)
                ) =>
            {
                return Ok(format!("'{}'", s.replace('\'', "''")));
            }
            Expr::Apply(_, f, arg, _) => {
                if let Expr::RecordSelector(_, slot) = f.as_ref()
                    && let Some(q) = qualifier(arg, parts)
                {
                    let name = selected_name(*slot, arg);
                    return Ok(if q.is_empty() {
                        name
                    } else {
                        format!("{}.{}", q, name)
                    });
                }
                let mut args = Vec::new();
                let fun = flatten(e, &mut args);
                if let Some(builtin) = fn_literal(fun) {
                    return self.sql_call(builtin, &args, parts);
                }
            }
            _ => {}
        }
        Err(unsupported(format!(
            "expression {} inside a SQL template",
            op_name(e)
        )))
    }

    /// Renders a call to a built-in as SQL.
    fn sql_call(
        &mut self,
        f: BuiltInFunction,
        args: &[&Expr],
        parts: &[String],
    ) -> Result<String> {
        let Some(entry) = self.entry(f) else {
            return Err(unsupported(format!(
                "built-in {} inside a SQL template, which the table omits",
                constant_name(f)
            )));
        };
        match entry.kind {
            Kind::Rewritten => function_table::expand(&entry.spark, |i| {
                self.sql(args[i], parts)
            }),
            Kind::Direct => {
                if args.len() == 2 && !is_word(&entry.spark) {
                    return Ok(format!(
                        "({} {} {})",
                        self.sql(args[0], parts)?,
                        entry.spark,
                        self.sql(args[1], parts)?
                    ));
                }
                let mut b = format!("{}(", entry.spark);
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        b.push_str(", ");
                    }
                    b.push_str(&self.sql(arg, parts)?);
                }
                b.push(')');
                Ok(b)
            }
            _ => Err(unsupported(format!(
                "{} inside a SQL template, which the table calls {}",
                constant_name(f),
                entry.kind.upper()
            ))),
        }
    }
}

/// Returns what Spark calls the table a collection reads, or `None` if
/// the collection is not a table of a connection's catalog.
///
/// The name is no guide, so the value decides: `scott.emps` may be a
/// table of the server, a data set of this session with the same name,
/// or a record whose field holds a collection, and only the first is a
/// scan. A table arrives as a value, because preparing replaced the
/// expression that read it with what it holds; and so do the rows of a
/// table that a name was bound to, which still know where they came
/// from.
fn catalog_table(e: &Expr) -> Option<String> {
    match e {
        Expr::Literal(_, Val::Progressive(tv)) => tv.qualified_name(),
        Expr::Literal(_, Val::List(rows)) => foreign::table_of_rows(rows),
        _ => None,
    }
}

// End translator.rs
