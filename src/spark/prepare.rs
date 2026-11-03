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

//! Expands `Spark.prepare (c, f)` and `Spark.remote (c, f)` where they
//! are applied to a function expression: translates `f` for connection
//! `c`, once, at compile time, and puts the plan in place of the call.
//!
//! Port of the part of morel-java's `Resolver` that does this. It runs
//! after inlining, as morel-java's does, because until a built-in is a
//! function literal the translator cannot see which function a call is
//! to; and before compiling, because by then the function is code and
//! its tree is gone. The connection must be a value at compile time --
//! a name bound to a connection, say -- since the plan is made for it.

use crate::compile::core::{Decl, Expr, Pat, ValBind};
use crate::compile::library::{BuiltIn, BuiltInFunction, lookup};
use crate::compile::postfix::peel_type;
use crate::compile::rel_lowerer::{map_children, map_steps};
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::code::LIBRARY;
use crate::eval::spark::{PreparedPlan, SparkError};
use crate::eval::val::{NativeFn, Val};
use crate::spark::schema;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// Expands every `prepare` and `remote` in a declaration.
///
/// `bindings` are the values of the session's names, which is how the
/// connection, and the collections that a query reads, are found.
pub fn prepare_decl(
    decl: Decl,
    bindings: &HashMap<String, Val>,
) -> Result<Decl, SparkError> {
    let preparer = Preparer {
        bindings,
        error: RefCell::new(None),
    };
    let decl = match decl {
        Decl::NonRecVal(bind) => {
            Decl::NonRecVal(Box::new(preparer.bind(bind.as_ref())))
        }
        Decl::RecVal(binds) => {
            Decl::RecVal(binds.iter().map(|b| preparer.bind(b)).collect())
        }
        decl => decl,
    };
    match preparer.error.into_inner() {
        Some(e) => Err(e),
        None => Ok(decl),
    }
}

struct Preparer<'a> {
    bindings: &'a HashMap<String, Val>,
    /// The first failure; once there is one, nothing more is prepared.
    error: RefCell<Option<SparkError>>,
}

impl Preparer<'_> {
    fn bind(&self, bind: &ValBind) -> ValBind {
        let mut bind = bind.clone();
        bind.expr = self.exp(&bind.expr);
        bind
    }

    fn exp(&self, e: &Expr) -> Expr {
        if self.error.borrow().is_some() {
            return e.clone();
        }
        if let Expr::Apply(t, f, arg, span) = e
            && let Expr::Literal(_, Val::Fn(builtin)) = f.as_ref()
            && matches!(
                builtin,
                BuiltInFunction::SparkPrepare | BuiltInFunction::SparkRemote
            )
            && let Expr::Tuple(_, args) = arg.as_ref()
            && args.len() == 2
        {
            return match self.prepare(&args[0], &args[1]) {
                Ok(plan) => {
                    let plan = Rc::new(plan);
                    let value = if *builtin == BuiltInFunction::SparkPrepare {
                        Val::Plan(plan)
                    } else {
                        // `remote (c, f)` is `prepare` and `execute` in
                        // one step, and its value is a function that
                        // runs the plan.
                        let span = span.clone();
                        let description = plan.describe();
                        Val::NativeFn(Rc::new(NativeFn::described(
                            "Spark.execute",
                            description,
                            move |arg| {
                                plan.execute(arg).map_err(|e| e.raise(&span))
                            },
                        )))
                    };
                    Expr::Literal(t.clone(), value)
                }
                Err(err) => {
                    *self.error.borrow_mut() = Some(err);
                    e.clone()
                }
            };
        }
        map_deep(e, &|c| self.exp(c))
    }

    /// Prepares `(c, f)`: translates `f` for connection `c`, and
    /// returns the plan.
    fn prepare(
        &self,
        connection: &Expr,
        f: &Expr,
    ) -> Result<PreparedPlan, SparkError> {
        // A query with no step but the scan -- `from e in emps` -- has
        // no relational node in it, because it is the collection it
        // reads; such a query is the collection.
        let body = match f {
            Expr::Fn(_, matches, _) if matches.len() == 1 => &matches[0].expr,
            _ => f,
        };
        let query = first_rel(f).or_else(|| {
            schema::element_type(&body.type_()).map(|_| body.clone())
        });
        let Some(query) = query else {
            // Phase 1 prepares a query and nothing else; a function
            // whose body is not relational has no plan. Raised as the
            // translator raises its own refusals, so that every reason a
            // plan cannot be prepared reads alike.
            return Err(SparkError::new(
                "UNSUPPORTED",
                "Spark cannot do a function that is not a query",
            ));
        };
        // The plan runs on the connection it was prepared for, so the
        // plan holds it; and it computes a value of the type the
        // program was typed against, so it holds that too.
        let Some(Val::Connection(connection)) = self.value_of(connection)
        else {
            return Err(SparkError::new(
                "UNSUPPORTED",
                "Spark cannot see which connection to prepare on; bind the \
                 connection to a name",
            ));
        };
        let result_type = match peel_type(&f.type_()) {
            Type::Fn(_, result) => Rc::clone(result),
            t => Rc::new(t.clone()),
        };
        let (element_type, collection) =
            match schema::element_type(&result_type) {
                Some(e) => (e, true),
                None => (result_type, false),
            };
        PreparedPlan::new(
            connection,
            self.sourced(&query),
            parameters(f),
            element_type,
            collection,
        )
    }

    /// Replaces each collection a query reads with the value it
    /// denotes, so that the translator can see what it is.
    ///
    /// A query names its sources -- `spark.catalog.scott.emps`,
    /// `scott.emps`, `rates` -- and what crosses to Spark depends on
    /// what each one is, not on what it is called: a table of a
    /// connection's catalog is a table scan, and every other collection
    /// is rows to send. Only the environment knows which.
    ///
    /// A name the environment cannot value is left as it is -- a plan's
    /// own parameter, for one -- and the translator refuses what it
    /// cannot read.
    fn sourced(&self, e: &Expr) -> Expr {
        if let Expr::Apply(t, f, _, _) = e
            && matches!(f.as_ref(), Expr::RecordSelector(..))
            && schema::element_type(t).is_some()
            && let Some(value) = self.value_of(e)
        {
            return Expr::Literal(t.clone(), value);
        }
        map_deep(e, &|c| self.sourced(c))
    }

    /// Returns the value of an expression that names one -- a name, or
    /// a field of a value -- or `None` if it is not one the environment
    /// can value.
    fn value_of(&self, e: &Expr) -> Option<Val> {
        match e {
            Expr::Literal(_, v) => Some(v.clone()),
            Expr::Identifier(_, name) => {
                if let Some(v) = self.bindings.get(name) {
                    return Some(v.clone());
                }
                match lookup(name)? {
                    BuiltIn::Record(r) => {
                        LIBRARY.with(|lib| lib.structure_val(r).cloned())
                    }
                    BuiltIn::Fn(_) => None,
                }
            }
            Expr::Apply(_, f, arg, _) => {
                let Expr::RecordSelector(_, slot) = f.as_ref() else {
                    return None;
                };
                let value = self.value_of(arg)?;
                match value {
                    Val::Progressive(tv) => {
                        let fields = schema::fields(&arg.type_())?;
                        let (name, _) = fields.get(*slot)?;
                        // A table of a catalog is the table itself,
                        // which knows the name Spark has for it, and is
                        // not read.
                        if let Ok(Some((child, _))) = tv.child(name)
                            && child.qualified_name().is_some()
                        {
                            return Some(Val::Progressive(child));
                        }
                        tv.field_value(name).ok().flatten()
                    }
                    Val::List(items) => items.get(*slot).cloned(),
                    _ => None,
                }
            }
            _ => None,
        }
    }
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

/// Returns the first relational node in `e`, in pre-order: the
/// outermost query.
fn first_rel(e: &Expr) -> Option<Expr> {
    if matches!(e, Expr::Rel(..)) {
        return Some(e.clone());
    }
    let found = RefCell::new(None);
    let _ = map_deep(e, &|c| {
        if found.borrow().is_none() {
            *found.borrow_mut() = first_rel(c);
        }
        c.clone()
    });
    found.into_inner()
}

/// Returns the parameters of the function a plan was prepared from, in
/// the order the argument holds them; empty if it has none.
///
/// A function of unit has a parameter in the tree but none to pass,
/// which is the same thing as none. A function of several arguments is
/// a function of a tuple, so its parameters are the names that the
/// tuple pattern binds, and the argument's components answer to them
/// one for one.
fn parameters(f: &Expr) -> Vec<String> {
    let Expr::Fn(_, matches, _) = f else {
        return Vec::new();
    };
    let [m] = matches.as_slice() else {
        return vec!["$arg".to_string()];
    };
    let is_unit = |t: &Type| {
        matches!(peel_type(t), Type::Primitive(PrimitiveType::Unit))
            || matches!(peel_type(t), Type::Tuple(ts) if ts.is_empty())
    };
    match &m.pat {
        p if is_unit(&p.type_()) => Vec::new(),
        Pat::Identifier(_, name) => vec![name.clone()],
        Pat::Tuple(_, pats) => {
            let names: Option<Vec<String>> = pats
                .iter()
                .map(|p| match p {
                    Pat::Identifier(_, name) => Some(name.clone()),
                    _ => None,
                })
                .collect();
            names.unwrap_or_else(|| vec!["$arg".to_string()])
        }
        _ => vec!["$arg".to_string()],
    }
}

// End prepare.rs
