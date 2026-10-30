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

//! Walks a declaration and grounds each query that scans something
//! unbounded, on its tree (see [`rel_expander`]), with the functions in
//! scope at the query to hand to the generators that invert a call.

use crate::compile::core::{
    Binding, Decl, Expr, Match, Pat, Step, StepEnv, StepKind, ValBind,
};
use crate::compile::library::BuiltInFunction;
use crate::compile::rel_expander;
use crate::compile::rel_lowerer;
use crate::compile::span::Span;
use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::val::Val;
use std::collections::{BTreeSet, HashMap};
use std::rc::Rc;

/// Map of let-bound function name → (parameter pattern, body
/// expression). Populated as `expand_decl` walks down through
/// nested `Let` expressions so that `maybe_function` can inline a
/// known function's body when it sees a constraint of the form
/// `f arg`.
pub type FnEnv = HashMap<String, (Pat, Expr)>;

/// What `finite_extent` needs to enumerate the values of a
/// `Type::Data(name, _)`: each datatype's constructor names in
/// declaration order, and the argument type of any constructor that
/// takes one. A constructor absent from `arg_types` is nullary, and
/// is a value in itself.
#[derive(Clone, Debug, Default)]
pub struct DatatypeMap {
    /// Datatype name → its constructor names, in declaration order.
    pub constructors: HashMap<String, Vec<String>>,
    /// Constructor name → the type of its argument, for those that
    /// take one.
    pub arg_types: HashMap<String, Type>,
}

impl DatatypeMap {
    pub fn new(
        constructors: &HashMap<String, Vec<String>>,
        arg_types: &HashMap<String, Type>,
    ) -> Self {
        DatatypeMap {
            constructors: constructors.clone(),
            arg_types: arg_types.clone(),
        }
    }
}

/// Tree-walking pass that grounds every query it encounters, with a
/// `FnEnv` populated from enclosing `let val rec ... = fn p => body`
/// bindings. This
/// Entry point used after the resolver finishes, so that
/// `maybe_function` can inline let-bound predicates that the
/// per-query passes inside `resolve_query` couldn't see.
///
/// Seeds the inlining environment with cross-statement function
/// bindings the session has accumulated from earlier `fun` / `val`
/// decls so predicate inversion can inline a function declared in
/// a previous shell statement. `rec_session_fns` carries the
/// pre-expander function bodies for recursive-predicate inversion,
/// while `session_fns` keeps post-expander bodies for use by
/// `inline_tuple_fn_calls_in_where`.
pub fn expand_decl_with_session_rec(
    decl: Decl,
    datatypes: &DatatypeMap,
    session_fns: &FnEnv,
    rec_session_fns: &FnEnv,
) -> Decl {
    walk_decl_rec(decl, session_fns, rec_session_fns, datatypes)
}

/// Walks a Core decl and records any single-arm `fn p => body`
/// value-bindings into `env`. Mirrors `collect_fn_bindings` but
/// is exposed for the shell, which tracks session-level fn
/// definitions for cross-statement predicate inversion.
pub fn collect_session_fn_bindings(decl: &Decl, env: &mut FnEnv) {
    collect_fn_bindings(decl, env);
}

/// Adds every identifier-name bound by `pat` to `out`. Used to
/// extend the "outer scope" set as we walk into a `Fn` body or
/// a `Case` arm.
fn collect_pat_names(pat: &Pat, out: &mut BTreeSet<String>) {
    let mut bs: Vec<Binding> = Vec::new();
    Binding::collect_bindings(pat, &mut bs);
    for b in bs {
        out.insert(b.id.name);
    }
}

/// Adds every identifier-name bound by `decl`'s left-hand
/// patterns to `out`. Used to extend the "outer scope" set as
/// we walk into a `Let` body.
fn collect_decl_pat_names(decl: &Decl, out: &mut BTreeSet<String>) {
    use std::slice::from_ref;
    let binds: &[ValBind] = match decl {
        Decl::NonRecVal(b) => from_ref(b.as_ref()),
        Decl::RecVal(binds) => binds.as_slice(),
        _ => return,
    };
    for b in binds {
        collect_pat_names(&b.pat, out);
    }
}

fn walk_decl_rec(
    decl: Decl,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> Decl {
    walk_decl_with_scope(decl, env, rec_env, datatypes, &BTreeSet::new())
}

fn walk_decl_with_scope(
    decl: Decl,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
) -> Decl {
    match decl {
        Decl::NonRecVal(b) => {
            let mut b2 = (*b).clone();
            b2.expr = walk_expr_with_scope(
                b2.expr,
                env,
                rec_env,
                datatypes,
                outer_scope,
            );
            Decl::NonRecVal(Box::new(b2))
        }
        Decl::RecVal(binds) => {
            let mut new_binds = Vec::with_capacity(binds.len());
            for mut b in binds {
                b.expr = walk_expr_with_scope(
                    b.expr,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                );
                new_binds.push(b);
            }
            Decl::RecVal(new_binds)
        }
        other => other,
    }
}

/// Rewrites every `Relational.nonEmpty` over a query, anywhere in
/// an expression, as a query whose last step tests for existence.
///
/// The two say the same thing. The call is what `Core` carries, and
/// the step is what the generators read in a function's body.
fn as_exists_steps(e: Expr) -> Expr {
    if let Expr::Apply(_, f, a, _) = &e
        && matches!(
            f.as_ref(),
            Expr::Literal(_, Val::Fn(BuiltInFunction::RelationalNonEmpty))
        )
        && matches!(a.as_ref(), Expr::From(_, _))
    {
        let Expr::Apply(_, _, a, _) = e else {
            unreachable!("matched above");
        };
        return exists_step(as_exists_steps(*a));
    }
    match e {
        // lint: sort until '#}' where '##Expr::'
        Expr::Aggregate(t, a, b, s) => Expr::Aggregate(
            t,
            Box::new(as_exists_steps(*a)),
            Box::new(as_exists_steps(*b)),
            s,
        ),
        Expr::Apply(t, f, a, s) => Expr::Apply(
            t,
            Box::new(as_exists_steps(*f)),
            Box::new(as_exists_steps(*a)),
            s,
        ),
        Expr::Case(t, subject, arms, s) => Expr::Case(
            t,
            Box::new(as_exists_steps(*subject)),
            arms.into_iter().map(as_exists_steps_arm).collect(),
            s,
        ),
        Expr::Fn(t, arms, s) => {
            Expr::Fn(t, arms.into_iter().map(as_exists_steps_arm).collect(), s)
        }
        Expr::From(t, steps) => {
            Expr::From(t, steps.into_iter().map(as_exists_steps_step).collect())
        }
        Expr::Let(t, decls, body) => Expr::Let(
            t,
            decls.into_iter().map(as_exists_steps_decl).collect(),
            Box::new(as_exists_steps(*body)),
        ),
        Expr::List(t, items) => {
            Expr::List(t, items.into_iter().map(as_exists_steps).collect())
        }
        Expr::Raise(t, a, s) => {
            Expr::Raise(t, Box::new(as_exists_steps(*a)), s)
        }
        Expr::Tuple(t, items) => {
            Expr::Tuple(t, items.into_iter().map(as_exists_steps).collect())
        }
        other => other,
    }
}

fn as_exists_steps_arm(m: Match) -> Match {
    Match {
        pat: m.pat,
        expr: as_exists_steps(m.expr),
    }
}

fn as_exists_steps_decl(d: Decl) -> Decl {
    match d {
        Decl::NonRecVal(b) => {
            let mut bind = *b;
            bind.expr = as_exists_steps(bind.expr);
            Decl::NonRecVal(Box::new(bind))
        }
        Decl::RecVal(binds) => Decl::RecVal(
            binds
                .into_iter()
                .map(|mut b| {
                    b.expr = as_exists_steps(b.expr);
                    b
                })
                .collect(),
        ),
        other => other,
    }
}

fn as_exists_steps_step(step: Step) -> Step {
    let each =
        |es: Vec<Expr>| es.into_iter().map(as_exists_steps).collect::<Vec<_>>();
    let kind = match step.kind {
        // lint: sort until '#}' where '##StepKind::'
        StepKind::Compute(e) => {
            StepKind::Compute(Box::new(as_exists_steps(*e)))
        }
        StepKind::Except(d, args) => StepKind::Except(d, each(args)),
        StepKind::Group(keys, aggs) => StepKind::Group(
            Box::new(as_exists_steps(*keys)),
            aggs.map(|a| Box::new(as_exists_steps(*a))),
        ),
        StepKind::Intersect(d, args) => StepKind::Intersect(d, each(args)),
        StepKind::Order(e) => StepKind::Order(Box::new(as_exists_steps(*e))),
        StepKind::Scan(pat, source, condition) => StepKind::Scan(
            pat,
            Box::new(as_exists_steps(*source)),
            condition.map(|c| Box::new(as_exists_steps(*c))),
        ),
        StepKind::Skip(e) => StepKind::Skip(Box::new(as_exists_steps(*e))),
        StepKind::Take(e) => StepKind::Take(Box::new(as_exists_steps(*e))),
        StepKind::Union(d, args) => StepKind::Union(d, each(args)),
        StepKind::Where(e) => StepKind::Where(Box::new(as_exists_steps(*e))),
        StepKind::Yield(e) => StepKind::Yield(Box::new(as_exists_steps(*e))),
        other => other,
    };
    Step { kind, ..step }
}

/// Returns the query whose rows a query ending in a step that tests for
/// existence counts: its steps but the last, typed as the environment
/// the last leaves them says.
fn exists_query(e: &Expr) -> Option<Expr> {
    let Expr::From(_, steps) = e else {
        return None;
    };
    let (last, rest) = steps.split_last()?;
    if !matches!(last.kind, StepKind::Exists) || rest.is_empty() {
        return None;
    }
    let env = &rest.last()?.env;
    let elem = match env.bindings.as_slice() {
        [] => Rc::new(Type::Primitive(PrimitiveType::Unit)),
        [b] if env.atom => b.type_.clone(),
        bindings => Rc::new(Type::Record(
            false,
            bindings
                .iter()
                .map(|b| (Label::String(b.id.name.clone()), b.type_.clone()))
                .collect(),
        )),
    };
    let t = if env.ordered {
        Type::List(elem)
    } else {
        Type::Bag(elem)
    };
    Some(Expr::From(Rc::new(t), rest.to_vec()))
}

/// The functions in scope, the recursive ones among them, for the tree
/// grounder, which inverts a call of either. A body is as it was written
/// where that is to hand: grounding may have rewritten the other,
/// folding the step predicate a closure is recognized by into a scan.
fn with_recursive(env: &FnEnv, rec_env: &FnEnv) -> FnEnv {
    let mut all = rec_env.clone();
    for (name, f) in env {
        all.entry(name.clone()).or_insert_with(|| f.clone());
    }
    all
}

/// Rewrites each query that ends in a step testing for existence as
/// `Relational.nonEmpty` over the rest of it.
fn as_non_empty(e: Expr) -> Expr {
    if let Some(query) = exists_query(&e) {
        return non_empty(query);
    }
    match e {
        Expr::From(..) => e,
        e => rel_lowerer::map_children(&e, &|x| as_non_empty(x.clone())),
    }
}

/// Returns `Relational.nonEmpty` over a query.
fn non_empty(query: Expr) -> Expr {
    let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let fn_t = Rc::new(Type::Fn(query.type_(), bool_t.clone()));
    Expr::Apply(
        bool_t,
        Box::new(Expr::Literal(
            fn_t,
            Val::Fn(BuiltInFunction::RelationalNonEmpty),
        )),
        Box::new(query),
        Span::new(""),
    )
}

/// Returns a query with a step that tests for existence, which is
/// how the step list says what a call over the query says.
fn exists_step(query: Expr) -> Expr {
    let Expr::From(t, mut steps) = query else {
        return query;
    };
    let env = match steps.last() {
        Some(step) => step.env.clone(),
        None => StepEnv::new(Vec::new(), false, true),
    };
    steps.push(Step::new(StepKind::Exists, env));
    Expr::From(t, steps)
}

fn walk_expr_with_scope(
    expr: Expr,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
) -> Expr {
    match expr {
        Expr::Let(t, decls, body) => {
            // Extend the environment with single-arg `fn` bindings
            // before recursing into the body. Also extend
            // outer_scope with the let-binding's pat names so
            // record-elem strategies treat them as runtime-stable.
            let mut env2 = env.clone();
            let mut rec_env2 = rec_env.clone();
            let mut scope2 = outer_scope.clone();
            for d in &decls {
                // Pre-expander bodies into both maps. `env2` is the
                // post-expander map for `inline_tuple_fn_calls_in_where`;
                // because Let-bound bodies haven't been walked yet at
                // this point, both maps temporarily hold the same
                // pre-expander bodies. (Phase 2 only fires for
                // self-recursive shapes that don't get inlined.)
                collect_fn_bindings(d, &mut env2);
                collect_fn_bindings(d, &mut rec_env2);
                collect_decl_pat_names(d, &mut scope2);
            }
            let new_decls: Vec<Decl> = decls
                .into_iter()
                .map(|d| {
                    walk_decl_with_scope(
                        d, &env2, &rec_env2, datatypes, &scope2,
                    )
                })
                .collect();
            let new_body = Box::new(walk_expr_with_scope(
                *body, &env2, &rec_env2, datatypes, &scope2,
            ));
            Expr::Let(t, new_decls, new_body)
        }
        e if rel_lowerer::is_query_tree(&e) => {
            // A query the resolver built as a tree: grounded on it if
            // the tree grounder can, and otherwise carried by the step
            // list it lowers to, as a query the resolver built as steps
            // is.
            if !rel_expander::has_unbounded_leaf(&e) {
                return walk_tree_children(
                    e,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                );
            }
            if let Some(grounded) = rel_expander::ground(
                &e,
                datatypes,
                &with_recursive(env, rec_env),
            ) {
                return walk_query_steps(grounded, env, rec_env, datatypes);
            }
            // A tree the grounder declines is left as it is; an
            // unbounded leaf that survives is reported when the query
            // is checked.
            walk_tree_children(e, env, rec_env, datatypes, outer_scope)
        }
        Expr::From(_, _) => {
            // Grounded on its tree first, which is where a scan
            // whose pattern is not a single variable can be
            // grounded, and where the order the leaves are scanned
            // in is the tree's to decide. The query is grounded
            // before what its steps hold, so that a constraint that
            // reads a nested query reads it as written.
            if let Some(grounded) = rel_expander::ground(
                &expr,
                datatypes,
                &with_recursive(env, rec_env),
            ) {
                return walk_query_steps(grounded, env, rec_env, datatypes);
            }
            walk_query_steps(expr, env, rec_env, datatypes)
        }
        Expr::Apply(t, f, a, span)
            if rel_lowerer::is_query_tree(&a)
                && matches!(
                    f.as_ref(),
                    Expr::Literal(
                        _,
                        Val::Fn(BuiltInFunction::RelationalNonEmpty)
                    )
                ) =>
        {
            // Whether a query built as a tree has a row: the rows are
            // counted and not read.
            if !rel_expander::has_unbounded_leaf(&a) {
                let a = walk_tree_children(
                    *a,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                );
                return Expr::Apply(t, f, Box::new(a), span);
            }
            if let Some(grounded) = rel_expander::ground_counted(
                &a,
                datatypes,
                &with_recursive(env, rec_env),
            ) {
                let a = walk_query_steps(grounded, env, rec_env, datatypes);
                return Expr::Apply(t, f, Box::new(a), span);
            }
            let a =
                walk_tree_children(*a, env, rec_env, datatypes, outer_scope);
            Expr::Apply(t, f, Box::new(a), span)
        }
        Expr::Apply(t, f, a, span)
            if matches!(a.as_ref(), Expr::From(_, _))
                && matches!(
                    f.as_ref(),
                    Expr::Literal(
                        _,
                        Val::Fn(BuiltInFunction::RelationalNonEmpty)
                    )
                ) =>
        {
            // Whether a query has a row: the rows are counted and
            // not read, so a side that nothing constrains need not
            // be enumerated and a variable that nothing bounds need
            // not be bounded.
            if let Some(grounded) = rel_expander::ground_counted(
                &a,
                datatypes,
                &with_recursive(env, rec_env),
            ) {
                let a = walk_query_steps(grounded, env, rec_env, datatypes);
                return Expr::Apply(t, f, Box::new(a), span);
            }
            let a = walk_query_steps(*a, env, rec_env, datatypes);
            Expr::Apply(t, f, Box::new(a), span)
        }
        Expr::Apply(t, f, a, span) => {
            // Higher-order predicate inversion: inline a call to a
            // non-recursive let-bound function whose body contains
            // an unresolved `Extent`. After substitution, the body's
            // from is walked normally and its inversion has access
            // to the concrete arg (e.g. `enumerate isClerk` becomes
            // `from r where isClerk r`, whose `isClerk r` grounds
            // `r` via the body's `elem` clause).
            //
            // Self-recursive functions are skipped — inlining them
            // would loop forever, and the dedicated iterate-inversion
            // path handles their self-call shapes.
            if let Expr::Identifier(_, fn_name) = f.as_ref()
                && let Some((param_pat, body)) = env.get(fn_name)
                && let Pat::Identifier(_, param_name) = param_pat
                && body_has_extent(body)
                && !contains_self_call(body, fn_name)
            {
                use crate::compile::replacer::substitute;
                let mut subst: HashMap<String, Expr> = HashMap::new();
                subst.insert(param_name.clone(), (*a).clone());
                // The body says whether a query has a row the way the
                // step list does; put in place of a call, it is whether
                // the query has one, which its tree may ground.
                let inlined = as_non_empty(substitute(body, &subst));
                return walk_expr_with_scope(
                    inlined,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                );
            }
            Expr::Apply(
                t,
                Box::new(walk_expr_with_scope(
                    *f,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                )),
                Box::new(walk_expr_with_scope(
                    *a,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                )),
                span,
            )
        }
        Expr::Case(t, subject, arms, span) => Expr::Case(
            t,
            Box::new(walk_expr_with_scope(
                *subject,
                env,
                rec_env,
                datatypes,
                outer_scope,
            )),
            arms.into_iter()
                .map(|m| {
                    let mut scope2 = outer_scope.clone();
                    collect_pat_names(&m.pat, &mut scope2);
                    Match {
                        pat: m.pat,
                        expr: walk_expr_with_scope(
                            m.expr, env, rec_env, datatypes, &scope2,
                        ),
                    }
                })
                .collect(),
            span,
        ),
        Expr::Fn(t, arms, span) => Expr::Fn(
            t,
            arms.into_iter()
                .map(|m| {
                    let mut scope2 = outer_scope.clone();
                    collect_pat_names(&m.pat, &mut scope2);
                    Match {
                        pat: m.pat,
                        // A query in a function body is grounded
                        // here, with the parameters bound, for a call
                        // that is not inlined; and again where a call
                        // is, from the body as written, where what
                        // bounds its variables may be the argument.
                        expr: walk_expr_with_scope(
                            m.expr, env, rec_env, datatypes, &scope2,
                        ),
                    }
                })
                .collect(),
            span,
        ),
        Expr::Tuple(t, items) => Expr::Tuple(
            t,
            items
                .into_iter()
                .map(|e| {
                    walk_expr_with_scope(
                        e,
                        env,
                        rec_env,
                        datatypes,
                        outer_scope,
                    )
                })
                .collect(),
        ),
        Expr::List(t, items) => Expr::List(
            t,
            items
                .into_iter()
                .map(|e| {
                    walk_expr_with_scope(
                        e,
                        env,
                        rec_env,
                        datatypes,
                        outer_scope,
                    )
                })
                .collect(),
        ),
        Expr::Aggregate(t, e1, e2, s) => Expr::Aggregate(
            t,
            Box::new(walk_expr_with_scope(
                *e1,
                env,
                rec_env,
                datatypes,
                outer_scope,
            )),
            Box::new(walk_expr_with_scope(
                *e2,
                env,
                rec_env,
                datatypes,
                outer_scope,
            )),
            s,
        ),
        other => other,
    }
}

/// Walks the expressions of a grounded tree, grounding the queries they
/// hold in turn; `only` over a tree is the tree's value.
fn walk_tree_children(
    e: Expr,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
    outer_scope: &BTreeSet<String>,
) -> Expr {
    match e {
        // An input is a tree, grounded with this one; an expression is
        // walked, which grounds the queries it holds.
        Expr::Rel(t, rel) => Expr::Rel(
            t,
            Box::new(rel.map_children(&|e| match e {
                Expr::Rel(..) => walk_tree_children(
                    e.clone(),
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                ),
                // A query that tests for existence -- a function's body,
                // put in place of a call that a grounded tree filters by
                // -- is whether the rest of it has a row, which its tree
                // may ground.
                _ => walk_expr_with_scope(
                    as_non_empty(e.clone()),
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                ),
            })),
        ),
        // `only` over a tree.
        Expr::Apply(t, f, a, span) if matches!(a.as_ref(), Expr::Rel(..)) => {
            Expr::Apply(
                t,
                f,
                Box::new(walk_tree_children(
                    *a,
                    env,
                    rec_env,
                    datatypes,
                    outer_scope,
                )),
                span,
            )
        }
        // What grounding left in the tree's place -- a closure's
        // iteration, say -- holds queries of its own.
        other => walk_expr_with_scope(
            as_non_empty(other),
            env,
            rec_env,
            datatypes,
            outer_scope,
        ),
    }
}

/// Walk inside a `From`/`Exists`/`Forall`'s steps so that
/// expressions embedded in `Where`, `Yield`, and other step kinds
/// get the same treatment. The query's outer wrapper is recreated.
fn walk_query_steps(
    expr: Expr,
    env: &FnEnv,
    rec_env: &FnEnv,
    datatypes: &DatatypeMap,
) -> Expr {
    let outer_scope = BTreeSet::new();
    let (t, steps) = match expr {
        Expr::From(t, s) => (t, s),
        other => {
            return walk_tree_children(
                other,
                env,
                rec_env,
                datatypes,
                &outer_scope,
            );
        }
    };
    let new_steps: Vec<Step> = steps
        .into_iter()
        .map(|s| {
            let new_kind = match s.kind {
                StepKind::Scan(p, source, cond) => StepKind::Scan(
                    p,
                    Box::new(walk_expr_with_scope(
                        *source,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )),
                    cond.map(|c| {
                        Box::new(walk_expr_with_scope(
                            *c,
                            env,
                            rec_env,
                            datatypes,
                            &outer_scope,
                        ))
                    }),
                ),
                StepKind::Where(c) => {
                    StepKind::Where(Box::new(walk_expr_with_scope(
                        *c,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )))
                }
                StepKind::Yield(e) => {
                    StepKind::Yield(Box::new(walk_expr_with_scope(
                        *e,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )))
                }
                StepKind::Order(e) => {
                    StepKind::Order(Box::new(walk_expr_with_scope(
                        *e,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )))
                }
                StepKind::Compute(e) => {
                    StepKind::Compute(Box::new(walk_expr_with_scope(
                        *e,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )))
                }
                StepKind::Group(k, a) => StepKind::Group(
                    Box::new(walk_expr_with_scope(
                        *k,
                        env,
                        rec_env,
                        datatypes,
                        &outer_scope,
                    )),
                    a.map(|e| {
                        Box::new(walk_expr_with_scope(
                            *e,
                            env,
                            rec_env,
                            datatypes,
                            &outer_scope,
                        ))
                    }),
                ),
                other => other,
            };
            Step::with_join(s.join_type, new_kind, s.env)
        })
        .collect();
    Expr::From(t, new_steps)
}

/// Inspects a `Decl` and, for every value-binding whose RHS is a
/// single-arm `fn p => body`, records the binding in `env`. We
/// cap at one parameter for now — multi-clause functions and
/// curried definitions can be added in a later phase.
fn collect_fn_bindings(decl: &Decl, env: &mut FnEnv) {
    use std::slice::from_ref;
    let binds: &[ValBind] = match decl {
        Decl::NonRecVal(b) => from_ref(b.as_ref()),
        Decl::RecVal(binds) => binds.as_slice(),
        _ => return,
    };
    for b in binds {
        if let Pat::Identifier(_, name) = &b.pat
            && let Expr::Fn(_, arms, _) = &b.expr
            && arms.len() == 1
        {
            let Match { pat, expr } = &arms[0];
            // A body reaches the step list's passes by being put in
            // place of a call, so it says what it says in the shape
            // those passes read.
            env.insert(
                name.clone(),
                (
                    pat.clone(),
                    as_exists_steps(rel_lowerer::steps_within(expr)),
                ),
            );
        }
    }
}

/// Returns true if `expr` contains an `Extent` placeholder anywhere
/// in its tree. Used to identify let-bound function bodies that
/// can't compile on their own (because they reference unbounded
/// domain variables) and need to be inlined at call sites for
/// predicate inversion to ground the variables.
fn body_has_extent(expr: &Expr) -> bool {
    match expr {
        Expr::Extent(..) => true,
        Expr::Rel(_, rel) => rel.children().iter().any(|e| body_has_extent(e)),
        Expr::Aggregate(_, e1, e2, _) => {
            body_has_extent(e1) || body_has_extent(e2)
        }
        Expr::Apply(_, f, a, _) => body_has_extent(f) || body_has_extent(a),
        Expr::Case(_, subj, arms, _) => {
            body_has_extent(subj)
                || arms.iter().any(|m| body_has_extent(&m.expr))
        }
        Expr::From(_, steps) => steps.iter().any(step_has_extent),
        Expr::Fn(_, arms, _) => arms.iter().any(|m| body_has_extent(&m.expr)),
        Expr::Let(_, _, body) => body_has_extent(body),
        Expr::List(_, items) | Expr::Tuple(_, items) => {
            items.iter().any(body_has_extent)
        }
        Expr::Raise(_, e, _) => body_has_extent(e),
        Expr::Current(_)
        | Expr::Identifier(_, _)
        | Expr::Literal(_, _)
        | Expr::Ordinal(_)
        | Expr::RecordSelector(_, _) => false,
    }
}

fn step_has_extent(s: &Step) -> bool {
    match &s.kind {
        StepKind::Compute(e)
        | StepKind::Order(e)
        | StepKind::Skip(e)
        | StepKind::Take(e)
        | StepKind::Where(e)
        | StepKind::Yield(e) => body_has_extent(e),
        StepKind::Group(k, agg) => {
            body_has_extent(k) || agg.as_deref().is_some_and(body_has_extent)
        }
        StepKind::Scan(_, src, cond) => {
            matches!(src.as_ref(), Expr::Extent(..))
                || body_has_extent(src)
                || cond.as_deref().is_some_and(body_has_extent)
        }
        StepKind::Except(_, exprs)
        | StepKind::Intersect(_, exprs)
        | StepKind::Union(_, exprs) => exprs.iter().any(body_has_extent),
        StepKind::Distinct | StepKind::Exists | StepKind::Unorder => false,
    }
}

/// Returns true if `body` contains an `Apply(Var(name), _)`
/// anywhere — i.e. a call to the named function.
pub(crate) fn contains_self_call(body: &Expr, name: &str) -> bool {
    fn walk(e: &Expr, name: &str) -> bool {
        if let Expr::Apply(_, f, _, _) = e
            && let Expr::Identifier(_, n) = f.as_ref()
            && n == name
        {
            return true;
        }
        match e {
            Expr::Apply(_, f, a, _) => walk(f, name) || walk(a, name),
            Expr::Tuple(_, items) | Expr::List(_, items) => {
                items.iter().any(|i| walk(i, name))
            }
            Expr::Case(_, subj, arms, _) => {
                walk(subj, name) || arms.iter().any(|m| walk(&m.expr, name))
            }
            Expr::Fn(_, arms, _) => arms.iter().any(|m| walk(&m.expr, name)),
            Expr::Let(_, _, body) => walk(body, name),
            Expr::From(_, steps) => steps.iter().any(|s| match &s.kind {
                StepKind::Scan(_, src, cond) => {
                    walk(src, name)
                        || cond.as_ref().is_some_and(|c| walk(c, name))
                }
                StepKind::Where(c)
                | StepKind::Yield(c)
                | StepKind::Order(c)
                | StepKind::Compute(c)
                | StepKind::Skip(c)
                | StepKind::Take(c) => walk(c, name),
                StepKind::Group(k, agg) => {
                    walk(k, name) || agg.as_ref().is_some_and(|a| walk(a, name))
                }
                _ => false,
            }),
            Expr::Aggregate(_, l, r, _) => walk(l, name) || walk(r, name),
            _ => false,
        }
    }
    walk(body, name)
}

/// Builds the `Relational.iterate seed updateFn` AST. The element
/// type of the result is `(x_t, y_t)` (a 2-tuple). If
/// `seed_label_order` is `Some(labels)`, the seed collection's
/// elements are records and we wrap with a projection
/// `from r in seed yield (r.<labels[0]>, r.<labels[1]>)` to
/// convert them to tuples.
pub(crate) fn build_iterate_ast(
    x_t: &Type,
    y_t: &Type,
    _z_t: &Type,
    seed_expr: Expr,
    seed_label_order: Option<Vec<String>>,
) -> Expr {
    use crate::compile::type_env::Id;
    // Result element type: (x_t, y_t).
    let elem_t = Type::Tuple(vec![Rc::new(x_t.clone()), Rc::new(y_t.clone())]);
    let bool_t = Type::Primitive(PrimitiveType::Bool);
    // Result collection type: Bag(elem_t). (We don't preserve list
    // ordering in Phase 1; iterate's runtime uses Val::List as its
    // representation regardless.)
    let coll_t = Type::Bag(Rc::new(elem_t.clone()));
    // Convert seed from records to tuples if needed.
    let typed_seed: Expr = match seed_label_order {
        None => {
            // Seed is already collection of tuples — just unify the
            // type to Bag(elem_t) if it was List(elem_t).
            seed_expr
        }
        Some(labels) => {
            // Wrap as `from r in seed yield (r.label0, r.label1)`.
            let r_name = "__tc_r";
            // Determine seed's element type.
            let seed_t = seed_expr.type_();
            let seed_elem_t = match seed_t.as_ref() {
                Type::List(t) | Type::Bag(t) => (**t).clone(),
                _ => return Expr::List(Rc::new(coll_t), Vec::new()),
            };
            let r_pat =
                Pat::Identifier(Rc::new(seed_elem_t.clone()), r_name.into());
            let r_id =
                Expr::Identifier(Rc::new(seed_elem_t.clone()), r_name.into());
            let mut tuple_items: Vec<Expr> = Vec::new();
            for (i, lbl) in labels.iter().enumerate() {
                let field_t = match &seed_elem_t {
                    Type::Record(_, fs) => {
                        let key = Label::String(lbl.clone());
                        match fs.get(&key) {
                            Some(t) => t.clone(),
                            None => {
                                return Expr::List(Rc::new(coll_t), Vec::new());
                            }
                        }
                    }
                    _ => return Expr::List(Rc::new(coll_t), Vec::new()),
                };
                let sel_t = Rc::new(Type::Fn(
                    Rc::new(seed_elem_t.clone()),
                    field_t.clone(),
                ));
                let sel = Expr::RecordSelector(sel_t, i);
                tuple_items.push(Expr::Apply(
                    field_t.clone(),
                    Box::new(sel),
                    Box::new(r_id.clone()),
                    Span::new(""),
                ));
            }
            let tuple_expr = Expr::Tuple(Rc::new(elem_t.clone()), tuple_items);
            let r_binding =
                Binding::new(Id::new(r_name, 0), Rc::new(seed_elem_t.clone()));
            let scan_env =
                StepEnv::new(vec![r_binding.clone()], true, seed_t.is_list());
            let yield_env = StepEnv::new(
                vec![Binding::new(
                    Id::new("current", 0),
                    Rc::new(elem_t.clone()),
                )],
                true,
                seed_t.is_list(),
            );
            let inner_steps = vec![
                Step::new(
                    StepKind::Scan(
                        Box::new(r_pat),
                        Box::new(seed_expr.clone()),
                        None,
                    ),
                    scan_env,
                ),
                Step::new(StepKind::Yield(Box::new(tuple_expr)), yield_env),
            ];
            let inner_t = if seed_t.is_list() {
                Type::List(Rc::new(elem_t.clone()))
            } else {
                Type::Bag(Rc::new(elem_t.clone()))
            };
            Expr::From(Rc::new(inner_t), inner_steps)
        }
    };
    // Build the update fn: `fn (allP, newP) =>
    //   from (px, pz) in newP, (sz, sy) in seed_tuples
    //   where pz = sz yield (px, sy)`.
    let all_name = "__tc_all";
    let new_name = "__tc_new";
    let px_name = "__tc_px";
    let pz_name = "__tc_pz";
    let sz_name = "__tc_sz";
    let sy_name = "__tc_sy";
    let coll_t_box = Rc::new(coll_t.clone());
    let all_pat = Pat::Identifier(coll_t_box.clone(), all_name.to_string());
    let new_pat = Pat::Identifier(coll_t_box.clone(), new_name.to_string());
    let pair_pat = Pat::Tuple(
        Rc::new(Type::Tuple(vec![
            Rc::new(coll_t.clone()),
            Rc::new(coll_t.clone()),
        ])),
        vec![all_pat, new_pat.clone()],
    );
    let new_id = Expr::Identifier(coll_t_box.clone(), new_name.into());
    // (px, pz) in newP
    let prev_pat = Pat::Tuple(
        Rc::new(elem_t.clone()),
        vec![
            Pat::Identifier(Rc::new(x_t.clone()), px_name.into()),
            Pat::Identifier(Rc::new(y_t.clone()), pz_name.into()),
        ],
    );
    // (sz, sy) in typed_seed
    let step_pat = Pat::Tuple(
        Rc::new(elem_t.clone()),
        vec![
            Pat::Identifier(Rc::new(x_t.clone()), sz_name.into()),
            Pat::Identifier(Rc::new(y_t.clone()), sy_name.into()),
        ],
    );
    // Where pz = sz
    let pair_int_t = Rc::new(Type::Tuple(vec![
        Rc::new(y_t.clone()),
        Rc::new(x_t.clone()),
    ]));
    let eq_op = match y_t {
        Type::Primitive(PrimitiveType::Int) => BuiltInFunction::IntEq,
        Type::Primitive(PrimitiveType::String) => BuiltInFunction::StringEq,
        Type::Primitive(PrimitiveType::Char) => BuiltInFunction::CharEq,
        Type::Primitive(PrimitiveType::Bool) => BuiltInFunction::BoolEq,
        _ => BuiltInFunction::GEq,
    };
    let eq_fn_t =
        Rc::new(Type::Fn(pair_int_t.clone(), Rc::new(bool_t.clone())));
    let eq_lit = Expr::Literal(eq_fn_t, Val::Fn(eq_op));
    let pz_id = Expr::Identifier(Rc::new(y_t.clone()), pz_name.into());
    let sz_id = Expr::Identifier(Rc::new(x_t.clone()), sz_name.into());
    let eq_arg = Expr::Tuple(pair_int_t, vec![pz_id, sz_id]);
    let where_cond = Expr::Apply(
        Rc::new(bool_t.clone()),
        Box::new(eq_lit),
        Box::new(eq_arg),
        Span::new(""),
    );
    // Yield (px, sy)
    let px_id = Expr::Identifier(Rc::new(x_t.clone()), px_name.into());
    let sy_id = Expr::Identifier(Rc::new(y_t.clone()), sy_name.into());
    let yield_tuple = Expr::Tuple(Rc::new(elem_t.clone()), vec![px_id, sy_id]);
    // Build inner from steps with their environments.
    let scan1_bindings = vec![
        Binding::new(Id::new(px_name, 0), Rc::new(x_t.clone())),
        Binding::new(Id::new(pz_name, 0), Rc::new(y_t.clone())),
    ];
    let scan1_env = StepEnv::new(scan1_bindings.clone(), false, false);
    let scan2_bindings = {
        let mut b = scan1_bindings.clone();
        b.push(Binding::new(Id::new(sz_name, 0), Rc::new(x_t.clone())));
        b.push(Binding::new(Id::new(sy_name, 0), Rc::new(y_t.clone())));
        b
    };
    let scan2_env = StepEnv::new(scan2_bindings.clone(), false, false);
    let where_env = scan2_env.clone();
    let yield_env = StepEnv::new(
        vec![Binding::new(Id::new("current", 0), Rc::new(elem_t.clone()))],
        true,
        false,
    );
    let inner_steps = vec![
        Step::new(
            StepKind::Scan(Box::new(prev_pat), Box::new(new_id), None),
            scan1_env,
        ),
        Step::new(
            StepKind::Scan(
                Box::new(step_pat),
                Box::new(typed_seed.clone()),
                None,
            ),
            scan2_env,
        ),
        Step::new(StepKind::Where(Box::new(where_cond)), where_env),
        Step::new(StepKind::Yield(Box::new(yield_tuple)), yield_env),
    ];
    let inner_from = Expr::From(Rc::new(coll_t.clone()), inner_steps);
    let update_fn_t = Rc::new(Type::Fn(
        Rc::new(Type::Tuple(vec![
            Rc::new(coll_t.clone()),
            Rc::new(coll_t.clone()),
        ])),
        Rc::new(coll_t.clone()),
    ));
    let update_fn = Expr::Fn(
        update_fn_t.clone(),
        vec![Match {
            pat: pair_pat,
            expr: inner_from,
        }],
        Span::new(""),
    );
    // Build `Relational.iterate seed updateFn`.
    let iter_t = Rc::new(Type::Fn(
        Rc::new(coll_t.clone()),
        Rc::new(Type::Fn(
            Rc::new(update_fn_t.as_ref().clone()),
            Rc::new(coll_t.clone()),
        )),
    ));
    let iter_lit =
        Expr::Literal(iter_t, Val::Fn(BuiltInFunction::RelationalIterate));
    let after_seed_t = Rc::new(Type::Fn(
        Rc::new(update_fn_t.as_ref().clone()),
        Rc::new(coll_t.clone()),
    ));
    let with_seed = Expr::Apply(
        after_seed_t,
        Box::new(iter_lit),
        Box::new(typed_seed),
        Span::new(""),
    );
    Expr::Apply(
        Rc::new(coll_t.clone()),
        Box::new(with_seed),
        Box::new(update_fn),
        Span::new(""),
    )
}

/// If a scan iterates over a list of numeric literals, adds conjuncts
/// for the least and the greatest of them to `bounds`.
pub(crate) fn list_bounds(pat: &Pat, source: &Expr, bounds: &mut Vec<Expr>) {
    let Pat::Identifier(t, name) = pat else {
        return;
    };
    if !matches!(t.as_ref(), Type::Primitive(PrimitiveType::Int)) {
        return;
    }
    let values: Vec<i32> = match source {
        Expr::List(_, elements) => {
            let mut values = Vec::with_capacity(elements.len());
            for e in elements {
                match e {
                    Expr::Literal(_, Val::Int(i)) => values.push(*i),
                    // Not a constant, so we know nothing about the range.
                    _ => return,
                }
            }
            values
        }
        Expr::Literal(_, Val::List(items)) => {
            let mut values = Vec::with_capacity(items.len());
            for v in items.iter() {
                match v {
                    Val::Int(i) => values.push(*i),
                    _ => return,
                }
            }
            values
        }
        _ => return,
    };
    let (Some(min), Some(max)) =
        (values.iter().min().copied(), values.iter().max().copied())
    else {
        return;
    };
    bounds.push(int_bound(name, t, BuiltInFunction::IntGe, min));
    bounds.push(int_bound(name, t, BuiltInFunction::IntLe, max));
}

/// Builds the conjunct `name op value`.
fn int_bound(
    name: &str,
    t: &Rc<Type>,
    op: BuiltInFunction,
    value: i32,
) -> Expr {
    let int_t = Rc::new(Type::Primitive(PrimitiveType::Int));
    let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
    let pair_t = Rc::new(Type::Tuple(vec![int_t.clone(), int_t.clone()]));
    let fn_t = Rc::new(Type::Fn(pair_t.clone(), bool_t.clone()));
    Expr::Apply(
        bool_t,
        Box::new(Expr::Literal(fn_t, Val::Fn(op))),
        Box::new(Expr::Tuple(
            pair_t,
            vec![
                Expr::Identifier(t.clone(), name.to_string()),
                Expr::Literal(int_t, Val::Int(value)),
            ],
        )),
        Span::new(""),
    )
}

/// Structural equality between two Core expressions, ignoring spans.
/// Adequate for matching `where` conjuncts against generator
/// provenance — no alpha-renaming is needed because both sides come
/// from the same surface query.
pub(crate) fn expr_eq(a: &Expr, b: &Expr) -> bool {
    match (a, b) {
        (Expr::Literal(t1, v1), Expr::Literal(t2, v2)) => t1 == t2 && v1 == v2,
        (Expr::Identifier(t1, n1), Expr::Identifier(t2, n2)) => {
            t1 == t2 && n1 == n2
        }
        (Expr::RecordSelector(t1, s1), Expr::RecordSelector(t2, s2)) => {
            t1 == t2 && s1 == s2
        }
        (Expr::Apply(_, f1, a1, _), Expr::Apply(_, f2, a2, _)) => {
            expr_eq(f1, f2) && expr_eq(a1, a2)
        }
        (Expr::Tuple(_, xs), Expr::Tuple(_, ys))
        | (Expr::List(_, xs), Expr::List(_, ys)) => {
            xs.len() == ys.len()
                && xs.iter().zip(ys.iter()).all(|(x, y)| expr_eq(x, y))
        }
        (Expr::Extent(t1, ..), Expr::Extent(t2, ..)) => t1 == t2,
        _ => false,
    }
}

pub(crate) fn and_all(conjuncts: Vec<Expr>) -> Expr {
    let mut iter = conjuncts.into_iter();
    let first = iter.next().expect("at least one conjunct");
    iter.fold(first, |lhs, rhs| {
        let bool_t = Rc::new(Type::Primitive(PrimitiveType::Bool));
        let pair_t = Rc::new(Type::Tuple(vec![
            Rc::new((*bool_t).clone()),
            Rc::new((*bool_t).clone()),
        ]));
        let fn_t = Rc::new(Type::Fn(pair_t.clone(), bool_t.clone()));
        let fn_expr =
            Expr::Literal(fn_t, Val::Fn(BuiltInFunction::BoolAndAlso));
        let arg = Expr::Tuple(pair_t, vec![lhs, rhs]);
        Expr::Apply(bool_t, Box::new(fn_expr), Box::new(arg), Span::new(""))
    })
}
