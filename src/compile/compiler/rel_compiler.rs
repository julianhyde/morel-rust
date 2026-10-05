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

//! Compiles a relational tree to a chain of row sinks. It is morel-java's
//! `RelCompiler`.
//!
//! A node's element travels to the node above it bound to the name by
//! which that node reads it, in one of two ways. A scan writes each
//! element into a slot, and so does a node that counts its rows (the
//! count, beside its row) and a group (its outputs, then the record of
//! them). Every other node defers its element: it hands up an expression
//! over the slots below -- a filter its row, a projection its expression,
//! a join the tuple of its inputs' components -- and the node above
//! substitutes that expression for the name before it compiles its own.
//! So a filter above a join reads the joined slots directly, and a
//! projection below a filter costs nothing until something reads a field.
//! A node that needs its element as a value -- a set operator -- puts it
//! in a slot with a yield.
//!
//! morel-java pushes each slot onto a stack as it goes. Here a slot is a
//! variable of the frame, which is sized before anything is compiled, so
//! every name this compiler writes is one the frame already has: a node's
//! row and position, and the names [`rel_out_name`] and [`group_out_name`]
//! derive from them.

use super::{Compiler, Context};
use crate::compile::core::{
    Expr, JoinKind, JoinRows, ORDINAL, Pat, Rel, Row, element_type,
    group_out_name, join_part_name, rel_out_name,
};
use crate::compile::free_finder::free_names_in;
use crate::compile::rel_lowerer::{component_count, field_at, substitute_name};
use crate::compile::replacer::substitute;
use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::code::Code;
use crate::eval::comparator::comparator_for;
use crate::eval::row_sink::{
    BuildJoinRowSink, CollectRowSink, ExceptRowSink, GroupRowSink,
    IntersectRowSink, OrderRowSink, OrdinalRowSink, RowSinkFactory,
    ScanRowSink, SkipRowSink, TakeRowSink, UnionRowSink, WhereRowSink,
    YieldRowSink,
};
use crate::eval::val::Val;
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;

/// Returns whether a tree is one this compiler compiles; the kernel
/// lowers one that is not to the step list that runs it.
///
/// Not: a join whose condition and right input both read its position,
/// which morel-java counts in two places and the scan here in one; a
/// `right` or `full` join whose right input reads the left row, which
/// morel-java does not allow either; and a position left for an enclosing
/// query that a step list carries.
pub(crate) fn compilable(e: &Expr) -> bool {
    if free_names_in(e).contains(ORDINAL) {
        return false;
    }
    fn node_ok(e: &Expr) -> bool {
        let Expr::Rel(_, rel) = e else {
            return true;
        };
        if let Rel::Join(kind, rows, condition, _, right) = rel.as_ref() {
            let reads = |e: &Expr, name: &str| free_names_in(e).contains(name);
            let ordinal = rows.ordinal.as_deref();
            let condition_ordinal =
                ordinal.is_some_and(|o| reads(condition, o));
            let right_ordinal = ordinal.is_some_and(|o| reads(right, o));
            if condition_ordinal && right_ordinal {
                return false;
            }
            // A `right` or `full` join reads its right input once, before
            // any left element, so the input cannot read one, and its sink
            // counts no pairs.
            if matches!(kind, JoinKind::Right | JoinKind::Full)
                && (reads(right, &rows.left)
                    || right_ordinal
                    || condition_ordinal)
            {
                return false;
            }
        }
        rel.inputs().into_iter().all(node_ok)
    }
    node_ok(e)
}

/// The name a node's element arrives under, and the element's type.
#[derive(Clone)]
struct Target {
    name: String,
    t: Rc<Type>,
}

impl Target {
    fn id(&self) -> Expr {
        Expr::Identifier(self.t.clone(), self.name.clone())
    }
}

/// The slots a query has written, and the elements deferred as
/// expressions over them.
#[derive(Clone, Default)]
struct Slots {
    names: Vec<String>,
    deferred: BTreeMap<String, Expr>,
}

impl Slots {
    /// Adds a slot.
    fn push(&self, name: &str) -> Slots {
        let mut s = self.clone();
        s.names.push(name.to_string());
        s
    }

    /// Defers a name to an expression over the slots.
    fn defer(&self, name: &str, e: &Expr) -> Slots {
        let mut s = self.clone();
        s.deferred.insert(name.to_string(), self.resolve(e));
        s
    }

    /// Returns whether a name is in a slot, rather than deferred.
    fn is_slot(&self, name: &str) -> bool {
        self.names.iter().any(|n| n == name)
            && !self.deferred.contains_key(name)
    }

    /// Replaces each deferred name in an expression with its expression,
    /// reading a field of a tuple built there off the tuple.
    fn resolve(&self, e: &Expr) -> Expr {
        self.deferred
            .iter()
            .fold(e.clone(), |e, (name, x)| substitute_name(&e, name, x))
    }
}

/// Builds the sink that reads a node's slots.
type Sink<'n> =
    dyn FnOnce(&mut Compiler, &Context, Slots) -> Option<RowSinkFactory> + 'n;

/// What consumes a node's element.
enum Next<'n> {
    /// The root, which collects the elements.
    Collect(Target),
    /// A node above, which builds the sink that reads the slots.
    Then(Box<Sink<'n>>),
}

impl Next<'_> {
    fn sink(
        self,
        c: &mut Compiler,
        cx: &Context,
        slots: Slots,
    ) -> Option<RowSinkFactory> {
        match self {
            Next::Collect(target) => {
                let code = c.code(cx, &slots, &target.id());
                Some(RowSinkFactory::new(move || {
                    Box::new(CollectRowSink::new(code.clone()))
                }))
            }
            Next::Then(f) => f(c, cx, slots),
        }
    }
}

fn then<'n>(
    f: impl FnOnce(&mut Compiler, &Context, Slots) -> Option<RowSinkFactory> + 'n,
) -> Next<'n> {
    Next::Then(Box::new(f))
}

/// The type of a node's element.
fn elem(e: &Expr) -> Rc<Type> {
    element_type(&e.type_()).unwrap_or_else(|| e.type_())
}

impl Compiler<'_> {
    /// Compiles a tree to code that evaluates it to a collection.
    pub(super) fn compile_rel(&mut self, cx: &Context, tree: &Expr) -> Code {
        let target = Target {
            name: rel_out_name(tree),
            t: elem(tree),
        };
        let factory = self
            .stream(cx, tree, target.clone(), Next::Collect(target))
            .unwrap_or_else(|| panic!("cannot compile tree {}", tree));
        Code::FromRowSink(factory)
    }

    /// Compiles an expression over the slots.
    fn code(&mut self, cx: &Context, slots: &Slots, e: &Expr) -> Code {
        self.compile_expr(cx, None, &slots.resolve(e))
    }

    fn slot(cx: &Context, name: &str) -> Option<usize> {
        cx.frame_def.try_var_index(name)
    }

    fn slot_indexes(cx: &Context, slots: &Slots) -> Option<Vec<usize>> {
        slots.names.iter().map(|n| Self::slot(cx, n)).collect()
    }

    /// Compiles a node so that its element arrives bound to `target`,
    /// and hands the slots to `next`.
    fn stream(
        &mut self,
        cx: &Context,
        node: &Expr,
        target: Target,
        next: Next<'_>,
    ) -> Option<RowSinkFactory> {
        let Expr::Rel(_, rel) = node else {
            return self.scan(cx, node, &target, next);
        };
        match rel.as_ref() {
            // lint: sort until '#}' where '##Rel::'
            Rel::Except(distinct, inputs) => {
                self.set_op(cx, SetOp::Except, *distinct, inputs, target, next)
            }
            Rel::Filter(row, input, condition) => {
                let row_target = Target {
                    name: row.name.clone(),
                    t: elem(input),
                };
                let row_id = row_target.id();
                self.stream(
                    cx,
                    input,
                    row_target,
                    then(move |c, cx, slots| {
                        c.with_ordinal(
                            cx,
                            slots,
                            row,
                            then(move |c, cx, slots| {
                                let code = c.code(cx, &slots, condition);
                                let nf = next.sink(
                                    c,
                                    cx,
                                    slots.defer(&target.name, &row_id),
                                )?;
                                Some(RowSinkFactory::new(move || {
                                    Box::new(WhereRowSink::new(
                                        code.clone(),
                                        nf.create(),
                                    ))
                                }))
                            }),
                        )
                    }),
                )
            }
            Rel::Group(row, input, keys, aggregates) => {
                let row_target = Target {
                    name: row.name.clone(),
                    t: elem(input),
                };
                let t = elem(node);
                self.stream(
                    cx,
                    input,
                    row_target,
                    then(move |c, cx, slots| {
                        c.with_ordinal(
                            cx,
                            slots,
                            row,
                            then(move |c, cx, slots| {
                                c.group(
                                    cx, &slots, row, keys, aggregates, &t,
                                    &target, next,
                                )
                            }),
                        )
                    }),
                )
            }
            Rel::Intersect(distinct, inputs) => self.set_op(
                cx,
                SetOp::Intersect,
                *distinct,
                inputs,
                target,
                next,
            ),
            Rel::Join(kind, rows, condition, left, right) => {
                self.join(cx, *kind, rows, condition, left, right, target, next)
            }
            Rel::Project(row, input, e) => {
                let row_target = Target {
                    name: row.name.clone(),
                    t: elem(input),
                };
                self.stream(
                    cx,
                    input,
                    row_target,
                    then(move |c, cx, slots| {
                        c.with_ordinal(
                            cx,
                            slots,
                            row,
                            then(move |c, cx, slots| {
                                next.sink(c, cx, slots.defer(&target.name, e))
                            }),
                        )
                    }),
                )
            }
            Rel::Skip(input, count) => {
                let count_code = self.compile_expr(cx, None, count);
                self.stream(
                    cx,
                    input,
                    target,
                    then(move |c, cx, slots| {
                        let nf = next.sink(c, cx, slots)?;
                        Some(RowSinkFactory::new(move || {
                            Box::new(SkipRowSink::new(
                                count_code.clone(),
                                nf.create(),
                            ))
                        }))
                    }),
                )
            }
            Rel::Sort(row, input, key) => {
                let row_target = Target {
                    name: row.name.clone(),
                    t: elem(input),
                };
                let row_id = row_target.id();
                self.stream(
                    cx,
                    input,
                    row_target,
                    then(move |c, cx, slots| {
                        c.with_ordinal(
                            cx,
                            slots,
                            row,
                            then(move |c, cx, slots| {
                                let key_code = c.code(cx, &slots, key);
                                let comparator = comparator_for(&key.type_());
                                // The sink writes every slot back before it
                                // emits a row, so the downstream reads what
                                // it reads here.
                                let in_slots = Self::slot_indexes(cx, &slots)?;
                                let nf = next.sink(
                                    c,
                                    cx,
                                    slots.defer(&target.name, &row_id),
                                )?;
                                Some(RowSinkFactory::new(move || {
                                    Box::new(OrderRowSink::new(
                                        key_code.clone(),
                                        comparator.clone(),
                                        in_slots.clone(),
                                        nf.create(),
                                    ))
                                }))
                            }),
                        )
                    }),
                )
            }
            Rel::Take(input, count) => {
                let count_code = self.compile_expr(cx, None, count);
                self.stream(
                    cx,
                    input,
                    target,
                    then(move |c, cx, slots| {
                        let nf = next.sink(c, cx, slots)?;
                        Some(RowSinkFactory::new(move || {
                            Box::new(TakeRowSink::new(
                                count_code.clone(),
                                nf.create(),
                            ))
                        }))
                    }),
                )
            }
            Rel::Union(distinct, inputs) => {
                self.set_op(cx, SetOp::Union, *distinct, inputs, target, next)
            }
            // A change of type only; ordered and unordered streams have
            // the same representation.
            Rel::Unorder(input) => self.stream(cx, input, target, next),
        }
    }

    /// Scans a collection, one slot per element.
    fn scan(
        &mut self,
        cx: &Context,
        collection: &Expr,
        target: &Target,
        next: Next<'_>,
    ) -> Option<RowSinkFactory> {
        let code = if let Expr::Extent(_, span, names) = collection {
            // The resolver reports an unbounded scan before anything is
            // compiled, except in a function's body, which grounding may
            // yet reach where the function is called.
            let name = names.first().map_or("_", String::as_str);
            Code::RaiseIllegalArgument(
                format!("pattern '{}' is not grounded", name),
                span.clone(),
            )
        } else {
            self.compile_expr(cx, None, collection)
        };
        Self::slot(cx, &target.name)?;
        let pat_code = self.compile_pat(
            cx,
            &Pat::Identifier(target.t.clone(), target.name.clone()),
        );
        let nf = next.sink(self, cx, Slots::default().push(&target.name))?;
        let condition = true_code();
        Some(RowSinkFactory::new(move || {
            Box::new(ScanRowSink::new_with_join(
                pat_code.clone(),
                code.clone(),
                condition.clone(),
                nf.create(),
                vec![],
                None,
            ))
        }))
    }

    /// Writes a node's position beside its row, if the node counts its
    /// rows, and hands the slots to `next`.
    fn with_ordinal(
        &mut self,
        cx: &Context,
        slots: Slots,
        row: &Row,
        next: Next<'_>,
    ) -> Option<RowSinkFactory> {
        let Some(ordinal) = &row.ordinal else {
            return next.sink(self, cx, slots);
        };
        let slot = Self::slot(cx, ordinal)?;
        let nf = next.sink(self, cx, slots.push(ordinal))?;
        Some(RowSinkFactory::new(move || {
            Box::new(OrdinalRowSink::new(slot, nf.create()))
        }))
    }

    /// Makes `target` the one slot, if it is not that already, and hands
    /// the slots to `next`.
    fn materialize(
        &mut self,
        cx: &Context,
        slots: Slots,
        target: &Target,
        next: Next<'_>,
    ) -> Option<RowSinkFactory> {
        if slots.names.len() == 1 && slots.is_slot(&target.name) {
            return next.sink(self, cx, slots);
        }
        let code = self.code(cx, &slots, &target.id());
        self.emit(cx, code, target, next)
    }

    /// Writes a value into the slot of `target`, or collects it where the
    /// root is what reads it.
    fn emit(
        &mut self,
        cx: &Context,
        code: Code,
        target: &Target,
        next: Next<'_>,
    ) -> Option<RowSinkFactory> {
        if let Next::Collect(_) = next {
            return Some(RowSinkFactory::new(move || {
                Box::new(CollectRowSink::new(code.clone()))
            }));
        }
        let slot = Self::slot(cx, &target.name)?;
        let nf = next.sink(self, cx, Slots::default().push(&target.name))?;
        Some(RowSinkFactory::new(move || {
            Box::new(YieldRowSink::new_scalar(
                code.clone(),
                slot,
                None,
                nf.create(),
            ))
        }))
    }

    /// Compiles a group: the keys and aggregates go into slots of their
    /// own, and the element, the record of them, into `target`'s.
    #[allow(clippy::too_many_arguments)]
    fn group(
        &mut self,
        cx: &Context,
        slots: &Slots,
        row: &Row,
        keys: &[(Label, Expr)],
        aggregates: &[(Label, Expr)],
        t: &Rc<Type>,
        target: &Target,
        next: Next<'_>,
    ) -> Option<RowSinkFactory> {
        let mut key_codes: Vec<Code> =
            keys.iter().map(|(_, e)| self.code(cx, slots, e)).collect();
        // One key is its value, and several a tuple of them; a tuple of
        // one is not a list at all.
        let key_is_record = key_codes.len() != 1;
        let key_code = if key_is_record {
            Code::new_tuple(&key_codes)
        } else {
            key_codes.remove(0)
        };
        let key_slots: Vec<usize> = keys
            .iter()
            .map(|(label, _)| Self::slot(cx, &group_out_name(row, label)))
            .collect::<Option<_>>()?;
        // The sink keeps each row's slots, and writes them back when it
        // evaluates an aggregate's argument.
        let scan_slots = Self::slot_indexes(cx, slots)?;
        let (aggregate_code, agg_slots) = if aggregates.is_empty() {
            (None, vec![])
        } else {
            let fields: BTreeMap<Label, Rc<Type>> = aggregates
                .iter()
                .map(|(label, e)| (label.clone(), e.type_()))
                .collect();
            // An aggregate may read a key by its label, which the sink
            // has written to the key's slot by the time it evaluates the
            // aggregate.
            let key_names: HashMap<String, Expr> = keys
                .iter()
                .map(|(label, e)| {
                    let name = group_out_name(row, label);
                    (label.to_string(), Expr::Identifier(e.type_(), name))
                })
                .collect();
            let aggregate =
                |e: &Expr| substitute(&slots.resolve(e), &key_names);
            let record = match aggregates {
                [(_, e)] => aggregate(e),
                _ => Expr::Tuple(
                    Rc::new(Type::Record(false, fields)),
                    aggregates.iter().map(|(_, e)| aggregate(e)).collect(),
                ),
            };
            let mut cx2 = cx.clone();
            cx2.compute_scan_slots = scan_slots.clone();
            let code = self.compile_expr(&cx2, None, &record);
            let agg_slots: Vec<usize> = aggregates
                .iter()
                .map(|(label, _)| Self::slot(cx, &group_out_name(row, label)))
                .collect::<Option<_>>()?;
            (Some(code), agg_slots)
        };
        let agg_is_record = aggregates.len() != 1;
        let elements_slot = Self::slot(cx, "elements");
        // The element is the record of the outputs, or the one output
        // where there is one.
        let outputs: Vec<&Label> = keys
            .iter()
            .chain(aggregates.iter())
            .map(|(l, _)| l)
            .collect();
        // The element is the record of the outputs where its type is that
        // record, even of one; otherwise the one output's value, or unit.
        let is_record = matches!(t.as_ref(), Type::Record(_, fields)
            if fields.len() == outputs.len()
                && outputs.iter().all(|l| fields.contains_key(*l)));
        let element = if is_record {
            let Type::Record(_, fields) = t.as_ref() else {
                unreachable!()
            };
            let codes = fields
                .keys()
                .map(|label| {
                    Self::slot(cx, &group_out_name(row, label))
                        .map(|s| Code::new_get_local(&cx.frame_def, s))
                })
                .collect::<Option<Vec<_>>>()?;
            Code::new_tuple(&codes)
        } else if let [label] = outputs.as_slice() {
            Code::new_get_local(
                &cx.frame_def,
                Self::slot(cx, &group_out_name(row, label))?,
            )
        } else {
            Code::new_constant(&Type::Primitive(PrimitiveType::Unit), Val::Unit)
        };
        let nf = self.emit(cx, element, target, next)?;
        Some(RowSinkFactory::new(move || {
            Box::new(GroupRowSink::new(
                key_code.clone(),
                aggregate_code.clone(),
                elements_slot,
                agg_slots.clone(),
                agg_is_record,
                scan_slots.clone(),
                key_slots.clone(),
                key_is_record,
                nf.create(),
            ))
        }))
    }

    /// Compiles a set operator, whose first input's element is the one
    /// slot.
    fn set_op(
        &mut self,
        cx: &Context,
        op: SetOp,
        distinct: bool,
        inputs: &[Expr],
        target: Target,
        next: Next<'_>,
    ) -> Option<RowSinkFactory> {
        let (first, others) = inputs.split_first()?;
        let target2 = target.clone();
        self.stream(
            cx,
            first,
            target,
            then(move |c, cx, slots| {
                c.materialize(
                    cx,
                    slots,
                    &target2,
                    then(move |c, cx, slots| {
                        let codes: Vec<Code> = others
                            .iter()
                            .map(|e| c.code(cx, &slots, e))
                            .collect();
                        let slot_list = Self::slot_indexes(cx, &slots)?;
                        let nf = next.sink(c, cx, slots)?;
                        Some(match op {
                            SetOp::Except => RowSinkFactory::new(move || {
                                Box::new(ExceptRowSink::new(
                                    slot_list.clone(),
                                    false,
                                    distinct,
                                    codes.clone(),
                                    nf.create(),
                                ))
                            }),
                            SetOp::Intersect => {
                                RowSinkFactory::new(move || {
                                    Box::new(IntersectRowSink::new(
                                        slot_list.clone(),
                                        false,
                                        distinct,
                                        codes.clone(),
                                        nf.create(),
                                    ))
                                })
                            }
                            SetOp::Union => {
                                // A distinct union is a union whose rows are
                                // then grouped on the whole element.
                                let nf = if distinct {
                                    distinct_on(cx, &slot_list, nf)
                                } else {
                                    nf
                                };
                                RowSinkFactory::new(move || {
                                    Box::new(UnionRowSink::new(
                                        slot_list.clone(),
                                        false,
                                        codes.clone(),
                                        nf.create(),
                                    ))
                                })
                            }
                        })
                    }),
                )
            }),
        )
    }

    /// Compiles a join: the left input streams, and the right input is
    /// scanned once for each left element -- re-evaluated, where it reads
    /// the left row.
    #[allow(clippy::too_many_arguments)]
    fn join(
        &mut self,
        cx: &Context,
        kind: JoinKind,
        rows: &JoinRows,
        condition: &Expr,
        left: &Expr,
        right: &Expr,
        target: Target,
        next: Next<'_>,
    ) -> Option<RowSinkFactory> {
        let reads = |e: &Expr| {
            rows.ordinal
                .as_ref()
                .is_some_and(|o| free_names_in(e).contains(o))
        };
        let right_reads_ordinal = reads(right);
        let condition_reads_ordinal = reads(condition);
        let left_target = Target {
            name: rows.left.clone(),
            t: elem(left),
        };
        let left_id = left_target.id();
        self.stream(
            cx,
            left,
            left_target,
            then(move |c, cx, slots| {
                // The right input sees the left element's position.
                let counted = Row {
                    name: rows.left.clone(),
                    ordinal: if right_reads_ordinal {
                        rows.ordinal.clone()
                    } else {
                        None
                    },
                };
                c.with_ordinal(
                    cx,
                    slots,
                    &counted,
                    then(move |c, cx, slots| {
                        let join = Join {
                            kind,
                            rows,
                            condition,
                            right,
                            condition_reads_ordinal,
                        };
                        c.join2(
                            cx, &slots, &join, left, &left_id, &target, next,
                        )
                    }),
                )
            }),
        )
    }

    /// Compiles a join whose left element has arrived. A `right` or
    /// `full` join's sink wraps each slot of its left input in `option`,
    /// and the element has one `option` per component; so the components
    /// are laid out one to a slot, and the left row read as the tuple of
    /// them.
    #[allow(clippy::too_many_arguments)]
    fn join2(
        &mut self,
        cx: &Context,
        slots: &Slots,
        join: &Join<'_>,
        left: &Expr,
        left_id: &Expr,
        target: &Target,
        next: Next<'_>,
    ) -> Option<RowSinkFactory> {
        let parts = components(left, left_id);
        let build = matches!(join.kind, JoinKind::Right | JoinKind::Full);
        if !build
            || (parts.len() == 1
                && slots.names.len() == 1
                && slots.is_slot(&join.rows.left))
        {
            return self.join3(cx, slots, join, parts, target, next);
        }
        let names: Vec<String> = (0..parts.len())
            .map(|i| join_part_name(&join.rows.left, i))
            .collect();
        let codes: Vec<Code> =
            parts.iter().map(|e| self.code(cx, slots, e)).collect();
        let ids: Vec<Expr> = names
            .iter()
            .zip(&parts)
            .map(|(n, e)| Expr::Identifier(e.type_(), n.clone()))
            .collect();
        let mut laid_out = Slots::default();
        for name in &names {
            laid_out = laid_out.push(name);
        }
        let laid_out = laid_out.defer(&join.rows.left, &tuple_of(ids.clone()));
        let slot_list: Vec<usize> = names
            .iter()
            .map(|n| Self::slot(cx, n))
            .collect::<Option<_>>()?;
        let nf = self.join3(cx, &laid_out, join, ids, target, next)?;
        Some(
            if let ([code], [slot]) = (codes.as_slice(), slot_list.as_slice()) {
                let (code, slot) = (code.clone(), *slot);
                RowSinkFactory::new(move || {
                    Box::new(YieldRowSink::new_scalar(
                        code.clone(),
                        slot,
                        None,
                        nf.create(),
                    ))
                })
            } else {
                let code = Code::new_tuple(&codes);
                RowSinkFactory::new(move || {
                    Box::new(YieldRowSink::new_record(
                        code.clone(),
                        slot_list.clone(),
                        nf.create(),
                    ))
                })
            },
        )
    }

    /// Compiles the scan of a join's right input, once for each left
    /// element: re-evaluated where it reads the left row, and read once
    /// before any left element by a `right` or `full` join, which
    /// cannot.
    fn join3(
        &mut self,
        cx: &Context,
        slots: &Slots,
        join: &Join<'_>,
        left_parts: Vec<Expr>,
        target: &Target,
        next: Next<'_>,
    ) -> Option<RowSinkFactory> {
        let rows = join.rows;
        let right = join.right;
        let right_elem = elem(right);
        let right_code = self.code(cx, slots, right);
        let count = component_count(right);
        let right_optional =
            matches!(join.kind, JoinKind::Left | JoinKind::Full);
        // As for the left side: a sink that wraps each slot it writes
        // in `option` writes one per component.
        let (pat, right_parts, names) = if right_optional && count > 1 {
            let Type::Tuple(types) = right_elem.as_ref() else {
                return None;
            };
            let names: Vec<String> =
                (0..count).map(|i| join_part_name(&rows.right, i)).collect();
            let pats = names
                .iter()
                .zip(types)
                .map(|(n, t)| Pat::Identifier(t.clone(), n.clone()))
                .collect();
            let ids = names
                .iter()
                .zip(types)
                .map(|(n, t)| Expr::Identifier(t.clone(), n.clone()))
                .collect();
            (Pat::Tuple(right_elem.clone(), pats), ids, names)
        } else {
            let id = Expr::Identifier(right_elem.clone(), rows.right.clone());
            (
                Pat::Identifier(right_elem.clone(), rows.right.clone()),
                components(right, &id),
                vec![rows.right.clone()],
            )
        };
        let pat_code = self.compile_pat(cx, &pat);
        let mut scanned = slots.clone();
        for name in &names {
            scanned = scanned.push(name);
        }
        if names.len() > 1 {
            scanned =
                scanned.defer(&rows.right, &tuple_of(right_parts.clone()));
        }
        let source_slots: Vec<usize> = names
            .iter()
            .map(|n| Self::slot(cx, n))
            .collect::<Option<_>>()?;
        // The condition runs once per candidate pair, and sees the
        // pair's position, which the scan counts.
        let condition_slot = if join.condition_reads_ordinal {
            Some(Self::slot(cx, rows.ordinal.as_ref()?)?)
        } else {
            None
        };
        let condition_code = self.code(cx, &scanned, join.condition);
        // The element is the inputs' components in order.
        let mut parts = left_parts;
        parts.extend(right_parts);
        let element = tuple_of(parts);
        let nf = next.sink(self, cx, scanned.defer(&target.name, &element))?;
        if matches!(join.kind, JoinKind::Right | JoinKind::Full) {
            let left_slots = Self::slot_indexes(cx, slots)?;
            let full = join.kind == JoinKind::Full;
            return Some(RowSinkFactory::new(move || {
                Box::new(BuildJoinRowSink::new(
                    pat_code.clone(),
                    right_code.clone(),
                    condition_code.clone(),
                    nf.create(),
                    left_slots.clone(),
                    source_slots.clone(),
                    full,
                    full,
                ))
            }));
        }
        let optional = if right_optional { source_slots } else { vec![] };
        Some(RowSinkFactory::new(move || {
            Box::new(ScanRowSink::new_with_join(
                pat_code.clone(),
                right_code.clone(),
                condition_code.clone(),
                nf.create(),
                optional.clone(),
                condition_slot,
            ))
        }))
    }
}

/// The parts of a join that its compilation reads once its left element
/// has arrived.
struct Join<'a> {
    kind: JoinKind,
    rows: &'a JoinRows,
    condition: &'a Expr,
    right: &'a Expr,
    condition_reads_ordinal: bool,
}

/// A tuple of expressions, or the one expression where there is one.
fn tuple_of(mut parts: Vec<Expr>) -> Expr {
    if parts.len() == 1 {
        return parts.remove(0);
    }
    Expr::Tuple(
        Rc::new(Type::Tuple(parts.iter().map(Expr::type_).collect())),
        parts,
    )
}

/// A set operator.
#[derive(Copy, Clone)]
enum SetOp {
    Except,
    Intersect,
    Union,
}

/// The components of a node's element, read out of an expression for it:
/// a join's are its inputs', and any other node's is the element.
fn components(node: &Expr, e: &Expr) -> Vec<Expr> {
    let n = component_count(node);
    if n == 1 {
        return vec![e.clone()];
    }
    (0..n).map(|i| field_at(e, i)).collect()
}

/// Wraps a sink so that it sees each distinct row once: a group whose
/// key is the whole row and which has no aggregates.
fn distinct_on(
    cx: &Context,
    slots: &[usize],
    nf: RowSinkFactory,
) -> RowSinkFactory {
    let key_code = if let [slot] = slots {
        Code::new_get_local(&cx.frame_def, *slot)
    } else {
        Code::new_tuple(
            &slots
                .iter()
                .map(|s| Code::new_get_local(&cx.frame_def, *s))
                .collect::<Vec<_>>(),
        )
    };
    let slots = slots.to_vec();
    let is_record = slots.len() > 1;
    RowSinkFactory::new(move || {
        Box::new(GroupRowSink::new(
            key_code.clone(),
            None,
            None,
            vec![],
            false,
            slots.clone(),
            slots.clone(),
            is_record,
            nf.create(),
        ))
    })
}

fn true_code() -> Code {
    Code::new_constant(&Type::Primitive(PrimitiveType::Bool), Val::Bool(true))
}
