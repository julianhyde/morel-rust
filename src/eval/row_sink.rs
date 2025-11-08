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

//! Row sink infrastructure for push-based query evaluation.
//!
//! This module provides an alternative to the pull-based query evaluation in
//! `Code::eval_from`. Instead of accumulating results in vectors, row sinks
//! form a pipeline where rows are pushed downstream.
//!
//! ## Architecture
//!
//! - **RowSink trait**: Defines the protocol (start, accept, result)
//! - **ScanRowSink**: Iterates collections and binds patterns
//! - **WhereRowSink**: Filters rows based on conditions
//! - **UnionRowSink**: Combines multiple collections
//! - **CollectRowSink**: Terminal sink that accumulates results
//!
//! ## Current Status (Phase 5 - Partial)
//!
//! The basic infrastructure is in place with four row sink implementations.
//! These sinks work with the existing Code evaluation model (eval_f0/eval_f1).
//!
//! ### TODO
//!
//! - Implement Join sink (separate from Scan)
//! - Complete Union sink deduplication logic
//! - Implement Group, Order, Skip, Take, Distinct sinks
//! - Integrate with FromBuilder to use sinks instead of QueryStep
//! - Add comprehensive tests

use crate::eval::code::{Code, EvalEnv, Frame};
use crate::eval::comparator::Comparator;
use crate::eval::val::Val;
use crate::shell::main::MorelError;
use std::sync::Arc;

/// Accepts rows produced by a supplier as part of a `from` step.
///
/// This is a push-based pipeline pattern where:
/// - `start(r, f)` initializes the sink before processing
/// - `accept(r, f)` processes one row from upstream
/// - `result(r, f)` retrieves the final results after all rows are processed
pub trait RowSink {
    /// Initialize the sink before processing rows.
    fn start(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError>;

    /// Accept and process a single row.
    fn accept(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError>;

    /// Return the final results after all rows have been processed.
    fn result(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError>;
}

/// Implementation of RowSink for a scan/join step.
///
/// Iterates over a collection, binds each element to a pattern,
/// evaluates an optional condition, and passes matching rows downstream.
pub struct ScanRowSink {
    pat_code: Code,
    collection_code: Code,
    condition_code: Code,
    row_sink: Box<dyn RowSink>,
}

impl ScanRowSink {
    pub fn new(
        pat_code: Code,
        collection_code: Code,
        condition_code: Code,
        row_sink: Box<dyn RowSink>,
    ) -> Self {
        Self {
            pat_code,
            collection_code,
            condition_code,
            row_sink,
        }
    }
}

impl RowSink for ScanRowSink {
    fn start(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        self.row_sink.start(r, f)
    }

    fn accept(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        // Evaluate the collection to iterate over in the current environment.
        // This is key for joins: each time accept() is called, we iterate
        // the collection in the context of the current row from upstream.
        //
        // For example, in
        //   "from e in emps, d in depts where e.deptno = d.deptno":
        // - The first ScanRowSink iterates over emps, binds each to 'e'.
        // - For each employee, the second ScanRowSink (downstream)
        //   evaluates depts (which may reference 'e') and iterates,
        //   binding each dept to 'd'.
        // - This creates a nested loop = cross join.
        let collection = self.collection_code.eval_f0(r, f)?;
        let items = collection.expect_list();

        // Iterate over elements in the collection.
        // For each element, we:
        // 1. Bind it to the pattern (updates frame slots in place).
        // 2. Evaluate the condition.
        // 3. If true, pass the current frame state downstream.
        for item in items {
            // Try to bind the pattern to this item.
            // BindSlot will write to f.vals[slot] = item.
            let matched = self.pat_code.eval_f1(r, f, item)?;
            if matched.expect_bool() {
                // Evaluate the condition in the extended environment.
                let condition = self.condition_code.eval_f0(r, f)?;
                if condition.expect_bool() {
                    // Pass this row downstream. The downstream sink will see
                    // all bindings from upstream plus our new binding.
                    self.row_sink.accept(r, f)?;
                }
            }
        }
        Ok(())
    }

    fn result(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError> {
        self.row_sink.result(r, f)
    }
}

/// Implementation of RowSink for a where/filter step.
///
/// Evaluates a boolean condition and only passes rows downstream if true.
pub struct WhereRowSink {
    filter_code: Code,
    row_sink: Box<dyn RowSink>,
}

impl WhereRowSink {
    pub fn new(filter_code: Code, row_sink: Box<dyn RowSink>) -> Self {
        Self {
            filter_code,
            row_sink,
        }
    }
}

impl RowSink for WhereRowSink {
    fn start(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        self.row_sink.start(r, f)
    }

    fn accept(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        let condition = self.filter_code.eval_f0(r, f)?;
        if condition.expect_bool() {
            self.row_sink.accept(r, f)?;
        }
        Ok(())
    }

    fn result(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError> {
        self.row_sink.result(r, f)
    }
}

/// Implementation of RowSink for a union step.
///
/// First accepts rows from upstream, then evaluates additional collections
/// and passes their elements downstream.
pub struct UnionRowSink {
    slot_count: usize,
    codes: Vec<Code>,
    row_sink: Box<dyn RowSink>,
}

impl UnionRowSink {
    pub fn new(
        slot_count: usize,
        codes: Vec<Code>,
        row_sink: Box<dyn RowSink>,
    ) -> Self {
        Self {
            slot_count,
            codes,
            row_sink,
        }
    }
}

impl RowSink for UnionRowSink {
    fn start(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        self.row_sink.start(r, f)
    }

    fn accept(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        self.row_sink.accept(r, f)
    }

    fn result(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError> {
        // Process additional collections from the union.
        let codes = self.codes.clone();
        for code in &codes {
            let collection = code.eval_f0(r, f)?;
            let items = collection.expect_list();
            for item in items {
                // Bind the item directly to frame slots (0..slot_count).
                if self.slot_count == 1 {
                    // Atom case: single binding at slot 0.
                    f.vals[0] = item.clone();
                } else {
                    // Tuple case: unpack tuple and bind to slots
                    // 0..slot_count.
                    let tuple_items = item.expect_list();
                    f.vals[..self.slot_count]
                        .clone_from_slice(&tuple_items[..self.slot_count]);
                }
                self.row_sink.accept(r, f)?;
            }
        }
        self.row_sink.result(r, f)
    }
}

/// Implementation of RowSink that collects results into a list.
///
/// This is the terminal sink at the end of the pipeline.
pub struct CollectRowSink {
    code: Code,
    list: Vec<Val>,
}

impl CollectRowSink {
    pub fn new(code: Code) -> Self {
        Self {
            code,
            list: Vec::new(),
        }
    }
}

impl RowSink for CollectRowSink {
    fn start(
        &mut self,
        _r: &mut EvalEnv,
        _f: &mut Frame,
    ) -> Result<(), MorelError> {
        self.list.clear();
        Ok(())
    }

    fn accept(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        let value = self.code.eval_f0(r, f)?;
        self.list.push(value);
        Ok(())
    }

    fn result(
        &mut self,
        _r: &mut EvalEnv,
        _f: &mut Frame,
    ) -> Result<Val, MorelError> {
        Ok(Val::List(self.list.clone()))
    }
}

/// Implementation of RowSink for an order step.
///
/// Accumulates all rows during accept(), then sorts them in result()
/// based on evaluating an order expression, and passes them downstream
/// in sorted order.
///
/// The comparator determines how order keys are compared, allowing for
/// different sort orders (ascending, descending, custom).
pub struct OrderRowSink {
    order_code: Code,
    comparator: Arc<dyn Comparator>,
    slot_count: usize,
    row_sink: Box<dyn RowSink>,
    rows: Vec<Val>,
}

impl OrderRowSink {
    pub fn new(
        order_code: Code,
        comparator: Arc<dyn Comparator>,
        slot_count: usize,
        row_sink: Box<dyn RowSink>,
    ) -> Self {
        Self {
            order_code,
            comparator,
            slot_count,
            row_sink,
            rows: Vec::new(),
        }
    }
}

impl RowSink for OrderRowSink {
    fn start(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        self.rows.clear();
        self.row_sink.start(r, f)
    }

    fn accept(
        &mut self,
        _r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        // Accumulate the current row for sorting later.
        // Extract the current row value from the frame.
        let row_val = if self.slot_count == 1 {
            // Atom case: single binding.
            f.vals[0].clone()
        } else {
            // Tuple case: create tuple from slots 0..slot_count.
            Val::List(f.vals[0..self.slot_count].to_vec())
        };
        self.rows.push(row_val);
        Ok(())
    }

    fn result(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError> {
        // Sort the accumulated rows.
        // We need to evaluate the order expression for each row and
        // compare. This is tricky because we need to restore the frame
        // state for each comparison.

        // Create tuples of (row_val, order_key) for stable sorting.
        let mut rows_with_keys: Vec<(Val, Val)> = Vec::new();

        for row in &self.rows {
            // Restore the frame to this row's state.
            if self.slot_count == 1 {
                f.vals[0] = row.clone();
            } else {
                let items = row.expect_list();
                f.vals[..self.slot_count]
                    .clone_from_slice(&items[..self.slot_count]);
            }

            // Evaluate the order expression for this row.
            let order_key = self.order_code.eval_f0(r, f)?;
            rows_with_keys.push((row.clone(), order_key));
        }

        // Sort by the order keys using the comparator.
        rows_with_keys.sort_by(|a, b| {
            // Compare the order keys (second element of the tuple).
            self.comparator.compare(&a.1, &b.1)
        });

        // Pass sorted rows downstream.
        for (row, _key) in rows_with_keys {
            // Restore the frame to this row.
            if self.slot_count == 1 {
                f.vals[0] = row;
            } else {
                let items = row.expect_list();
                f.vals[..self.slot_count]
                    .clone_from_slice(&items[..self.slot_count]);
            }
            self.row_sink.accept(r, f)?;
        }

        self.row_sink.result(r, f)
    }
}

/// Implementation of RowSink for a skip step.
///
/// Skips the first N rows and passes the rest downstream.
pub struct SkipRowSink {
    skip_code: Code,
    row_sink: Box<dyn RowSink>,
    remaining: i32,
}

impl SkipRowSink {
    pub fn new(skip_code: Code, row_sink: Box<dyn RowSink>) -> Self {
        Self {
            skip_code,
            row_sink,
            remaining: 0,
        }
    }
}

impl RowSink for SkipRowSink {
    fn start(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        // Evaluate the skip count.
        let skip_val = self.skip_code.eval_f0(r, f)?;
        self.remaining = skip_val.expect_int();
        self.row_sink.start(r, f)
    }

    fn accept(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        if self.remaining > 0 {
            self.remaining -= 1;
        } else {
            self.row_sink.accept(r, f)?;
        }
        Ok(())
    }

    fn result(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError> {
        self.row_sink.result(r, f)
    }
}

/// Implementation of RowSink for a take step.
///
/// Takes the first N rows and ignores the rest.
pub struct TakeRowSink {
    take_code: Code,
    row_sink: Box<dyn RowSink>,
    remaining: i32,
}

impl TakeRowSink {
    pub fn new(take_code: Code, row_sink: Box<dyn RowSink>) -> Self {
        Self {
            take_code,
            row_sink,
            remaining: 0,
        }
    }
}

impl RowSink for TakeRowSink {
    fn start(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        // Evaluate the take count.
        let take_val = self.take_code.eval_f0(r, f)?;
        self.remaining = take_val.expect_int();
        self.row_sink.start(r, f)
    }

    fn accept(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        if self.remaining > 0 {
            self.remaining -= 1;
            self.row_sink.accept(r, f)?;
        }
        Ok(())
    }

    fn result(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError> {
        self.row_sink.result(r, f)
    }
}

/// Implementation of RowSink for an intersect step.
///
/// Computes the intersection of the upstream collection with additional
/// collections.
pub struct IntersectRowSink {
    slot_count: usize,
    codes: Vec<Code>,
    row_sink: Box<dyn RowSink>,
    seen: Vec<Val>,
}

impl IntersectRowSink {
    pub fn new(
        slot_count: usize,
        codes: Vec<Code>,
        row_sink: Box<dyn RowSink>,
    ) -> Self {
        Self {
            slot_count,
            codes,
            row_sink,
            seen: Vec::new(),
        }
    }
}

impl RowSink for IntersectRowSink {
    fn start(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        self.seen.clear();
        self.row_sink.start(r, f)
    }

    fn accept(
        &mut self,
        _r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        // Collect the current row value.
        let row_val = if self.slot_count == 1 {
            f.vals[0].clone()
        } else {
            Val::List(f.vals[0..self.slot_count].to_vec())
        };
        self.seen.push(row_val);
        Ok(())
    }

    fn result(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError> {
        // For each collection on the right, we need to limit the
        // multiplicities. For example: [3,2,1,3,2] intersect [2,3,2,4]
        // should return [3,2,2] (3 once, 2 twice).
        let codes = self.codes.clone();
        for code in &codes {
            let collection = code.eval_f0(r, f)?;
            let items_slice = collection.expect_list();
            let mut items = items_slice.to_vec();

            // Filter seen to only include items that appear in the right
            // collection, respecting multiplicity. We consume from items
            // as we match.
            let mut new_seen = Vec::new();
            for val in &self.seen {
                // Find and consume one occurrence of val from items.
                if let Some(pos) = items.iter().position(|item| item == val) {
                    new_seen.push(val.clone());
                    items.remove(pos);
                }
            }
            self.seen = new_seen;
        }

        // Pass the remaining items downstream.
        for item in &self.seen {
            if self.slot_count == 1 {
                f.vals[0] = item.clone();
            } else {
                let tuple_items = item.expect_list();
                f.vals[..self.slot_count]
                    .clone_from_slice(&tuple_items[..self.slot_count]);
            }
            self.row_sink.accept(r, f)?;
        }
        self.row_sink.result(r, f)
    }
}

/// Implementation of RowSink for an except step.
///
/// Removes elements from the upstream collection that appear in additional
/// collections.
pub struct ExceptRowSink {
    slot_count: usize,
    codes: Vec<Code>,
    row_sink: Box<dyn RowSink>,
    seen: Vec<Val>,
}

impl ExceptRowSink {
    pub fn new(
        slot_count: usize,
        codes: Vec<Code>,
        row_sink: Box<dyn RowSink>,
    ) -> Self {
        Self {
            slot_count,
            codes,
            row_sink,
            seen: Vec::new(),
        }
    }
}

impl RowSink for ExceptRowSink {
    fn start(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        self.seen.clear();
        self.row_sink.start(r, f)
    }

    fn accept(
        &mut self,
        _r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        // Collect the current row value.
        let row_val = if self.slot_count == 1 {
            f.vals[0].clone()
        } else {
            Val::List(f.vals[0..self.slot_count].to_vec())
        };
        self.seen.push(row_val);
        Ok(())
    }

    fn result(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError> {
        // For except, we need to respect multiplicities. For example:
        // [1,2,3,4,5,1,5,1,2] except [2,4] should return [1,3,5,1,5,1,2]
        // (2 appears twice on left, once on right, so output once).
        let codes = self.codes.clone();
        for code in &codes {
            let collection = code.eval_f0(r, f)?;
            let items_slice = collection.expect_list();
            let mut items = items_slice.to_vec();

            // Remove items from seen that match items in the except list.
            // We consume from items as we match to respect multiplicity.
            let mut new_seen = Vec::new();
            for val in &self.seen {
                // Try to find and consume one occurrence from the exclude list.
                if let Some(pos) = items.iter().position(|item| item == val) {
                    items.remove(pos);
                    // Item was in except list, so skip it (don't add to
                    // new_seen).
                } else {
                    // Item was NOT in except list, so keep it.
                    new_seen.push(val.clone());
                }
            }
            self.seen = new_seen;
        }

        // Pass the remaining items downstream.
        for item in &self.seen {
            if self.slot_count == 1 {
                f.vals[0] = item.clone();
            } else {
                let tuple_items = item.expect_list();
                f.vals[..self.slot_count]
                    .clone_from_slice(&tuple_items[..self.slot_count]);
            }
            self.row_sink.accept(r, f)?;
        }
        self.row_sink.result(r, f)
    }
}

/// Implementation of RowSink for a distinct step.
///
/// Filters out duplicate rows, passing only the first occurrence of each
/// unique value to the downstream sink.
pub struct DistinctRowSink {
    slot_count: usize,
    row_sink: Box<dyn RowSink>,
    seen: Vec<Val>,
}

impl DistinctRowSink {
    pub fn new(slot_count: usize, row_sink: Box<dyn RowSink>) -> Self {
        Self {
            slot_count,
            row_sink,
            seen: Vec::new(),
        }
    }
}

impl RowSink for DistinctRowSink {
    fn start(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        self.seen.clear();
        self.row_sink.start(r, f)
    }

    fn accept(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<(), MorelError> {
        // Extract the current row value from the frame.
        let row_val = if self.slot_count == 1 {
            // Atom case: single binding.
            f.vals[0].clone()
        } else {
            // Tuple case: create tuple from slots 0..slot_count.
            Val::List(f.vals[0..self.slot_count].to_vec())
        };

        // Only pass through if we haven't seen this value before.
        if !self.seen.contains(&row_val) {
            self.seen.push(row_val);
            self.row_sink.accept(r, f)?;
        }
        Ok(())
    }

    fn result(
        &mut self,
        r: &mut EvalEnv,
        f: &mut Frame,
    ) -> Result<Val, MorelError> {
        self.row_sink.result(r, f)
    }
}
