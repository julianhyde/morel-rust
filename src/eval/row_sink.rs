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
use crate::eval::val::Val;
use crate::shell::main::MorelError;

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
        // Evaluate the collection to iterate over
        let collection = self.collection_code.eval_f0(r, f)?;
        let items = collection.expect_list();

        // Iterate over elements
        for item in items {
            // Try to bind the pattern to this item
            let matched = self.pat_code.eval_f1(r, f, item)?;
            if matched.expect_bool() {
                // Evaluate condition
                let condition = self.condition_code.eval_f0(r, f)?;
                if condition.expect_bool() {
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
/// and passes their elements downstream. Supports distinct mode for
/// deduplication.
pub struct UnionRowSink {
    distinct: bool,
    slot_count: usize,
    codes: Vec<Code>,
    row_sink: Box<dyn RowSink>,
    seen: Vec<Val>,
}

impl UnionRowSink {
    pub fn new(
        distinct: bool,
        slot_count: usize,
        codes: Vec<Code>,
        row_sink: Box<dyn RowSink>,
    ) -> Self {
        Self {
            distinct,
            slot_count,
            codes,
            row_sink,
            seen: Vec::new(),
        }
    }

    fn add(&mut self, val: &Val) -> bool {
        if self.distinct {
            if self.seen.contains(val) {
                false
            } else {
                self.seen.push(val.clone());
                true
            }
        } else {
            true
        }
    }
}

impl RowSink for UnionRowSink {
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
        // For union, we need to track the row value to check for duplicates
        // This is simplified - ideally we'd extract the row value from frame
        // For now, just pass through
        if !self.distinct {
            self.row_sink.accept(r, f)?;
        } else {
            // TODO: Extract value from frame to check for duplicates
            self.row_sink.accept(r, f)?;
        }
        Ok(())
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
                if self.add(item) {
                    // Bind the item directly to frame slots (0..slot_count).
                    if self.slot_count == 1 {
                        // Atom case: single binding at slot 0.
                        f.vals[0] = item.clone();
                    } else {
                        // Tuple case: unpack tuple and bind to slots 0..slot_count.
                        let tuple_items = item.expect_list();
                        for i in 0..self.slot_count {
                            f.vals[i] = tuple_items[i].clone();
                        }
                    }
                    self.row_sink.accept(r, f)?;
                }
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
