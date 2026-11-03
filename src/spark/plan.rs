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

//! A Spark plan: what `Spark.prepare` makes of a Morel function, and
//! what `execute` runs.
//!
//! Port of morel-java's `SparkPlan`. Its text is the plan's own, in
//! protobuf's text format, except that a `LocalRelation` shows the
//! number of rows it carries rather than the Arrow bytes that carry
//! them.

use crate::spark::proto;
use crate::spark::text_format;
use std::fmt;

/// A plan, translated from a query.
#[derive(Clone)]
pub struct Plan {
    plan: proto::Plan,
    local_row_counts: Vec<usize>,
}

impl fmt::Debug for Plan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Plan({})", self.text())
    }
}

impl Plan {
    pub(crate) fn new(plan: proto::Plan, local_row_counts: Vec<usize>) -> Self {
        Plan {
            plan,
            local_row_counts,
        }
    }

    /// Returns the plan, to send to the server.
    #[allow(dead_code)]
    pub(crate) fn proto(&self) -> &proto::Plan {
        &self.plan
    }

    /// Returns the plan as text.
    pub fn text(&self) -> String {
        text_format::plan_text(&self.plan, &self.local_row_counts)
    }
}

// End plan.rs
