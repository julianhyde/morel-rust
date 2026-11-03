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

//! Runs `triple.smli` a third time, with every query pushed down to
//! Spark, as morel-java's `ScriptTest.testScriptTripleSpark` does.
//!
//! The same queries, the same expected answers, and a third way of
//! computing them. A query that Spark cannot do, or answers
//! differently, fails here. It needs a live Spark Connect server, so it
//! runs only when `MOREL_SPARK` is set and `SPARK_REMOTE` names the
//! server; otherwise it is skipped, and passes.

use morel::shell::ScriptTest;

#[test]
fn triple_spark() {
    ScriptTest::default()
        .with_spark_push_down()
        .run("tests/script/triple.smli")
        .expect("should work");
}

// End spark.rs
