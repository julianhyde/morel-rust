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

//! Orchestrator for `Datalog.execute`. Mirrors morel-java's
//! `DatalogEvaluator` (hydromatic/morel#323).
//!
//! Pipeline: parse → analyze → translate → run translated Morel source
//! in a fresh `Shell` → wrap last binding's value as `Val::Variant`.
//!
//! A fresh `Shell` is used per call so the inner program's bindings,
//! type bindings, and overload state stay isolated from the outer
//! session that triggered the `Datalog.execute` call. The morel-java
//! implementation calls back into the same compile pipeline; in
//! morel-rust the borrow chain through `RefCell<Session>` makes
//! re-entry impractical, so we run in a sibling shell instead.

use crate::compile::types::{PrimitiveType, Type};
use crate::datalog::error::DatalogError;
use crate::datalog::{analyze, parse, translate};
use crate::eval::val::Val;
use crate::eval::variant::variant_of;
use crate::shell::main::Shell;

/// Runs a Datalog program and returns its output wrapped as a
/// `Val::Variant`. On parse, analysis, or runtime failure, returns a
/// variant of type `string` whose value is the error message.
pub fn execute(source: &str) -> Val {
    let ast = match parse(source) {
        Ok(a) => a,
        Err(DatalogError::Parse(msg)) => {
            return error_variant(&format!("Parse error: {}", msg));
        }
        Err(e) => return error_variant(&format!("Compilation error: {}", e)),
    };
    if let Err(e) = analyze(&ast) {
        let msg = match e {
            DatalogError::Analysis(m) => m,
            other => format!("{}", other),
        };
        return error_variant(&format!("Compilation error: {}", msg));
    }
    let morel_source = translate(&ast);

    let mut shell = Shell::new(&[]);
    if let Err(e) = shell.process_statement(&morel_source, None) {
        return error_variant(&format!(
            "Error executing Morel translation: {:?}\n\
             Generated Morel code:\n{}",
            e, morel_source
        ));
    }

    // Pull the last binding (`it` for an expression). The Datalog
    // translator always emits a `let ... in <expr> end` whose top-level
    // value lands in `it`; an empty program (no facts/rules and no
    // .output) emits `()` which still binds `it`.
    let value = shell.get_val("it").cloned().unwrap_or(Val::Unit);
    let result_type = shell
        .session_borrow()
        .type_bindings
        .get("it")
        .map_or(Type::Primitive(PrimitiveType::Unit), |(t, _)| t.clone());

    variant_of(result_type, value)
}

fn error_variant(msg: &str) -> Val {
    variant_of(
        Type::Primitive(PrimitiveType::String),
        Val::String(msg.to_string()),
    )
}
