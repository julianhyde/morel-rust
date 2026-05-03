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

//! Datalog frontend (hydromatic/morel#323).
//!
//! Phase 1: AST + parser only. Later phases add the analyzer
//! (safety + stratification), translator (Datalog → Morel source),
//! and evaluator (parse → analyze → translate → compile → eval).

pub mod analyzer;
pub mod ast;
pub mod error;
pub mod parser;

pub use analyzer::analyze;
pub use error::DatalogError;
pub use parser::parse;

/// Validates a Datalog program. Returns `"OK"` on success, or an error
/// message starting with `"Parse error: "` or `"Compilation error: "`
/// on failure.
///
/// Phase 4 will replace the success path with a rendering of the
/// compiled program's result type. Until then, callers can rely on the
/// failure messages but the success placeholder is provisional.
pub fn validate(source: &str) -> String {
    match parse(source) {
        Err(DatalogError::Parse(msg)) => format!("Parse error: {}", msg),
        Err(other) => format!("Compilation error: {}", other),
        Ok(prog) => match analyze(&prog) {
            Ok(()) => "OK".to_string(),
            Err(e) => match e {
                DatalogError::Analysis(msg) => {
                    format!("Compilation error: {}", msg)
                }
                _ => format!("Compilation error: {}", e),
            },
        },
    }
}
