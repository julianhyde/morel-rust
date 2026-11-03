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

//! The Spark adapter: translates a Morel query to a Spark Connect
//! plan, and runs it on a server.
//!
//! Port of morel-java's `net.hydromatic.morel.spark` package. As
//! there, the adapter has requirements that the rest of Morel does not
//! -- protobuf, Arrow and gRPC -- and nothing outside this module
//! refers to them. The connections and catalogs that the `Spark`
//! structure works with are in [`crate::eval::spark`], which is
//! morel-java's `foreign` side; it calls in here to translate and to
//! execute.
//!
//! The adapter is built for native targets only. On wasm, where there
//! is neither a network nor room for the libraries, this module is a
//! stub that says the adapter is not available, as morel-java does
//! where the adapter is not on its class path.

#[cfg(not(target_arch = "wasm32"))]
mod arrow;
#[cfg(not(target_arch = "wasm32"))]
mod function_table;
#[cfg(not(target_arch = "wasm32"))]
mod plan;
#[cfg(not(target_arch = "wasm32"))]
mod prepare;
#[cfg(not(target_arch = "wasm32"))]
mod proto;
#[cfg(not(target_arch = "wasm32"))]
mod schema;
#[cfg(not(target_arch = "wasm32"))]
mod text_format;
#[cfg(not(target_arch = "wasm32"))]
mod translator;

#[cfg(not(target_arch = "wasm32"))]
pub use plan::Plan;
#[cfg(not(target_arch = "wasm32"))]
pub use prepare::prepare_decl;
#[cfg(not(target_arch = "wasm32"))]
pub use translator::translate;

/// Returns whether the Spark adapter is present in this build.
pub fn is_available() -> bool {
    cfg!(not(target_arch = "wasm32"))
}

#[cfg(target_arch = "wasm32")]
mod stub {
    use crate::compile::core::{Decl, Expr};
    use crate::eval::spark::{SparkError, adapter_unavailable};
    use crate::eval::val::Val;
    use std::collections::HashMap;

    /// A plan. Without the adapter there is none.
    #[derive(Clone, Debug)]
    pub enum Plan {}

    impl Plan {
        pub fn text(&self) -> String {
            match *self {}
        }
    }

    /// Without the adapter, nothing is prepared at compile time, and
    /// `Spark.prepare` raises where it is evaluated.
    pub fn prepare_decl(
        decl: Decl,
        _bindings: &HashMap<String, Val>,
    ) -> Result<Decl, SparkError> {
        Ok(decl)
    }

    pub fn translate(_query: &Expr) -> Result<Plan, SparkError> {
        Err(adapter_unavailable())
    }
}

#[cfg(target_arch = "wasm32")]
pub use stub::{Plan, prepare_decl, translate};

// End mod.rs
