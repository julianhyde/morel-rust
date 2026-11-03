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

use std::env;

fn main() {
    // Only walk `src/`; the default `process_root()` walks the
    // current working dir, which has tripped on unrelated artifacts
    // under `target/` during `cargo doc` in CI.
    lalrpop::process_src().unwrap();
    spark_protos();
}

/// Generates the messages of Spark Connect's protocol from the protos
/// vendored in `src/spark/proto`, for the Spark adapter. The protos are
/// compiled by `protox`, in Rust, so that building needs no `protoc`.
/// The adapter is native only, so a wasm build generates nothing.
fn spark_protos() {
    if env::var("CARGO_CFG_TARGET_ARCH").as_deref() == Ok("wasm32") {
        return;
    }
    const ROOT: &str = "src/spark/proto";
    println!("cargo:rerun-if-changed={}", ROOT);
    let files = [
        "spark/connect/base.proto",
        "spark/connect/catalog.proto",
        "spark/connect/commands.proto",
        "spark/connect/common.proto",
        "spark/connect/expressions.proto",
        "spark/connect/relations.proto",
        "spark/connect/types.proto",
    ];
    let fds = protox::compile(files, [ROOT]).unwrap();
    prost_build::Config::new().compile_fds(fds).unwrap();
}
