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

//! The messages of Spark Connect's protocol, `spark.connect`, generated
//! by `build.rs` from the protos in `src/spark/proto`, which are
//! morel-java's, which are Spark 4.0's.

#![allow(clippy::all, clippy::pedantic, missing_docs, rustdoc::all)]
#![allow(dead_code, deprecated)]

include!(concat!(env!("OUT_DIR"), "/spark.connect.rs"));

// End proto.rs
