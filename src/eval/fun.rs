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

use crate::compile::library::BuiltInExn;
use crate::eval::code::{Code, EvalEnv, Frame, Span};
use crate::eval::val::Val;
use crate::shell::main::MorelError;

/// Support for the `Fn` structure.
///
/// The Fn structure provides utility functions for working with functions,
/// including composition, currying, and function application.
pub struct Fn;

impl Fn {
    // lint: sort until '#}' where '##pub'

    /// Applies function `f` n times to a value.
    /// If n is 0, returns the identity function.
    /// If n is negative, raises Domain exception.
    pub(crate) fn repeat(
        r: &mut EvalEnv,
        f: &mut Frame,
        n: i32,
        func: &Code,
        value: &Val,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if n < 0 {
            Err(MorelError::Runtime(BuiltInExn::Domain, span.clone()))
        } else if n == 0 {
            Ok(value.clone())
        } else {
            let mut result = value.clone();
            for _ in 0..n {
                result = func.eval_f1(r, f, &result)?;
            }
            Ok(result)
        }
    }
}
