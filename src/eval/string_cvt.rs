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

//! The `StringCvt` functions that take a reader.
//!
//! A reader is a function `'b -> (char * 'b) option`: it reads one
//! character from a stream and returns it with the rest of the stream,
//! or `NONE` at the end. Only the reader knows what the stream is; the
//! functions here pass it back unexamined.

use crate::eval::code::{EvalEnv, Frame};
use crate::eval::val::Val;
use crate::shell::kernel::MorelError;

/// Reads from `src` the longest prefix of characters satisfying `p`,
/// and returns it with the rest of the stream. `splitl`, `takel` and
/// `dropl` return the pair, its first component and its second.
pub(crate) fn splitl(
    r: &mut EvalEnv,
    f: &mut Frame,
    p: &Val,
    rdr: &Val,
    src: &Val,
) -> Result<(String, Val), MorelError> {
    let mut prefix = String::new();
    let mut s = src.clone();
    loop {
        let Val::Some(pair) = rdr.apply_f1(r, f, &s)? else {
            break; // NONE: end of stream
        };
        let pair = pair.expect_list();
        let c = pair[0].expect_char();
        if !p.apply_f1(r, f, &pair[0])?.expect_bool() {
            break;
        }
        prefix.push(c);
        s = pair[1].clone();
    }
    Ok((prefix, s))
}

/// Drops any leading whitespace from `src`.
pub(crate) fn skip_ws(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let mut s = src.clone();
    loop {
        let Val::Some(pair) = rdr.apply_f1(r, f, &s)? else {
            break;
        };
        let pair = pair.expect_list();
        if !pair[0].expect_char().is_whitespace() {
            break;
        }
        s = pair[1].clone();
    }
    Ok(s)
}
