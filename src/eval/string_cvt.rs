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
use crate::eval::val::{NativeFn, Val};
use crate::shell::kernel::MorelError;
use std::rc::Rc;

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

/// Scans `s` with the scanner `scan`, giving it a reader over the
/// characters of `s`. The stream is a position in `s`, but the
/// scanner's type does not say so, and the reader is the only thing
/// that can make sense of it.
pub(crate) fn scan_string(
    r: &mut EvalEnv,
    f: &mut Frame,
    scan: &Val,
    s: &str,
) -> Result<Val, MorelError> {
    let reader = string_reader(s);
    let scanner = scan.apply_f1(r, f, &reader)?;
    match scanner.apply_f1(r, f, &Val::Int(0))? {
        Val::Some(pair) => {
            Ok(Val::Some(Box::new(pair.expect_list()[0].clone())))
        }
        _ => Ok(Val::Unit),
    }
}

/// Reads `word` from `src`, character by character, and returns the
/// stream that follows it; `None` if the stream does not begin with it.
pub(crate) fn expect_word(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    word: &str,
) -> Result<Option<Val>, MorelError> {
    let mut s = src.clone();
    for want in word.chars() {
        let Val::Some(pair) = rdr.apply_f1(r, f, &s)? else {
            return Ok(None);
        };
        let pair = pair.expect_list();
        if pair[0].expect_char() != want {
            return Ok(None);
        }
        s = pair[1].clone();
    }
    Ok(Some(s))
}

/// `SOME (value, rest)`, the result of a scanner that read something.
pub(crate) fn scanned(value: Val, rest: Val) -> Val {
    Val::Some(Box::new(Val::List(Rc::new(vec![value, rest]))))
}

/// Scans `true` or `false`, after skipping whitespace.
pub(crate) fn bool_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let s = skip_ws(r, f, rdr, src)?;
    for (word, value) in [("true", true), ("false", false)] {
        if let Some(rest) = expect_word(r, f, rdr, &s, word)? {
            return Ok(scanned(Val::Bool(value), rest));
        }
    }
    Ok(Val::Unit)
}

/// Scans a value from a prefix of `s` with a scanner written in Rust,
/// as `StringCvt.scanString` does for one written in Morel. `Bool
/// .fromString` and its like are defined that way, so whitespace is
/// skipped and characters after the value are ignored.
pub(crate) fn scan_str(
    r: &mut EvalEnv,
    f: &mut Frame,
    scan: impl Fn(&mut EvalEnv, &mut Frame, &Val, &Val) -> Result<Val, MorelError>,
    s: &str,
) -> Result<Val, MorelError> {
    let reader = string_reader(s);
    match scan(r, f, &reader, &Val::Int(0))? {
        Val::Some(pair) => {
            Ok(Val::Some(Box::new(pair.expect_list()[0].clone())))
        }
        _ => Ok(Val::Unit),
    }
}

/// A reader over the characters of `s`. The stream is a position in `s`.
pub(crate) fn string_reader(s: &str) -> Val {
    let chars: Rc<Vec<char>> = Rc::new(s.chars().collect());
    Val::NativeFn(Rc::new(NativeFn::new(
        "StringCvt.scanString.reader",
        move |v| match usize::try_from(v.expect_int())
            .ok()
            .and_then(|i| chars.get(i).map(|c| (i, *c)))
        {
            Some((i, c)) => Val::Some(Box::new(Val::List(Rc::new(vec![
                Val::Char(c),
                Val::Int(i as i32 + 1),
            ])))),
            // NONE: the end of the string, or a position beyond it.
            None => Val::Unit,
        },
    )))
}
