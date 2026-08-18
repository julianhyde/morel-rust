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
use crate::eval::int::radix_base;
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

/// Reads the characters of `src` while `p` holds, and returns them with
/// the rest of the stream. Unlike [`splitl`] the predicate is a Rust
/// function, for the scanners that recognise a token themselves.
fn take_while(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    p: impl Fn(char) -> bool,
) -> Result<(String, Val), MorelError> {
    let mut prefix = String::new();
    let mut s = src.clone();
    loop {
        let Val::Some(pair) = rdr.apply_f1(r, f, &s)? else {
            break;
        };
        let pair = pair.expect_list();
        let c = pair[0].expect_char();
        if !p(c) {
            break;
        }
        prefix.push(c);
        s = pair[1].clone();
    }
    Ok((prefix, s))
}

/// A radix's base, and which characters are its digits.
fn radix_of(radix: &Val) -> (u32, fn(char) -> bool) {
    match radix_base(radix) {
        2 => (2, |c: char| matches!(c, '0'..='1')),
        8 => (8, |c: char| matches!(c, '0'..='7')),
        16 => (16, |c: char| c.is_ascii_hexdigit()),
        base => (base, |c: char| c.is_ascii_digit()),
    }
}

/// Reads the digits of a number in `radix`, after an optional prefix
/// that says what the radix is (`0x` for hexadecimal, `0w`/`0wx` for a
/// word), and returns them with the rest of the stream. The prefix is
/// only taken if digits follow it; `0xzz` reads as the digit `0` and
/// stops at the `x`, because `0` is itself a hexadecimal digit.
fn digits(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    radix: u32,
    is_digit: fn(char) -> bool,
    word: bool,
) -> Result<Option<(String, Val)>, MorelError> {
    let mut s = src.clone();
    for prefix in prefixes(radix, word) {
        if let Some(after) = expect_word(r, f, rdr, &s, prefix)? {
            let (ds, rest) = take_while(r, f, rdr, &after, is_digit)?;
            if !ds.is_empty() {
                return Ok(Some((ds, rest)));
            }
        }
    }
    let (ds, rest) = take_while(r, f, rdr, &s, is_digit)?;
    s = rest;
    if ds.is_empty() {
        return Ok(None);
    }
    Ok(Some((ds, s)))
}

/// The radix prefixes to try, longest first.
fn prefixes(radix: u32, word: bool) -> &'static [&'static str] {
    match (radix, word) {
        (16, true) => &["0wx", "0x"],
        (16, false) => &["0x"],
        (_, true) => &["0w"],
        _ => &[],
    }
}

/// Reads a sign, if there is one: `~` or `+`, and `-` too where
/// `minus` says so. Returns whether the value is negative, and the
/// stream that follows the sign.
fn signed(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
    minus: bool,
) -> Result<(bool, Val), MorelError> {
    let negatives: &[&str] = if minus { &["~", "-"] } else { &["~"] };
    for sign in negatives {
        if let Some(rest) = expect_word(r, f, rdr, src, sign)? {
            return Ok((true, rest));
        }
    }
    match expect_word(r, f, rdr, src, "+")? {
        Some(rest) => Ok((false, rest)),
        None => Ok((false, src.clone())),
    }
}

/// Scans an integer in `radix`, after skipping whitespace. A leading
/// `~` or `+` gives the sign.
pub(crate) fn int_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    radix: &Val,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let (base, is_digit) = radix_of(radix);
    let s = skip_ws(r, f, rdr, src)?;
    let (negative, s) = signed(r, f, rdr, &s, false)?;
    let Some((ds, rest)) = digits(r, f, rdr, &s, base, is_digit, false)? else {
        return Ok(Val::Unit);
    };
    let Ok(magnitude) = i64::from_str_radix(&ds, base) else {
        return Ok(Val::Unit);
    };
    let value = if negative { -magnitude } else { magnitude };
    let Ok(value) = i32::try_from(value) else {
        return Ok(Val::Unit);
    };
    Ok(scanned(Val::Int(value), rest))
}

/// Scans a word in `radix`, after skipping whitespace. A word has no
/// sign.
pub(crate) fn word_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    radix: &Val,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let (base, is_digit) = radix_of(radix);
    let s = skip_ws(r, f, rdr, src)?;
    let Some((ds, rest)) = digits(r, f, rdr, &s, base, is_digit, true)? else {
        return Ok(Val::Unit);
    };
    let Ok(value) = u64::from_str_radix(&ds, base) else {
        return Ok(Val::Unit);
    };
    Ok(scanned(Val::Word(value), rest))
}

/// Scans a real, after skipping whitespace: an optional sign, then
/// `inf`, `infinity` or `nan`, or digits with an optional fraction and
/// exponent.
pub(crate) fn real_scan(
    r: &mut EvalEnv,
    f: &mut Frame,
    rdr: &Val,
    src: &Val,
) -> Result<Val, MorelError> {
    let s = skip_ws(r, f, rdr, src)?;
    // A real may be signed with `-` as well as Standard ML's `~`, and
    // its exponent likewise, because `Real.fromString` reads what other
    // languages write.
    let (negative, s) = signed(r, f, rdr, &s, true)?;
    let sign = if negative { -1.0 } else { 1.0 };
    for (word, value) in [
        ("infinity", f32::INFINITY),
        ("inf", f32::INFINITY),
        ("nan", f32::NAN),
    ] {
        if let Some(rest) = expect_word(r, f, rdr, &s, word)? {
            let value = if word == "nan" { value } else { sign * value };
            return Ok(scanned(Val::Real(value), rest));
        }
    }
    let (whole, s) = take_while(r, f, rdr, &s, |c| c.is_ascii_digit())?;
    if whole.is_empty() {
        return Ok(Val::Unit);
    }
    let mut text = whole;
    let mut rest = s;
    // A fraction, only if a digit follows the point.
    if let Some(after) = expect_word(r, f, rdr, &rest, ".")? {
        let (frac, after2) =
            take_while(r, f, rdr, &after, |c| c.is_ascii_digit())?;
        if !frac.is_empty() {
            text.push('.');
            text.push_str(&frac);
            rest = after2;
        }
    }
    // An exponent, only if a digit follows `e` (or `E`) and its
    // optional sign.
    let exponent = match expect_word(r, f, rdr, &rest, "e")? {
        Some(after) => Some(after),
        None => expect_word(r, f, rdr, &rest, "E")?,
    };
    if let Some(after) = exponent {
        let (exp_neg, after) = signed(r, f, rdr, &after, true)?;
        let (exp, after2) =
            take_while(r, f, rdr, &after, |c| c.is_ascii_digit())?;
        if !exp.is_empty() {
            text.push('e');
            if exp_neg {
                text.push('-');
            }
            text.push_str(&exp);
            rest = after2;
        }
    }
    let Ok(value) = text.parse::<f32>() else {
        return Ok(Val::Unit);
    };
    Ok(scanned(Val::Real(sign * value), rest))
}
