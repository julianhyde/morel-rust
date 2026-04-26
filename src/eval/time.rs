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

//! Implementation of the `Time` structure of the SML Basis Library.
//!
//! Time values are stored as a 64-bit signed nanosecond count since the
//! Unix epoch (1970-01-01T00:00:00Z), or as a duration when interpreted
//! contextually.

use crate::compile::library::BuiltInExn;
use crate::compile::span::Span;
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::main::MorelError;
use crate::shell::prop::{Prop, PropVal};
use std::time::{SystemTime, UNIX_EPOCH};

/// Wraps a nanosecond count as a `Val::Time`.
fn t(n: i64) -> Val {
    Val::Time(n)
}

/// `Time.zeroTime`: the zero time value.
pub(crate) fn zero_time() -> Val {
    t(0)
}

/// `Time.fromSeconds n`: time from seconds.
pub(crate) fn from_seconds(n: i32) -> Val {
    t(n as i64 * 1_000_000_000)
}

/// `Time.fromMilliseconds n`: time from milliseconds.
pub(crate) fn from_milliseconds(n: i32) -> Val {
    t(n as i64 * 1_000_000)
}

/// `Time.fromMicroseconds n`: time from microseconds.
pub(crate) fn from_microseconds(n: i32) -> Val {
    t(n as i64 * 1_000)
}

/// `Time.fromNanoseconds n`: time from nanoseconds.
pub(crate) fn from_nanoseconds(n: i32) -> Val {
    t(n as i64)
}

/// `Time.toSeconds t`: returns whole seconds, truncated toward zero.
pub(crate) fn to_seconds(v: i64) -> Val {
    Val::Int((v / 1_000_000_000) as i32)
}

/// `Time.toMilliseconds t`: returns whole milliseconds.
pub(crate) fn to_milliseconds(v: i64) -> Val {
    Val::Int((v / 1_000_000) as i32)
}

/// `Time.toMicroseconds t`: returns whole microseconds.
pub(crate) fn to_microseconds(v: i64) -> Val {
    Val::Int((v / 1_000) as i32)
}

/// `Time.toNanoseconds t`: returns nanoseconds.
pub(crate) fn to_nanoseconds(v: i64) -> Val {
    Val::Int(v as i32)
}

/// `Time.fromReal r`: converts seconds to time. Raises `Time` on NaN
/// or infinity.
pub(crate) fn from_real(r: f32, span: &Span) -> Result<Val, MorelError> {
    if !r.is_finite() {
        return Err(MorelError::Runtime(BuiltInExn::Time, span.clone()));
    }
    Ok(t((r as f64 * 1e9) as i64))
}

/// `Time.toReal t`: converts a time to seconds as a real.
pub(crate) fn to_real(v: i64) -> Val {
    Val::Real(v as f32 / 1e9)
}

/// `Time.fmt n t`: format `t` as decimal seconds with `n` fractional
/// digits.
pub(crate) fn fmt(n: i32, v: i64) -> Val {
    Val::String(format(n, v))
}

/// `Time.toString t`: equivalent to `fmt 3 t`.
pub(crate) fn to_string(v: i64) -> Val {
    Val::String(format(3, v))
}

/// `Time.fromString s`: parse a decimal-seconds string into `time
/// option`.
pub(crate) fn from_string(s: &str) -> Val {
    let trimmed = s.trim();
    let cleaned: String = trimmed
        .chars()
        .map(|c| if c == '~' { '-' } else { c })
        .collect();
    match cleaned.parse::<f64>() {
        Ok(seconds) if seconds.is_finite() => {
            Val::Some(Box::new(t((seconds * 1e9) as i64)))
        }
        _ => Val::Unit, // NONE
    }
}

/// `Time.now ()`: current time. Honors the `now` property if set.
pub(crate) fn now(session: &Session) -> Val {
    if let Some(PropVal::String(s)) = session.config.get_optional(Prop::Now)
        && let Some(nanos) = parse_iso8601_nanos(&s)
    {
        return t(nanos);
    }
    let now = SystemTime::now();
    let dur = now
        .duration_since(UNIX_EPOCH)
        .expect("system time before epoch");
    t(dur.as_nanos() as i64)
}

/// Format `t` as decimal seconds with `n` fractional digits.
fn format(n: i32, t: i64) -> String {
    let neg = t < 0;
    let abs = t.unsigned_abs();
    let secs = abs / 1_000_000_000;
    let mut s = String::new();
    if neg {
        s.push('~');
    }
    s.push_str(&secs.to_string());
    if n > 0 {
        s.push('.');
        let nanos = (abs % 1_000_000_000) as u32;
        let frac = format!("{:09}", nanos);
        let take = (n as usize).min(9);
        s.push_str(&frac[..take]);
        for _ in take..n as usize {
            s.push('0');
        }
    }
    s
}

/// Parses an ISO-8601 instant string like `"2024-01-01T00:00:00Z"` to
/// nanoseconds since epoch. Supports the canonical UTC form with or
/// without a fractional seconds part.
fn parse_iso8601_nanos(s: &str) -> Option<i64> {
    // Format: YYYY-MM-DDTHH:MM:SS[.fff...]Z
    let s = s.trim();
    let s = s.strip_suffix('Z')?;
    let (date_part, time_part) = s.split_once('T')?;
    let mut date_iter = date_part.split('-');
    let y: i32 = date_iter.next()?.parse().ok()?;
    let m: u32 = date_iter.next()?.parse().ok()?;
    let d: u32 = date_iter.next()?.parse().ok()?;
    let (clock, frac) = match time_part.split_once('.') {
        Some((c, f)) => (c, f),
        None => (time_part, ""),
    };
    let mut clock_iter = clock.split(':');
    let hh: u32 = clock_iter.next()?.parse().ok()?;
    let mm: u32 = clock_iter.next()?.parse().ok()?;
    let ss: u32 = clock_iter.next()?.parse().ok()?;

    let days = days_from_civil(y, m as i32, d as i32);
    let secs = days * 86_400 + hh as i64 * 3600 + mm as i64 * 60 + ss as i64;
    let nanos = if frac.is_empty() {
        0
    } else {
        let mut padded = String::with_capacity(9);
        padded.push_str(&frac[..frac.len().min(9)]);
        while padded.len() < 9 {
            padded.push('0');
        }
        padded.parse::<u32>().ok()? as i64
    };
    Some(secs * 1_000_000_000 + nanos)
}

/// Howard Hinnant's `days_from_civil`: number of days from 1970-01-01
/// to the given proleptic Gregorian date (negative for earlier dates).
fn days_from_civil(y: i32, m: i32, d: i32) -> i64 {
    let y = if m <= 2 { y - 1 } else { y } as i64;
    let era = if y >= 0 { y / 400 } else { (y - 399) / 400 };
    let yoe = y - era * 400;
    let m = m as i64;
    let d = d as i64;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}
