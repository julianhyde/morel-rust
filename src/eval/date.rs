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

//! Implementation of the `Date` structure of the SML Basis Library.
//!
//! Date values are stored as 64-bit signed nanosecond counts since
//! the Unix epoch (1970-01-01T00:00:00Z), the same representation
//! as `Time` values.

use crate::compile::library::BuiltInExn;
use crate::compile::span::Span;
use crate::eval::order::Order;
use crate::eval::session::Session;
use crate::eval::val::{
    self, MONTH_APR_ORDINAL, MONTH_AUG_ORDINAL, MONTH_DEC_ORDINAL,
    MONTH_FEB_ORDINAL, MONTH_JAN_ORDINAL, MONTH_JUL_ORDINAL, MONTH_JUN_ORDINAL,
    MONTH_MAR_ORDINAL, MONTH_MAY_ORDINAL, MONTH_NOV_ORDINAL, MONTH_OCT_ORDINAL,
    MONTH_SEP_ORDINAL, Val, WEEKDAY_FRI_ORDINAL, WEEKDAY_MON_ORDINAL,
    WEEKDAY_SAT_ORDINAL, WEEKDAY_SUN_ORDINAL, WEEKDAY_THU_ORDINAL,
    WEEKDAY_TUE_ORDINAL, WEEKDAY_WED_ORDINAL,
};
use crate::shell::main::MorelError;
use crate::shell::prop::{Prop, PropVal};

const NS_PER_SEC: i64 = 1_000_000_000;
const SECS_PER_DAY: i64 = 86_400;
const SECS_PER_HOUR: i64 = 3_600;
const SECS_PER_MIN: i64 = 60;

/// Decomposed broken-down date.
#[derive(Copy, Clone)]
struct Broken {
    year: i32,
    month: u32, // 1..12
    day: u32,   // 1..31
    hour: u32,
    minute: u32,
    second: u32,
    weekday: u32, // 0=Mon..6=Sun
    yearday: u32, // 0..365
}

fn weekday_ordinal(w: u32) -> usize {
    match w {
        0 => WEEKDAY_MON_ORDINAL,
        1 => WEEKDAY_TUE_ORDINAL,
        2 => WEEKDAY_WED_ORDINAL,
        3 => WEEKDAY_THU_ORDINAL,
        4 => WEEKDAY_FRI_ORDINAL,
        5 => WEEKDAY_SAT_ORDINAL,
        6 => WEEKDAY_SUN_ORDINAL,
        _ => panic!("invalid weekday: {}", w),
    }
}

fn month_ordinal(m: u32) -> usize {
    match m {
        1 => MONTH_JAN_ORDINAL,
        2 => MONTH_FEB_ORDINAL,
        3 => MONTH_MAR_ORDINAL,
        4 => MONTH_APR_ORDINAL,
        5 => MONTH_MAY_ORDINAL,
        6 => MONTH_JUN_ORDINAL,
        7 => MONTH_JUL_ORDINAL,
        8 => MONTH_AUG_ORDINAL,
        9 => MONTH_SEP_ORDINAL,
        10 => MONTH_OCT_ORDINAL,
        11 => MONTH_NOV_ORDINAL,
        12 => MONTH_DEC_ORDINAL,
        _ => panic!("invalid month: {}", m),
    }
}

/// Returns the 1-based month (1..12) for the given month constructor
/// ordinal.
pub(crate) fn ordinal_to_month(o: usize) -> u32 {
    match o {
        x if x == MONTH_JAN_ORDINAL => 1,
        x if x == MONTH_FEB_ORDINAL => 2,
        x if x == MONTH_MAR_ORDINAL => 3,
        x if x == MONTH_APR_ORDINAL => 4,
        x if x == MONTH_MAY_ORDINAL => 5,
        x if x == MONTH_JUN_ORDINAL => 6,
        x if x == MONTH_JUL_ORDINAL => 7,
        x if x == MONTH_AUG_ORDINAL => 8,
        x if x == MONTH_SEP_ORDINAL => 9,
        x if x == MONTH_OCT_ORDINAL => 10,
        x if x == MONTH_NOV_ORDINAL => 11,
        x if x == MONTH_DEC_ORDINAL => 12,
        _ => panic!("not a month ordinal: {}", o),
    }
}

/// Wraps a date constructor as a `Val::Constructor` with `Val::Unit`
/// payload.
fn ctor(o: usize) -> Val {
    Val::Constructor(o, Box::new(Val::Unit))
}

fn weekday_val(w: u32) -> Val {
    ctor(weekday_ordinal(w))
}

fn month_val(m: u32) -> Val {
    ctor(month_ordinal(m))
}

const MONTH_NAMES_SHORT: [&str; 12] = [
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct",
    "Nov", "Dec",
];
const WEEKDAY_NAMES_SHORT: [&str; 7] =
    ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];

/// Howard Hinnant's `civil_from_days`: converts a count of days since
/// 1970-01-01 into a (year, month, day) triple.
fn civil_from_days(days: i64) -> (i32, u32, u32) {
    let z = days + 719468;
    let era = if z >= 0 {
        z / 146097
    } else {
        (z - 146096) / 146097
    };
    let doe = (z - era * 146097) as u64;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    let y = if m <= 2 { y + 1 } else { y };
    (y as i32, m, d)
}

/// Howard Hinnant's `days_from_civil`: converts a (year, month, day)
/// triple into days since 1970-01-01.
fn days_from_civil(y: i32, m: u32, d: u32) -> i64 {
    let y = if m <= 2 { y as i64 - 1 } else { y as i64 };
    let era = if y >= 0 { y / 400 } else { (y - 399) / 400 };
    let yoe = y - era * 400;
    let m = m as i64;
    let d = d as i64;
    let doy = (153 * (if m > 2 { m - 3 } else { m + 9 }) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}

fn is_leap(y: i32) -> bool {
    (y % 4 == 0 && y % 100 != 0) || y % 400 == 0
}

const DAYS_IN_MONTH: [u32; 12] =
    [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];

fn days_in_month(y: i32, m: u32) -> u32 {
    if m == 2 && is_leap(y) {
        29
    } else {
        DAYS_IN_MONTH[(m - 1) as usize]
    }
}

/// Day of year (0..365) for the given civil date.
fn day_of_year(y: i32, m: u32, d: u32) -> u32 {
    let mut total: u32 = 0;
    for i in 1..m {
        total += days_in_month(y, i);
    }
    total + d - 1
}

/// Decomposes nanoseconds since epoch into broken-down UTC fields.
fn break_down(nanos: i64) -> Broken {
    let mut secs = nanos.div_euclid(NS_PER_SEC);
    let mut days = secs.div_euclid(SECS_PER_DAY);
    secs = secs.rem_euclid(SECS_PER_DAY);
    let hour = (secs / SECS_PER_HOUR) as u32;
    let minute = ((secs % SECS_PER_HOUR) / SECS_PER_MIN) as u32;
    let second = (secs % SECS_PER_MIN) as u32;
    // Compute weekday: 1970-01-01 was a Thursday (weekday = 3 with Mon=0).
    let weekday = ((days.rem_euclid(7) + 3).rem_euclid(7)) as u32;
    let _ = &mut days;
    let (y, m, d) = civil_from_days(days);
    let yearday = day_of_year(y, m, d);
    Broken {
        year: y,
        month: m,
        day: d,
        hour,
        minute,
        second,
        weekday,
        yearday,
    }
}

/// Formats a date value as ISO-8601 (e.g. `1970-01-01T00:00Z`).
pub(crate) fn format_iso(nanos: i64) -> String {
    let b = break_down(nanos);
    if b.second == 0 {
        format!(
            "{:04}-{:02}-{:02}T{:02}:{:02}Z",
            b.year, b.month, b.day, b.hour, b.minute
        )
    } else {
        format!(
            "{:04}-{:02}-{:02}T{:02}:{:02}:{:02}Z",
            b.year, b.month, b.day, b.hour, b.minute, b.second
        )
    }
}

/// `Date.fromTimeUniv t`: converts a time to a UTC date.
pub(crate) fn from_time_univ(t: i64) -> Val {
    Val::Date(t)
}

/// `Date.fromTimeLocal t`: converts a time to a local date. With
/// `timeZone` property = "UTC", same as `fromTimeUniv`.
pub(crate) fn from_time_local(t: i64, _session: &Session) -> Val {
    // For now, we only support UTC.
    Val::Date(t)
}

/// `Date.toTime d`: converts a date to a time.
pub(crate) fn to_time(d: i64) -> Val {
    Val::Time(d)
}

/// `Date.localOffset ()`: returns the local timezone offset as a time.
pub(crate) fn local_offset(_session: &Session) -> Val {
    // Only UTC supported.
    Val::Time(0)
}

/// `Date.year d`.
pub(crate) fn year(d: i64) -> Val {
    Val::Int(break_down(d).year)
}

/// `Date.month d`.
pub(crate) fn month(d: i64) -> Val {
    month_val(break_down(d).month)
}

/// `Date.day d`.
pub(crate) fn day(d: i64) -> Val {
    Val::Int(break_down(d).day as i32)
}

/// `Date.hour d`.
pub(crate) fn hour(d: i64) -> Val {
    Val::Int(break_down(d).hour as i32)
}

/// `Date.minute d`.
pub(crate) fn minute(d: i64) -> Val {
    Val::Int(break_down(d).minute as i32)
}

/// `Date.second d`.
pub(crate) fn second(d: i64) -> Val {
    Val::Int(break_down(d).second as i32)
}

/// `Date.weekDay d`.
pub(crate) fn week_day(d: i64) -> Val {
    weekday_val(break_down(d).weekday)
}

/// `Date.yearDay d`.
pub(crate) fn year_day(d: i64) -> Val {
    Val::Int(break_down(d).yearday as i32)
}

/// `Date.isDst d`.
pub(crate) fn is_dst(_d: i64) -> Val {
    // NONE — DST information not available.
    Val::Unit
}

/// `Date.compare (d1, d2)`.
pub(crate) fn compare(d1: i64, d2: i64) -> Val {
    Val::Order(Order(d1.cmp(&d2)))
}

/// `Date.date {year, month, day, hour, minute, second, offset}`.
/// The record is passed as a tuple of 7 values in field order:
/// day, hour, minute, month, offset, second, year (alphabetical).
/// Raises `Date` if any field is out of range.
pub(crate) fn make_date(args: &[Val], span: &Span) -> Result<Val, MorelError> {
    // Records sort fields alphabetically: day, hour, minute, month, offset,
    // second, year.
    assert_eq!(args.len(), 7);
    let day = args[0].expect_int();
    let hour = args[1].expect_int();
    let minute = args[2].expect_int();
    let month_ord = match &args[3] {
        Val::Constructor(o, _) => *o,
        _ => panic!("expected month constructor"),
    };
    let offset = &args[4]; // time option (Unit = NONE)
    let second = args[5].expect_int();
    let year = args[6].expect_int();

    let m = ordinal_to_month(month_ord);
    if !(1..=days_in_month(year, m) as i32).contains(&day)
        || !(0..24).contains(&hour)
        || !(0..60).contains(&minute)
        || !(0..60).contains(&second)
    {
        return Err(MorelError::Runtime(BuiltInExn::Date, span.clone()));
    }

    let days = days_from_civil(year, m, day as u32);
    let secs = days * SECS_PER_DAY
        + hour as i64 * SECS_PER_HOUR
        + minute as i64 * SECS_PER_MIN
        + second as i64;
    let mut nanos = secs * NS_PER_SEC;
    // If offset is SOME t, subtract it (offset is east-of-UTC).
    if let Val::Some(boxed) = offset {
        let off = boxed.expect_time();
        nanos -= off;
    }
    Ok(Val::Date(nanos))
}

/// `Date.toString d`: e.g. `"Wed Dec 31 00:00:00 1969"`.
pub(crate) fn to_string(d: i64) -> Val {
    let b = break_down(d);
    Val::String(format!(
        "{} {} {:02} {:02}:{:02}:{:02} {:04}",
        WEEKDAY_NAMES_SHORT[b.weekday as usize],
        MONTH_NAMES_SHORT[(b.month - 1) as usize],
        b.day,
        b.hour,
        b.minute,
        b.second,
        b.year
    ))
}

/// `Date.fmt fmt d`: format with strftime-style directives. Supports
/// `%Y`, `%m`, `%d`, `%H`, `%M`, `%S`, `%A`, `%a`, `%B`, `%b`, `%j`,
/// `%%`.
pub(crate) fn fmt(format: &str, d: i64) -> Val {
    let b = break_down(d);
    let mut out = String::new();
    let mut chars = format.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '%'
            && let Some(&next) = chars.peek()
        {
            chars.next();
            match next {
                'Y' => out.push_str(&format!("{:04}", b.year)),
                'm' => out.push_str(&format!("{:02}", b.month)),
                'd' => out.push_str(&format!("{:02}", b.day)),
                'H' => out.push_str(&format!("{:02}", b.hour)),
                'M' => out.push_str(&format!("{:02}", b.minute)),
                'S' => out.push_str(&format!("{:02}", b.second)),
                'b' => out.push_str(MONTH_NAMES_SHORT[(b.month - 1) as usize]),
                'a' => out.push_str(WEEKDAY_NAMES_SHORT[b.weekday as usize]),
                'j' => out.push_str(&format!("{:03}", b.yearday + 1)),
                '%' => out.push('%'),
                _ => {
                    out.push('%');
                    out.push(next);
                }
            }
        } else {
            out.push(c);
        }
    }
    Val::String(out)
}

/// `Date.fromString s`: parse a date string in `ctime` format
/// (e.g. `"Wed Mar 08 19:06:45 1995"`).
pub(crate) fn from_string(s: &str) -> Val {
    let trimmed = s.trim();
    let parts: Vec<&str> = trimmed.split_ascii_whitespace().collect();
    if parts.len() != 5 {
        return Val::Unit;
    }
    let weekday = parts[0];
    if !WEEKDAY_NAMES_SHORT.contains(&weekday) {
        return Val::Unit;
    }
    let month = match MONTH_NAMES_SHORT.iter().position(|m| *m == parts[1]) {
        Some(i) => (i as u32) + 1,
        None => return Val::Unit,
    };
    let day: u32 = match parts[2].parse() {
        Ok(d) => d,
        _ => return Val::Unit,
    };
    let time_parts: Vec<&str> = parts[3].split(':').collect();
    if time_parts.len() != 3 {
        return Val::Unit;
    }
    let hour: u32 = match time_parts[0].parse() {
        Ok(h) => h,
        _ => return Val::Unit,
    };
    let minute: u32 = match time_parts[1].parse() {
        Ok(m) => m,
        _ => return Val::Unit,
    };
    let second: u32 = match time_parts[2].parse() {
        Ok(s) => s,
        _ => return Val::Unit,
    };
    let year: i32 = match parts[4].parse() {
        Ok(y) => y,
        _ => return Val::Unit,
    };
    if !(1..=days_in_month(year, month)).contains(&day)
        || hour >= 24
        || minute >= 60
        || second >= 60
    {
        return Val::Unit;
    }
    let days = days_from_civil(year, month, day);
    let secs = days * SECS_PER_DAY
        + hour as i64 * SECS_PER_HOUR
        + minute as i64 * SECS_PER_MIN
        + second as i64;
    Val::Some(Box::new(Val::Date(secs * NS_PER_SEC)))
}

/// Helper: avoid unused-import warning for Prop/PropVal until the
/// timezone-aware implementation lands.
#[allow(dead_code)]
fn _use_prop(p: Option<PropVal>, _: Prop) -> Option<PropVal> {
    p
}

#[allow(dead_code)]
const _USE_VAL: usize = val::CONTINUOUS_SET_ORDINAL;
