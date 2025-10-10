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
use crate::eval::code::Span;
use crate::eval::order::Order;
use crate::eval::val::Val;
use crate::shell::main::MorelError;

/// Support for the `real` built-in type and the `Real` structure.
pub struct Real;

impl Real {
    /// Computes the Morel expression `Real.abs r`.
    ///
    /// Returns the absolute value of `r`.
    pub(crate) fn abs(r: f32) -> f32 {
        r.abs()
    }

    /// Computes the Morel expression `Real.ceil r`.
    ///
    /// Produces ceil(r), the smallest int not less than `r`.
    #[allow(clippy::if_same_then_else)]
    pub(crate) fn ceil(r: f32, span: &Span) -> Result<Val, MorelError> {
        let result = r.ceil();
        if result.is_infinite() || result.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else if result < i32::MIN as f32 || result > i32::MAX as f32 {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else {
            Ok(Val::Int(result as i32))
        }
    }

    /// Computes the Morel expression `Real.checkFloat x`.
    ///
    /// Raises `Overflow` if x is an infinity, and raises `Div` if x is NaN.
    /// Otherwise, it returns its argument.
    pub(crate) fn check_float(x: f32, span: &Span) -> Result<Val, MorelError> {
        if x.is_infinite() {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else if x.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Div, span.clone()))
        } else {
            Ok(Val::Real(x))
        }
    }

    /// Computes the Morel expression `Real.compare (x, y)`.
    ///
    /// Returns `LESS`, `EQUAL`, or `GREATER` according to whether its first
    /// argument is less than, equal to, or greater than the second.
    /// It raises `IEEEReal.Unordered` on unordered arguments.
    pub(crate) fn compare(
        x: f32,
        y: f32,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if x.is_nan() || y.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Unordered, span.clone()))
        } else if x < y {
            Ok(Val::Int(Order::Less as i32))
        } else if x > y {
            Ok(Val::Int(Order::Greater as i32))
        } else {
            Ok(Val::Int(Order::Equal as i32))
        }
    }

    /// Computes the Morel expression `Real.copySign (x, y)`.
    ///
    /// Returns `x` with the sign of `y`, even if `y` is NaN.
    pub(crate) fn copy_sign(x: f32, y: f32) -> f32 {
        x.copysign(y)
    }

    /// Computes the Morel expression `Real.floor r`.
    ///
    /// Produces floor(r), the largest int not larger than `r`.
    #[allow(clippy::if_same_then_else)]
    pub(crate) fn floor(r: f32, span: &Span) -> Result<Val, MorelError> {
        let result = r.floor();
        if result.is_infinite() || result.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else if result < i32::MIN as f32 || result > i32::MAX as f32 {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else {
            Ok(Val::Int(result as i32))
        }
    }

    /// Computes the Morel expression `Real.fromInt i`.
    ///
    /// Converts the integer `i` to a `real` value.
    pub(crate) fn from_int(i: i32) -> f32 {
        i as f32
    }

    /// Computes the Morel expression `Real.fromManExp {exp, man}`.
    ///
    /// Returns the real value constructed from mantissa and exponent.
    pub(crate) fn from_man_exp(man: f32, exp: i32) -> f32 {
        man * 2_f32.powi(exp)
    }

    /// Computes the Morel expression `Real.fromString s`.
    ///
    /// Scans a `real` value from a string.
    pub(crate) fn from_string(s: &str) -> Val {
        let trimmed = s.trim_start();
        if let Ok(r) = trimmed.parse::<f32>() {
            Val::Some(Box::new(Val::Real(r)))
        } else {
            Val::Unit // NONE
        }
    }

    /// Computes the Morel expression `Real.isFinite x`.
    ///
    /// Returns true if x is neither NaN nor an infinity.
    pub(crate) fn is_finite(x: f32) -> bool {
        x.is_finite()
    }

    /// Computes the Morel expression `Real.isNan x`.
    ///
    /// Returns true if x is NaN.
    pub(crate) fn is_nan(x: f32) -> bool {
        x.is_nan()
    }

    /// Computes the Morel expression `Real.isNormal x`.
    ///
    /// Returns true if x is normal, i.e., neither zero, subnormal,
    /// infinite nor NaN.
    pub(crate) fn is_normal(x: f32) -> bool {
        x.is_normal()
    }

    /// Computes the Morel expression `Real.max (x, y)`.
    ///
    /// Returns the larger of the arguments. If exactly one argument is NaN,
    /// returns the other argument. If both arguments are NaN, returns NaN.
    pub(crate) fn max(x: f32, y: f32) -> f32 {
        if x.is_nan() && y.is_nan() {
            f32::NAN
        } else if x.is_nan() {
            y
        } else if y.is_nan() {
            x
        } else {
            x.max(y)
        }
    }

    /// Computes the Morel expression `Real.min (x, y)`.
    ///
    /// Returns the smaller of the arguments. If exactly one argument is NaN,
    /// returns the other argument. If both arguments are NaN, returns NaN.
    pub(crate) fn min(x: f32, y: f32) -> f32 {
        if x.is_nan() && y.is_nan() {
            f32::NAN
        } else if x.is_nan() {
            y
        } else if y.is_nan() {
            x
        } else {
            x.min(y)
        }
    }

    /// Computes the Morel expression `Real.realCeil r`.
    ///
    /// Produces ceil(r), the smallest integer not less than `r`.
    pub(crate) fn real_ceil(r: f32) -> f32 {
        r.ceil()
    }

    /// Computes the Morel expression `Real.realFloor r`.
    ///
    /// Produces floor(r), the largest integer not larger than `r`.
    pub(crate) fn real_floor(r: f32) -> f32 {
        r.floor()
    }

    /// Computes the Morel expression `Real.realMod r`.
    ///
    /// Returns the fractional part of `r`.
    pub(crate) fn real_mod(r: f32) -> f32 {
        r.fract()
    }

    /// Computes the Morel expression `Real.realRound r`.
    ///
    /// Rounds to the integer-valued real value that is nearest to `r`.
    /// In the case of a tie, it rounds to the nearest even integer.
    pub(crate) fn real_round(r: f32) -> f32 {
        r.round()
    }

    /// Computes the Morel expression `Real.realTrunc r`.
    ///
    /// Rounds `r` towards zero.
    pub(crate) fn real_trunc(r: f32) -> f32 {
        r.trunc()
    }

    /// Computes the Morel expression `Real.rem (x, y)`.
    ///
    /// Returns the remainder `x - n * y`, where `n` = `trunc (x / y)`.
    pub(crate) fn rem(x: f32, y: f32) -> f32 {
        if x.is_infinite() || y == 0.0 {
            f32::NAN
        } else if y.is_infinite() {
            x
        } else {
            let n = (x / y).trunc();
            x - n * y
        }
    }

    /// Computes the Morel expression `Real.round r`.
    ///
    /// Yields the integer nearest to `r`. In the case of a tie, it rounds
    /// to the nearest even integer.
    #[allow(clippy::if_same_then_else)]
    pub(crate) fn round(r: f32, span: &Span) -> Result<Val, MorelError> {
        let result = r.round();
        if result.is_infinite() || result.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else if result < i32::MIN as f32 || result > i32::MAX as f32 {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else {
            Ok(Val::Int(result as i32))
        }
    }

    /// Computes the Morel expression `Real.sameSign (r1, r2)`.
    ///
    /// Returns true if and only if `signBit r1` equals `signBit r2`.
    pub(crate) fn same_sign(r1: f32, r2: f32) -> bool {
        r1.is_sign_positive() == r2.is_sign_positive()
    }

    /// Computes the Morel expression `Real.sign r`.
    ///
    /// Returns ~1 if r is negative, 0 if r is zero, or 1 if r is positive.
    /// An infinity returns its sign; a zero returns 0 regardless of its sign.
    /// It raises `Domain` on NaN.
    pub(crate) fn sign(r: f32, span: &Span) -> Result<Val, MorelError> {
        if r.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Domain, span.clone()))
        } else if r == 0.0 {
            Ok(Val::Int(0))
        } else if r > 0.0 {
            Ok(Val::Int(1))
        } else {
            Ok(Val::Int(-1))
        }
    }

    /// Computes the Morel expression `Real.signBit r`.
    ///
    /// Returns true if and only if the sign of `r` (infinities, zeros,
    /// and NaN, included) is negative.
    pub(crate) fn sign_bit(r: f32) -> bool {
        r.is_sign_negative()
    }

    /// Computes the Morel expression `Real.split r`.
    ///
    /// Returns `{frac, whole}`, where `frac` and `whole` are the fractional
    /// and integral parts of `r`, respectively.
    pub(crate) fn split(r: f32) -> Val {
        let whole = r.trunc();
        let frac = r - whole;
        Val::List(vec![Val::Real(frac), Val::Real(whole)])
    }

    /// Computes the Morel expression `Real.trunc r`.
    ///
    /// Rounds r towards zero.
    #[allow(clippy::if_same_then_else)]
    pub(crate) fn trunc(r: f32, span: &Span) -> Result<Val, MorelError> {
        let result = r.trunc();
        if result.is_infinite() || result.is_nan() {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else if result < i32::MIN as f32 || result > i32::MAX as f32 {
            Err(MorelError::Runtime(BuiltInExn::Overflow, span.clone()))
        } else {
            Ok(Val::Int(result as i32))
        }
    }

    /// Computes the Morel expression `Real.toManExp r`.
    ///
    /// Returns `{man, exp}`, where `man` and `exp` are the mantissa
    /// and exponent of r, respectively.
    pub(crate) fn to_man_exp(r: f32) -> Val {
        if r == 0.0 || r.is_infinite() || r.is_nan() {
            Val::List(vec![Val::Real(r), Val::Int(0)])
        } else {
            let exp = r.abs().log2().floor() as i32;
            let man = r / 2_f32.powi(exp);
            Val::List(vec![Val::Real(man), Val::Int(exp)])
        }
    }

    /// Formats a real number for display in the REPL.
    /// Uses `~` for both negative numbers and negative exponents.
    pub(crate) fn display(r: f32) -> String {
        if r.is_nan() {
            "nan".to_string()
        } else if r.is_infinite() {
            if r > 0.0 {
                "inf".to_string()
            } else {
                "~inf".to_string()
            }
        } else if r == 0.0 {
            // Handle negative zero specially
            if r.is_sign_negative() {
                "~0".to_string()
            } else {
                "0".to_string()
            }
        } else {
            // Use scientific notation for very large or very small numbers
            let abs = r.abs();
            if !(1e-5..1e7).contains(&abs) {
                // Format in scientific notation with uppercase E
                // Rust's default precision for {:E} prints only
                // significant digits
                let s = format!("{:E}", r);
                // Replace leading - with ~ and E- with E~
                let s = if let Some(stripped) = s.strip_prefix('-') {
                    format!("~{}", stripped)
                } else {
                    s
                };
                s.replace("E-", "E~")
            } else if r.fract() == 0.0 && abs < i64::MAX as f32 {
                // Whole numbers display without .0
                if r.is_sign_negative() {
                    format!("~{}", -r.trunc() as i64)
                } else {
                    format!("{}", r.trunc() as i64)
                }
            } else {
                // For non-whole numbers, use default formatting
                let s = format!("{}", r);
                // Replace negative sign with ~
                s.replace('-', "~")
            }
        }
    }

    /// Computes the Morel expression `Real.toString r`.
    ///
    /// Converts a `real` into a `string`.
    /// Returns a string suitable for parsing back as a real number.
    /// Uses `~` for negative numbers but `-` for negative exponents.
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn to_string(r: f32) -> String {
        if r.is_nan() {
            "nan".to_string()
        } else if r.is_infinite() {
            if r > 0.0 {
                "inf".to_string()
            } else {
                "~inf".to_string()
            }
        } else if r == 0.0 {
            if r.is_sign_negative() {
                "~0".to_string()
            } else {
                "0".to_string()
            }
        } else {
            // Use scientific notation for very large or very small numbers.
            let abs = r.abs();
            if !(1e-5..1e7).contains(&abs) {
                // Format in scientific notation with uppercase E.
                // Rust's default precision for '{:E}' prints only
                // significant digits.
                format!("{:E}", r).replace("-", "~")
            } else if r.fract() == 0.0 && abs < i64::MAX as f32 {
                // Whole numbers display without .0.
                format!("{}", r.trunc() as i64).replace("-", "~")
            } else {
                // For non-whole numbers, use default formatting.
                format!("{}", r).replace('-', "~")
            }
        }
    }

    /// Computes the Morel expression `Real.unordered (x, y)`.
    ///
    /// Returns true if x and y are unordered, i.e., at least one of
    /// x and y is NaN.
    pub(crate) fn unordered(x: f32, y: f32) -> bool {
        x.is_nan() || y.is_nan()
    }
}
