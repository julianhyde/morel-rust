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

//! Rules for evaluating constant expressions at compile time. It is
//! morel-java's `Folder`.

use crate::compile::core::Expr;
use crate::compile::library::BuiltInFunction;
use crate::compile::types::Type;
use crate::eval::code::Impl;
use crate::eval::val::Val;
use std::rc::Rc;

/// Returns whether a built-in function constructs a value, or converts a
/// value to another type without losing information, and so may be
/// evaluated at compile time if its argument is constant.
///
/// Not included: functions that round (`Real.floor`, `Decimal.toReal`)
/// or truncate (`Time.toSeconds`), which lose information; functions that
/// format or parse (`Int.toString`, `Date.fromString`); and functions
/// that depend on the environment (`Date.fromTimeLocal`, which depends on
/// the time zone).
pub(crate) fn is_foldable(f: BuiltInFunction) -> bool {
    matches!(
        f,
        BuiltInFunction::Bag
            | BuiltInFunction::BagFromList
            | BuiltInFunction::CharChr
            | BuiltInFunction::CharOrd
            | BuiltInFunction::DecimalDecimal
            | BuiltInFunction::DecimalFromInt
            | BuiltInFunction::DecimalFromReal
            | BuiltInFunction::IntFromInt
            | BuiltInFunction::IntFromLarge
            | BuiltInFunction::IntToInt
            | BuiltInFunction::IntToLarge
            | BuiltInFunction::Real
            | BuiltInFunction::RealFromInt
            | BuiltInFunction::StringStr
            | BuiltInFunction::TimeFromMicroseconds
            | BuiltInFunction::TimeFromMilliseconds
            | BuiltInFunction::TimeFromNanoseconds
            | BuiltInFunction::TimeFromSeconds
            | BuiltInFunction::Vector
            | BuiltInFunction::VectorFromList
            | BuiltInFunction::WordFromInt
            | BuiltInFunction::WordFromLargeWord
            | BuiltInFunction::WordToLargeWord
    )
}

/// Returns the value of a call to a foldable built-in whose argument is
/// a literal, as a literal; or `None` if the call cannot be folded here,
/// because the function is not foldable, the argument is not a literal,
/// the result is not a primitive or a `decimal`, the function needs the
/// environment to evaluate (as one that may raise does), or (for
/// `Real.fromInt`) the conversion would lose information.
///
/// A call that this declines may still be evaluated at compile time by
/// the compiler, which has an environment to evaluate it in.
pub(crate) fn fold_call(apply: &Expr) -> Option<Expr> {
    let Expr::Apply(t, f, arg, _) = apply else {
        return None;
    };
    let Expr::Literal(_, Val::Fn(builtin)) = f.as_ref() else {
        return None;
    };
    if !is_foldable(*builtin) || !is_lossless(*builtin, arg) {
        return None;
    }
    let Expr::Literal(_, value) = arg.as_ref() else {
        return None;
    };
    if !is_scalar(value) {
        return None;
    }
    let Impl::E1(eager) = builtin.get_impl() else {
        return None;
    };
    let result = eager.apply(value.clone());
    match (t.as_ref(), &result) {
        (Type::Primitive(_), _) | (_, Val::Decimal(_)) => {
            Some(Expr::Literal(t.clone(), result))
        }
        _ => None,
    }
}

/// Returns whether a value is a literal of a primitive type or a
/// `decimal`.
fn is_scalar(value: &Val) -> bool {
    matches!(
        value,
        Val::Bool(_)
            | Val::Char(_)
            | Val::Int(_)
            | Val::Real(_)
            | Val::String(_)
            | Val::Unit
            | Val::Word(_)
            | Val::Decimal(_)
    )
}

/// Returns whether a call to a foldable built-in loses no information.
///
/// Every foldable built-in is lossless, except `Real.fromInt` (and
/// `real`, which is the same function), because a
/// real has 24 bits of precision and cannot hold every int; so
/// `Real.fromInt 7` is folded, but not `Real.fromInt 16777217`.
pub(crate) fn is_lossless(f: BuiltInFunction, arg: &Expr) -> bool {
    if f != BuiltInFunction::RealFromInt && f != BuiltInFunction::Real {
        return true;
    }
    let Expr::Literal(_, Val::Int(i)) = arg else {
        return false;
    };
    // Compare as i64: `(*i as f32) as i32` saturates, so for the
    // largest int, whose float is 2^31, it would give the int back.
    (*i as f32) as i64 == i64::from(*i)
}

/// Returns whether an expression constructs a value from constants, and
/// so may be compiled to code that returns that value.
///
/// Such an expression is a literal (other than a function or a table,
/// which is read each time); a record, tuple or list whose elements are
/// constant; a datatype constructor applied to a constant; a call to a
/// foldable built-in (see [`is_foldable`]) with a constant argument; or a
/// field of a constant.
pub(crate) fn is_constant(e: &Expr) -> bool {
    match e {
        // A constructor of no argument, such as `NONE`, is a value.
        Expr::Literal(t, Val::Fn(builtin)) => {
            builtin.is_constructor() && !matches!(t.as_ref(), Type::Fn(..))
        }
        Expr::Literal(_, value) => is_scalar(value) || is_value(value),
        Expr::Tuple(_, args) | Expr::List(_, args) => {
            args.iter().all(is_constant)
        }
        // Look at the function before the argument, so that a call to
        // a function that cannot be folded does not scan its argument;
        // the compiler asks again of each argument.
        Expr::Apply(t, f, arg, _) => match f.as_ref() {
            Expr::Literal(_, Val::Fn(builtin)) => {
                (is_foldable(*builtin) && is_lossless(*builtin, arg)
                    || builtin.is_constructor() && !is_variant(t))
                    && is_constant(arg)
            }
            Expr::RecordSelector(..) => is_constant(arg),
            Expr::Identifier(_, name) => {
                is_constructor(t, name) && is_constant(arg)
            }
            _ => false,
        },
        _ => false,
    }
}

/// Returns whether a value is a structure of values that is the same
/// each time it is read: a list, an option, or a constructor applied to
/// such a value. Not a table, nor a function.
fn is_value(value: &Val) -> bool {
    match value {
        Val::List(items) => items.iter().all(|v| is_scalar(v) || is_value(v)),
        Val::Some(v) | Val::Inl(v) | Val::Inr(v) => is_scalar(v) || is_value(v),
        Val::Constructor(_, v) => is_scalar(v) || is_value(v),
        Val::Time(_) | Val::Date(..) | Val::Order(_) => true,
        _ => false,
    }
}

/// Returns whether a type is `variant`, whose values need a session to
/// construct.
fn is_variant(t: &Rc<Type>) -> bool {
    matches!(t.as_ref(), Type::Data(name, _) if name == "variant")
}

/// Returns whether an identifier applied to an argument, giving a value
/// of type `t`, is a constructor of a datatype other than `variant`.
fn is_constructor(t: &Rc<Type>, name: &str) -> bool {
    matches!(t.as_ref(), Type::Data(dt, _) if dt != "variant")
        && name.starts_with(|c: char| c.is_ascii_uppercase())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compile::types::PrimitiveType;

    #[test]
    fn real_from_int_is_lossless_only_where_a_real_holds_the_int() {
        let int = |i: i32| {
            Expr::Literal(
                Rc::new(Type::Primitive(PrimitiveType::Int)),
                Val::Int(i),
            )
        };
        let f = BuiltInFunction::RealFromInt;
        assert!(is_lossless(f, &int(7)));
        assert!(!is_lossless(f, &int(16_777_217)));
        assert!(!is_lossless(f, &int(i32::MAX)));
    }
}
