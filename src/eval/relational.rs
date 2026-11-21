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
use crate::compile::span::Span;
use crate::eval::code::{EvalEnv, Frame};
use crate::eval::comparator::{Comparator, NaturalComparator};
use crate::eval::decimal::{self, Decimal};
use crate::eval::order::Order;
use crate::eval::val::Val;
use crate::shell::kernel::MorelError;

/// Support for the `Relational` structure.
pub struct Relational;

/// A statistic of a collection of numbers.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Stat {
    /// The mean.
    Avg,
    /// The population standard deviation.
    StddevPop,
    /// The sample standard deviation.
    StddevSamp,
    /// The population variance.
    VarPop,
    /// The sample variance.
    VarSamp,
}

/// How an aggregate treats its elements and an answer it cannot give.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Form {
    /// Over the elements; raises `Empty` where it has no answer.
    Plain,
    /// Over the elements; `SOME` of the answer, or `NONE` where it has
    /// none.
    Opt,
    /// Over the values of the `SOME` elements, ignoring `NONE`; `SOME` of
    /// the answer, or `NONE` where it has none. It is SQL's aggregate,
    /// which ignores nulls.
    Some,
}

/// Returns the values of the `SOME` elements of a list of options.
fn some_values(list: &[Val]) -> Vec<Val> {
    list.iter()
        .filter_map(|v| match v {
            Val::Some(x) => Some((**x).clone()),
            _ => None,
        })
        .collect()
}

/// Returns the elements an aggregate of the form `form` reads.
fn values_of(list: &[Val], form: Form) -> Vec<Val> {
    if form == Form::Some {
        some_values(list)
    } else {
        list.to_vec()
    }
}

/// Returns the answer of an aggregate of the form `form`; `None` is
/// that it has no answer.
fn answer(
    form: Form,
    result: Option<Val>,
    span: &Span,
) -> Result<Val, MorelError> {
    match (form, result) {
        (Form::Plain, Some(v)) => Ok(v),
        (Form::Plain, None) => {
            Err(MorelError::Runtime(BuiltInExn::Empty, span.clone()))
        }
        (_, Some(v)) => Ok(Val::Some(Box::new(v))),
        (_, None) => Ok(Val::Unit),
    }
}

/// Returns a number as a double, for a statistic.
fn to_f64(v: &Val) -> f64 {
    match v {
        Val::Int(i) => f64::from(*i),
        Val::Real(x) => f64::from(*x),
        Val::Decimal(d) => d.to_string_with('-').parse().unwrap_or(f64::NAN),
        _ => panic!("not a number: {:?}", v),
    }
}

impl Relational {
    /// Returns a statistic of a collection of `int`, `real` or `decimal`
    /// values: `avg`, `stddevPop` and so on, in the form `form`.
    ///
    /// The mean of `int` values is a `real`, computed in double and
    /// rounded to `real` at the end; of `real` values, a `real`; of
    /// `decimal` values, a `decimal`, the exact sum divided by the
    /// count, rounded as `/` is. A standard deviation or variance is a
    /// `real`; a sample statistic needs at least two values, and a
    /// population statistic one.
    pub(crate) fn statistic(
        stat: Stat,
        form: Form,
        list: &[Val],
        span: &Span,
    ) -> Result<Val, MorelError> {
        let values = values_of(list, form);
        let n = values.len();
        let needed = match stat {
            Stat::StddevSamp | Stat::VarSamp => 2,
            _ => 1,
        };
        if n < needed {
            return answer(form, None, span);
        }
        if stat == Stat::Avg {
            if let Val::Decimal(_) = &values[0] {
                let decimals: Vec<Decimal> =
                    values.iter().map(|v| v.expect_decimal().clone()).collect();
                let overflow =
                    || MorelError::Runtime(BuiltInExn::Overflow, span.clone());
                let sum = decimal::sum(&decimals).ok_or_else(overflow)?;
                let count = Decimal::from_i32(n as i32);
                let mean = decimal::div(&sum, &count)
                    .ok()
                    .flatten()
                    .ok_or_else(overflow)?;
                return answer(form, Some(Val::Decimal(mean)), span);
            }
            let sum: f64 = values.iter().map(to_f64).sum();
            return answer(
                form,
                Some(Val::Real((sum / n as f64) as f32)),
                span,
            );
        }
        let mean = values.iter().map(to_f64).sum::<f64>() / n as f64;
        let sum_squares: f64 = values
            .iter()
            .map(|v| {
                let d = to_f64(v) - mean;
                d * d
            })
            .sum();
        let divisor = match stat {
            Stat::StddevSamp | Stat::VarSamp => n - 1,
            _ => n,
        };
        let variance = sum_squares / divisor as f64;
        let result = match stat {
            Stat::StddevPop | Stat::StddevSamp => variance.sqrt(),
            _ => variance,
        };
        answer(form, Some(Val::Real(result as f32)), span)
    }

    /// Returns how many elements of a collection of options are `SOME`.
    pub(crate) fn count_some(list: &[Val]) -> Val {
        Val::Int(some_values(list).len() as i32)
    }

    /// Returns the greatest (or, if `!greatest`, least) element, in the
    /// form `form`: `maxOpt`, `maxSome`, `minOpt`, `minSome`.
    pub(crate) fn extreme(
        greatest: bool,
        form: Form,
        list: &[Val],
        span: &Span,
    ) -> Result<Val, MorelError> {
        let values = values_of(list, form);
        let cmp = |a: &&Val, b: &&Val| NaturalComparator.compare(a, b);
        let result = if greatest {
            values.iter().max_by(cmp)
        } else {
            values.iter().min_by(cmp)
        };
        answer(form, result.cloned(), span)
    }

    /// Returns the sum of a collection of `int`, `real` or `decimal`
    /// values, in the form `form`: `sumOpt`, `sumSome`. The sum of no
    /// values is `NONE`.
    pub(crate) fn sum_form(
        form: Form,
        list: &[Val],
        span: &Span,
    ) -> Result<Val, MorelError> {
        let values = values_of(list, form);
        let sum = match values.first() {
            None => None,
            Some(Val::Int(_)) => {
                Some(Val::Int(values.iter().map(Val::expect_int).sum()))
            }
            Some(Val::Real(_)) => {
                Some(Val::Real(values.iter().map(Val::expect_real).sum()))
            }
            Some(_) => {
                let decimals: Vec<Decimal> =
                    values.iter().map(|v| v.expect_decimal().clone()).collect();
                let d = decimal::sum(&decimals).ok_or_else(|| {
                    MorelError::Runtime(BuiltInExn::Overflow, span.clone())
                })?;
                Some(Val::Decimal(d))
            }
        };
        answer(form, sum, span)
    }

    /// Fallback comparison using `NaturalComparator`. Prefer
    /// type-directed `Code::Compare` when the type is known at
    /// compile time.
    pub(crate) fn compare(a: &Val, b: &Val) -> Val {
        Val::Order(Order(NaturalComparator.compare(a, b)))
    }

    /// Fallback max using `NaturalComparator`.
    /// Returns the greatest element of the list.
    /// Throws Empty exception if the list is empty.
    pub(crate) fn max(list: &[Val], span: &Span) -> Result<Val, MorelError> {
        if list.is_empty() {
            return Err(MorelError::Runtime(BuiltInExn::Empty, span.clone()));
        }
        Ok(list
            .iter()
            .max_by(|a, b| NaturalComparator.compare(a, b))
            .unwrap()
            .clone())
    }

    /// Fallback min using `NaturalComparator`.
    /// Returns the least element of the list.
    /// Throws Empty exception if the list is empty.
    pub(crate) fn min(list: &[Val], span: &Span) -> Result<Val, MorelError> {
        if list.is_empty() {
            return Err(MorelError::Runtime(BuiltInExn::Empty, span.clone()));
        }
        Ok(list
            .iter()
            .min_by(|a, b| NaturalComparator.compare(a, b))
            .unwrap()
            .clone())
    }

    /// Returns the element of `list` for which `key_fn` gives the
    /// greatest key, or the least if `greatest` is false.
    ///
    /// The keys are compared as the shell orders values. Where several
    /// elements are tied, the first the traversal meets is returned, so
    /// for a bag -- whose order is arbitrary -- which one that is is not
    /// specified. Throws Empty if the list is empty.
    pub(crate) fn extreme_by(
        r: &mut EvalEnv,
        f: &mut Frame,
        key_fn: &Val,
        list: &[Val],
        greatest: bool,
        span: &Span,
    ) -> Result<Val, MorelError> {
        let Some((first, rest)) = list.split_first() else {
            return Err(MorelError::Runtime(BuiltInExn::Empty, span.clone()));
        };
        let mut best = first;
        let mut best_key = key_fn.apply_f1(r, f, first)?;
        for element in rest {
            let key = key_fn.apply_f1(r, f, element)?;
            let cmp = NaturalComparator.compare(&key, &best_key);
            if if greatest { cmp.is_gt() } else { cmp.is_lt() } {
                best = element;
                best_key = key;
            }
        }
        Ok(best.clone())
    }

    /// Returns the sole element of the list.
    /// Throws Size if more than one element, Empty if empty.
    pub(crate) fn only(list: &[Val], span: &Span) -> Result<Val, MorelError> {
        match list.len() {
            0 => Err(MorelError::Runtime(BuiltInExn::Empty, span.clone())),
            1 => Ok(list[0].clone()),
            _ => Err(MorelError::Runtime(BuiltInExn::Size, span.clone())),
        }
    }
}
