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

//! Bound endpoints for ranges, and merging logic used by
//! `Range.continuousSetOf` / `Range.discreteSetOf`.
//!
//! Port of `Bound.java` from morel-java commit b4a0c4b1. Discrete-step
//! support (the `Discrete` interface) is not yet wired up; it lands in
//! a later commit with `Range.discreteSetOf`.

use crate::eval::comparator::Comparator;
use crate::eval::val::{self, Val};
use std::cmp::Ordering;

/// One endpoint of a range: either unbounded (representing −∞ or +∞)
/// or a specific value with inclusivity.
#[derive(Clone, Debug)]
pub struct Bound {
    /// The endpoint value, or `None` if unbounded.
    pub value: Option<Val>,
    /// Whether the endpoint is inclusive (`>=` or `<=`). Only meaningful
    /// when `value` is `Some`.
    pub inclusive: bool,
}

impl Bound {
    /// Sentinel representing an unbounded endpoint.
    pub const UNBOUNDED: Self = Self {
        value: None,
        inclusive: false,
    };

    /// Returns an inclusive bound at `v`.
    pub fn inclusive(v: Val) -> Self {
        Self {
            value: Some(v),
            inclusive: true,
        }
    }

    /// Returns an exclusive bound at `v`.
    pub fn exclusive(v: Val) -> Self {
        Self {
            value: Some(v),
            inclusive: false,
        }
    }

    /// Extracts the lower `Bound` from a runtime range value.
    pub fn lower(range: &Val) -> Self {
        let (ord, inner) = match range {
            Val::Constructor(ord, inner) => (*ord, inner.as_ref()),
            _ => panic!("Bound::lower: not a range value"),
        };
        match ord {
            val::RANGE_ALL_ORDINAL
            | val::RANGE_AT_MOST_ORDINAL
            | val::RANGE_LESS_THAN_ORDINAL => Self::UNBOUNDED,
            val::RANGE_POINT_ORDINAL | val::RANGE_AT_LEAST_ORDINAL => {
                Self::inclusive(inner.clone())
            }
            val::RANGE_CLOSED_ORDINAL | val::RANGE_CLOSED_OPEN_ORDINAL => {
                Self::inclusive(inner.expect_list()[0].clone())
            }
            val::RANGE_GREATER_THAN_ORDINAL => Self::exclusive(inner.clone()),
            val::RANGE_OPEN_ORDINAL | val::RANGE_OPEN_CLOSED_ORDINAL => {
                Self::exclusive(inner.expect_list()[0].clone())
            }
            _ => panic!("Bound::lower: unknown range constructor {}", ord),
        }
    }

    /// Extracts the upper `Bound` from a runtime range value.
    pub fn upper(range: &Val) -> Self {
        let (ord, inner) = match range {
            Val::Constructor(ord, inner) => (*ord, inner.as_ref()),
            _ => panic!("Bound::upper: not a range value"),
        };
        match ord {
            val::RANGE_ALL_ORDINAL
            | val::RANGE_AT_LEAST_ORDINAL
            | val::RANGE_GREATER_THAN_ORDINAL => Self::UNBOUNDED,
            val::RANGE_POINT_ORDINAL | val::RANGE_AT_MOST_ORDINAL => {
                Self::inclusive(inner.clone())
            }
            val::RANGE_CLOSED_ORDINAL | val::RANGE_OPEN_CLOSED_ORDINAL => {
                Self::inclusive(inner.expect_list()[1].clone())
            }
            val::RANGE_LESS_THAN_ORDINAL => Self::exclusive(inner.clone()),
            val::RANGE_OPEN_ORDINAL | val::RANGE_CLOSED_OPEN_ORDINAL => {
                Self::exclusive(inner.expect_list()[1].clone())
            }
            _ => panic!("Bound::upper: unknown range constructor {}", ord),
        }
    }

    /// Converts a lower-upper `Bound` pair to a runtime range value.
    pub fn to_range(lo: &Self, hi: &Self) -> Val {
        match (&lo.value, &hi.value) {
            (None, None) => {
                Val::Constructor(val::RANGE_ALL_ORDINAL, Box::new(Val::Unit))
            }
            (None, Some(h)) => {
                let ord = if hi.inclusive {
                    val::RANGE_AT_MOST_ORDINAL
                } else {
                    val::RANGE_LESS_THAN_ORDINAL
                };
                Val::Constructor(ord, Box::new(h.clone()))
            }
            (Some(l), None) => {
                let ord = if lo.inclusive {
                    val::RANGE_AT_LEAST_ORDINAL
                } else {
                    val::RANGE_GREATER_THAN_ORDINAL
                };
                Val::Constructor(ord, Box::new(l.clone()))
            }
            (Some(l), Some(h)) => {
                if lo.inclusive && hi.inclusive && l == h {
                    return Val::Constructor(
                        val::RANGE_POINT_ORDINAL,
                        Box::new(l.clone()),
                    );
                }
                let ord = match (lo.inclusive, hi.inclusive) {
                    (true, true) => val::RANGE_CLOSED_ORDINAL,
                    (true, false) => val::RANGE_CLOSED_OPEN_ORDINAL,
                    (false, true) => val::RANGE_OPEN_CLOSED_ORDINAL,
                    (false, false) => val::RANGE_OPEN_ORDINAL,
                };
                Val::Constructor(
                    ord,
                    Box::new(Val::List(vec![l.clone(), h.clone()])),
                )
            }
        }
    }

    /// Compares this lower bound with `other` (earlier/smaller first).
    /// An unbounded lower bound sorts before all finite bounds. Among
    /// bounds with the same value, inclusive sorts before exclusive.
    pub fn compare_lower(
        &self,
        other: &Self,
        cmp: &dyn Comparator,
    ) -> Ordering {
        match (&self.value, &other.value) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some(a), Some(b)) => match cmp.compare(a, b) {
                Ordering::Equal => match (self.inclusive, other.inclusive) {
                    (true, false) => Ordering::Less,
                    (false, true) => Ordering::Greater,
                    _ => Ordering::Equal,
                },
                other => other,
            },
        }
    }

    /// Returns whether this upper bound reaches or exceeds `next` (the
    /// lower bound of the next range), meaning the two ranges overlap or
    /// touch.
    pub fn can_merge(&self, next: &Self, cmp: &dyn Comparator) -> bool {
        match (&self.value, &next.value) {
            (None, _) | (_, None) => true,
            (Some(a), Some(b)) => match cmp.compare(a, b) {
                Ordering::Greater => true,
                Ordering::Less => false,
                Ordering::Equal => self.inclusive || next.inclusive,
            },
        }
    }

    /// Returns the greater of this upper bound and `other`.
    pub fn max(&self, other: &Self, cmp: &dyn Comparator) -> Self {
        match (&self.value, &other.value) {
            (None, _) | (_, None) => Self::UNBOUNDED,
            (Some(a), Some(b)) => match cmp.compare(a, b) {
                Ordering::Greater => self.clone(),
                Ordering::Less => other.clone(),
                Ordering::Equal => {
                    if self.inclusive {
                        self.clone()
                    } else {
                        other.clone()
                    }
                }
            },
        }
    }
}

/// Converts a list of runtime range values into a normalized list:
/// sorts by lower bound, then merges overlapping or touching ranges.
/// Returns the merged ranges as `Val::List` of range constructors.
///
/// Discrete-step merging (for `discreteSetOf`) is not yet implemented;
/// this function covers only the continuous case.
pub fn from_ranges(ranges: &[Val], cmp: &dyn Comparator) -> Vec<Val> {
    let mut pairs: Vec<(Bound, Bound)> = ranges
        .iter()
        .map(|r| (Bound::lower(r), Bound::upper(r)))
        .collect();
    if pairs.len() < 2 {
        return pairs
            .iter()
            .map(|(lo, hi)| Bound::to_range(lo, hi))
            .collect();
    }
    pairs.sort_by(|a, b| a.0.compare_lower(&b.0, cmp));

    let mut result: Vec<(Bound, Bound)> = Vec::new();
    let (mut lo, mut hi) = pairs[0].clone();
    for (next_lo, next_hi) in pairs.into_iter().skip(1) {
        if hi.can_merge(&next_lo, cmp) {
            hi = hi.max(&next_hi, cmp);
        } else {
            result.push((lo, hi));
            lo = next_lo;
            hi = next_hi;
        }
    }
    result.push((lo, hi));
    result
        .iter()
        .map(|(lo, hi)| Bound::to_range(lo, hi))
        .collect()
}
