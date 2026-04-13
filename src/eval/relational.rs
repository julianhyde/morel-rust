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

use crate::eval::order::Order;
use crate::eval::val::Val;
use std::cmp::Ordering;

/// Support for the `Relational` structure.
pub struct Relational;

impl Relational {
    /// Returns `LESS`, `EQUAL`, or `GREATER` according to whether the first
    /// argument is less than, equal to, or greater than the second.
    ///
    /// Comparisons are based on the structure of the type. Primitive types
    /// are compared using their natural order; Option types compare with NONE
    /// last; Tuple types compare lexicographically; Record types compare
    /// lexicographically, with fields compared in alphabetical order; List
    /// values compare lexicographically; Bag values compare lexicographically.
    pub(crate) fn compare(a: &Val, b: &Val) -> Val {
        Val::Order(Order(Self::compare_vals(a, b)))
    }

    /// Internal comparison function that returns a Rust Ordering.
    fn compare_vals(a: &Val, b: &Val) -> Ordering {
        match (a, b) {
            // lint: sort until '#}' where '##\(Val::'
            (Val::Bool(a), Val::Bool(b)) => a.cmp(b),
            (Val::Char(a), Val::Char(b)) => a.cmp(b),
            (Val::Constructor(na, a), Val::Constructor(nb, b)) => {
                if na == nb {
                    // Same user-defined constructor: compare inner values.
                    if na.as_ref() == "DESC" {
                        // Descending: reverse the comparison of inner values.
                        Self::compare_vals(b, a)
                    } else {
                        Self::compare_vals(a, b)
                    }
                } else {
                    // Different constructors: compare by name (alphabetical
                    // as an approximation of declaration order).
                    na.cmp(nb)
                }
            }
            (Val::Inl(_), Val::Inr(_)) => Ordering::Less,
            (Val::Inl(a), Val::Inl(b)) => Self::compare_vals(a, b),
            (Val::Inr(_), Val::Inl(_)) => Ordering::Greater,
            (Val::Inr(a), Val::Inr(b)) => Self::compare_vals(a, b),
            (Val::Int(a), Val::Int(b)) => a.cmp(b),
            (Val::List(a), Val::List(b)) => Self::compare_lists(a, b),
            (Val::Order(a), Val::Order(b)) => a.cmp(b),
            (Val::Real(a), Val::Real(b)) => {
                a.partial_cmp(b).unwrap_or(Ordering::Equal)
            }
            // Option: NONE (Unit) < SOME.
            (Val::Some(_), Val::Unit) => Ordering::Greater,
            (Val::Some(a), Val::Some(b)) => Self::compare_vals(a, b),
            (Val::String(a), Val::String(b)) => a.cmp(b),
            (Val::Unit, Val::Some(_)) => Ordering::Less,
            (Val::Unit, Val::Unit) => Ordering::Equal,
            _ => Ordering::Equal,
        }
    }

    /// Compare two lists lexicographically.
    fn compare_lists(a: &[Val], b: &[Val]) -> Ordering {
        for (x, y) in a.iter().zip(b.iter()) {
            match Self::compare_vals(x, y) {
                Ordering::Equal => continue,
                other => return other,
            }
        }
        a.len().cmp(&b.len())
    }

    /// Returns the greatest element of the list.
    /// Throws Empty exception if the list is empty.
    pub(crate) fn max(list: &[Val]) -> Val {
        if list.is_empty() {
            panic!("Empty");
        }
        list.iter()
            .max_by(|a, b| Self::compare_vals(a, b))
            .unwrap()
            .clone()
    }

    /// Returns the least element of the list.
    /// Throws Empty exception if the list is empty.
    pub(crate) fn min(list: &[Val]) -> Val {
        if list.is_empty() {
            panic!("Empty");
        }
        list.iter()
            .min_by(|a, b| Self::compare_vals(a, b))
            .unwrap()
            .clone()
    }

    /// Returns the sole element of the list.
    /// Throws Empty exception if the list does not have exactly one element.
    pub(crate) fn only(list: &[Val]) -> Val {
        if list.len() != 1 {
            panic!("Empty");
        }
        list[0].clone()
    }
}
