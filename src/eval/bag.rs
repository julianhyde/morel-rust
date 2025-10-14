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
use crate::eval::code::{Code, EvalEnv, Frame, Span};
use crate::eval::order::Order;
use crate::eval::val::Val;
use crate::shell::main::MorelError;
use std::cmp::Ordering;

/// Support for the `bag` built-in type and the `Bag` structure.
pub struct Bag;

impl Bag {
    // lint: sort until '#}' where '##pub'

    /// Applies f to each element x of the bag b, in arbitrary order, until
    /// f(x) evaluates to false; it returns false if such an x exists and true
    /// otherwise.
    pub(crate) fn all(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        bag: &[Val],
    ) -> Result<bool, MorelError> {
        // Bags are unordered, so we can iterate in any order
        for v in bag {
            let result = func.eval_f1(r, f, v)?;
            if !result.expect_bool() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Applies f to the elements of b, in arbitrary order.
    pub(crate) fn app(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        bag: &[Val],
    ) -> Result<(), MorelError> {
        for v in bag {
            func.eval_f1(r, f, v)?;
        }
        Ok(())
    }

    /// Computes the Morel expression `bag1 @ bag2` (concatenation).
    pub(crate) fn at(bag1: &[Val], bag2: &[Val]) -> Vec<Val> {
        let mut bag = bag1.to_vec();
        bag.extend_from_slice(bag2);
        bag
    }

    /// Performs lexicographic comparison of the two bags using the given
    /// ordering f on the bag elements.
    pub(crate) fn collate(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        bag1: &[Val],
        bag2: &[Val],
    ) -> Result<Order, MorelError> {
        // For bags, we compare lexicographically just like lists
        for (v1, v2) in bag1.iter().zip(bag2.iter()) {
            let pair = Val::List(vec![v1.clone(), v2.clone()]);
            let result = func.eval_f1(r, f, &pair)?;
            let order = result.expect_order();
            if order.0 != Ordering::Equal {
                return Ok(order);
            }
        }
        // All elements compared equal, so compare lengths.
        Ok(Order(bag1.len().cmp(&bag2.len())))
    }

    /// Returns the bag that is the concatenation of all the bags in b.
    pub(crate) fn concat(bags: &[Val]) -> Vec<Val> {
        let mut result = Vec::new();
        for val in bags {
            if let Val::List(bag) = val {
                result.extend_from_slice(bag);
            }
        }
        result
    }

    /// Returns what is left after dropping an arbitrary i elements of the bag.
    /// Raises Subscript if i < 0 or i > length b.
    pub(crate) fn drop(
        bag: &[Val],
        i: i32,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if i < 0 || i > bag.len() as i32 {
            Err(MorelError::Runtime(BuiltInExn::Subscript, span.clone()))
        } else {
            // Drop from the front (arbitrary choice for bags)
            Ok(Val::List(bag[i as usize..].to_vec()))
        }
    }

    /// Applies f to each element x of the bag b, in arbitrary order, until
    /// f(x) evaluates to true; it returns true if such an x exists and false
    /// otherwise.
    pub(crate) fn exists(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        bag: &[Val],
    ) -> Result<bool, MorelError> {
        for v in bag {
            let result = func.eval_f1(r, f, v)?;
            if result.expect_bool() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Applies f to each element x of b and returns the bag of those x for
    /// which f x evaluated to true.
    pub(crate) fn filter(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        bag: &[Val],
    ) -> Result<Val, MorelError> {
        let mut result = Vec::new();
        for v in bag {
            let keep = func.eval_f1(r, f, v)?;
            if keep.expect_bool() {
                result.push(v.clone());
            }
        }
        Ok(Val::List(result))
    }

    /// Applies f to each element x of the bag b, in arbitrary order, until
    /// f x evaluates to true. Returns SOME (x) if such an x exists;
    /// otherwise returns NONE.
    pub(crate) fn find(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        bag: &[Val],
    ) -> Result<Val, MorelError> {
        for v in bag {
            let result = func.eval_f1(r, f, v)?;
            if result.expect_bool() {
                return Ok(Val::Some(Box::new(v.clone())));
            }
        }
        Ok(Val::Unit) // NONE
    }

    /// `fold f init (bag [x1, x2, ..., xn])` returns
    /// `f(xn, ... , f(x2, f(x1, init))...)` (for some arbitrary reordering)
    /// or `init` if the bag is empty.
    pub(crate) fn fold(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        init: &Val,
        bag: &[Val],
    ) -> Result<Val, MorelError> {
        let mut acc = init.clone();
        for v in bag {
            let pair = Val::List(vec![v.clone(), acc]);
            acc = func.eval_f1(r, f, &pair)?;
        }
        Ok(acc)
    }

    /// Converts a list to a bag.
    pub(crate) fn from_list(list: &[Val]) -> Vec<Val> {
        list.to_vec()
    }

    /// Returns NONE if the bag is empty, and SOME (hd b, tl b) otherwise
    /// (where hd and tl choose/remove the same arbitrary element).
    pub(crate) fn get_item(bag: &[Val]) -> Val {
        if bag.is_empty() {
            Val::Unit // NONE
        } else {
            // Pick an arbitrary element (first one)
            Val::Some(Box::new(Val::List(vec![
                bag[0].clone(),
                Val::List(bag[1..].to_vec()),
            ])))
        }
    }

    /// Returns an arbitrary element of the bag.
    /// Raises Empty if the bag is empty.
    pub(crate) fn hd(bag: &[Val], span: &Span) -> Result<Val, MorelError> {
        if bag.is_empty() {
            Err(MorelError::Runtime(BuiltInExn::Empty, span.clone()))
        } else {
            // Pick an arbitrary element (first one)
            Ok(bag[0].clone())
        }
    }

    /// Returns the number of elements in the bag.
    pub(crate) fn length(bag: &[Val]) -> i32 {
        bag.len() as i32
    }

    /// Applies f to each element of b, returning the bag of results.
    pub(crate) fn map(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        bag: &[Val],
    ) -> Result<Val, MorelError> {
        let results: Result<Vec<Val>, _> =
            bag.iter().map(|v| func.eval_f1(r, f, v)).collect();
        Ok(Val::List(results?))
    }

    /// Applies f to each element of b, returning a bag of results,
    /// with SOME stripped, where f was defined.
    pub(crate) fn map_partial(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        bag: &[Val],
    ) -> Result<Val, MorelError> {
        let mut result = Vec::new();
        for v in bag {
            let mapped = func.eval_f1(r, f, v)?;
            // If the result is SOME, unwrap it and add to result.
            if let Val::Some(boxed_val) = mapped {
                result.push(*boxed_val);
            }
            // If NONE (Val::Unit), skip it.
        }
        Ok(Val::List(result))
    }

    /// Returns true if the bag is empty.
    pub(crate) fn null(bag: &[Val]) -> bool {
        bag.is_empty()
    }

    /// Applies f to each element x of b, in arbitrary order, and returns a
    /// pair (pos, neg) where pos is the bag of those x for which f x
    /// evaluated to true, and neg is the bag of those for which f x
    /// evaluated to false.
    pub(crate) fn partition(
        r: &mut EvalEnv,
        f: &mut Frame,
        func: &Code,
        bag: &[Val],
    ) -> Result<Val, MorelError> {
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        for v in bag {
            let result = func.eval_f1(r, f, v)?;
            if result.expect_bool() {
                pos.push(v.clone());
            } else {
                neg.push(v.clone());
            }
        }
        Ok(Val::List(vec![Val::List(pos), Val::List(neg)]))
    }

    /// Creates a bag by applying f to integers 0 through n-1.
    pub(crate) fn tabulate(
        r: &mut EvalEnv,
        f: &mut Frame,
        count: i32,
        fun: &Code,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if count < 0 {
            return Err(MorelError::Runtime(BuiltInExn::Size, span.clone()));
        }
        let mut bag = Vec::with_capacity(count as usize);
        for i in 0..count {
            let v = fun.eval_f1(r, f, &Val::Int(i))?;
            bag.push(v);
        }
        Ok(Val::List(bag))
    }

    /// Returns an arbitrary i elements of the bag.
    /// Raises Subscript if i < 0 or i > length b.
    pub(crate) fn take(
        bag: &[Val],
        i: i32,
        span: &Span,
    ) -> Result<Val, MorelError> {
        if i < 0 || i > bag.len() as i32 {
            Err(MorelError::Runtime(BuiltInExn::Subscript, span.clone()))
        } else {
            // Take from the front (arbitrary choice for bags)
            Ok(Val::List(bag[..i as usize].to_vec()))
        }
    }

    /// Returns all but one arbitrary element of the bag.
    /// Raises Empty if the bag is empty.
    pub(crate) fn tl(bag: &[Val], span: &Span) -> Result<Val, MorelError> {
        if bag.is_empty() {
            Err(MorelError::Runtime(BuiltInExn::Empty, span.clone()))
        } else {
            // Remove an arbitrary element (first one)
            Ok(Val::List(bag[1..].to_vec()))
        }
    }

    /// Converts a bag to a list.
    pub(crate) fn to_list(bag: &[Val]) -> Vec<Val> {
        bag.to_vec()
    }
}
