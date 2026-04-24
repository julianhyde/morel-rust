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

//! Discrete ordered types: enumeration of successor/predecessor and
//! min/max values for types used in `Range.discreteSetOf`.
//!
//! Port of `Discrete.java` and `Discretes.java` from morel-java commit
//! b4a0c4b1.
//!
//! Covers `int`, `char`, `bool`, `unit`; tuples/records of discretes;
//! and `'a descending` where `'a` is discrete. Sum types (`order`,
//! `either`, `option`, user-defined enums) land in a follow-up commit
//! because morel-rust represents each as a distinct `Val` variant, not
//! the uniform `Val::Constructor` used for user datatypes.

use crate::compile::types::{PrimitiveType, Type};
use crate::eval::char::Char;
use crate::eval::val::{self, Val};
use std::sync::Arc;

/// Represents a discrete ordered type: each value (except the max) has
/// a unique successor. Analogous to Guava's `DiscreteDomain`.
pub trait Discrete: Send + Sync {
    /// Returns the successor of `v`, or `None` if `v` is the maximum
    /// value of this type.
    fn next(&self, v: &Val) -> Option<Val>;
    /// Returns the predecessor of `v`, or `None` if `v` is the minimum
    /// value of this type.
    fn prev(&self, v: &Val) -> Option<Val>;
    /// Returns the minimum value of this type, or `None` if unbounded.
    fn min_value(&self) -> Option<Val>;
    /// Returns the maximum value of this type, or `None` if unbounded.
    fn max_value(&self) -> Option<Val>;
}

pub struct IntDiscrete;

impl Discrete for IntDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        let n = v.expect_int();
        if n == i32::MAX {
            None
        } else {
            Some(Val::Int(n + 1))
        }
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        let n = v.expect_int();
        if n == i32::MIN {
            None
        } else {
            Some(Val::Int(n - 1))
        }
    }
    fn min_value(&self) -> Option<Val> {
        Some(Val::Int(i32::MIN))
    }
    fn max_value(&self) -> Option<Val> {
        Some(Val::Int(i32::MAX))
    }
}

pub struct CharDiscrete;

impl Discrete for CharDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        let c = v.expect_char();
        let code = c as u32;
        if code >= Char::MAX_ORD as u32 {
            None
        } else {
            char::from_u32(code + 1).map(Val::Char)
        }
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        let c = v.expect_char();
        let code = c as u32;
        if code == 0 {
            None
        } else {
            char::from_u32(code - 1).map(Val::Char)
        }
    }
    fn min_value(&self) -> Option<Val> {
        Some(Val::Char('\u{0000}'))
    }
    fn max_value(&self) -> Option<Val> {
        char::from_u32(Char::MAX_ORD as u32).map(Val::Char)
    }
}

pub struct BoolDiscrete;

impl Discrete for BoolDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        if v.expect_bool() {
            None
        } else {
            Some(Val::Bool(true))
        }
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        if v.expect_bool() {
            Some(Val::Bool(false))
        } else {
            None
        }
    }
    fn min_value(&self) -> Option<Val> {
        Some(Val::Bool(false))
    }
    fn max_value(&self) -> Option<Val> {
        Some(Val::Bool(true))
    }
}

pub struct UnitDiscrete;

impl Discrete for UnitDiscrete {
    fn next(&self, _v: &Val) -> Option<Val> {
        None
    }
    fn prev(&self, _v: &Val) -> Option<Val> {
        None
    }
    fn min_value(&self) -> Option<Val> {
        Some(Val::Unit)
    }
    fn max_value(&self) -> Option<Val> {
        Some(Val::Unit)
    }
}

/// Discrete for a tuple / record: lexicographic step on the rightmost
/// component, carrying into the next component on overflow.
pub struct TupleDiscrete {
    components: Vec<Arc<dyn Discrete>>,
}

impl TupleDiscrete {
    fn step(&self, v: &Val, forward: bool) -> Option<Val> {
        let values = v.expect_list();
        let n = self.components.len();
        for i in (0..n).rev() {
            let stepped = if forward {
                self.components[i].next(&values[i])
            } else {
                self.components[i].prev(&values[i])
            };
            if let Some(s) = stepped {
                let mut result: Vec<Val> = values.to_vec();
                result[i] = s;
                for (j, slot) in
                    result.iter_mut().enumerate().skip(i + 1).take(n - i - 1)
                {
                    let extreme = if forward {
                        self.components[j].min_value()
                    } else {
                        self.components[j].max_value()
                    };
                    *slot = extreme?;
                }
                return Some(Val::List(result));
            }
        }
        None
    }

    fn extreme(&self, min: bool) -> Option<Val> {
        let mut out: Vec<Val> = Vec::with_capacity(self.components.len());
        for d in &self.components {
            let x = if min { d.min_value() } else { d.max_value() }?;
            out.push(x);
        }
        Some(Val::List(out))
    }
}

impl Discrete for TupleDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        self.step(v, true)
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        self.step(v, false)
    }
    fn min_value(&self) -> Option<Val> {
        self.extreme(true)
    }
    fn max_value(&self) -> Option<Val> {
        self.extreme(false)
    }
}

/// Discrete for the `'a descending` datatype: next/prev are swapped
/// from the inner discrete order.
pub struct DescendingDiscrete {
    inner: Arc<dyn Discrete>,
}

impl Discrete for DescendingDiscrete {
    fn next(&self, v: &Val) -> Option<Val> {
        let inner_val = match v {
            Val::Constructor(val::DESC_ORDINAL, inner) => inner.as_ref(),
            _ => panic!("DescendingDiscrete::next: expected DESC value"),
        };
        self.inner
            .prev(inner_val)
            .map(|x| Val::Constructor(val::DESC_ORDINAL, Box::new(x)))
    }
    fn prev(&self, v: &Val) -> Option<Val> {
        let inner_val = match v {
            Val::Constructor(val::DESC_ORDINAL, inner) => inner.as_ref(),
            _ => panic!("DescendingDiscrete::prev: expected DESC value"),
        };
        self.inner
            .next(inner_val)
            .map(|x| Val::Constructor(val::DESC_ORDINAL, Box::new(x)))
    }
    fn min_value(&self) -> Option<Val> {
        self.inner
            .max_value()
            .map(|x| Val::Constructor(val::DESC_ORDINAL, Box::new(x)))
    }
    fn max_value(&self) -> Option<Val> {
        self.inner
            .min_value()
            .map(|x| Val::Constructor(val::DESC_ORDINAL, Box::new(x)))
    }
}

/// Returns a `Discrete` for the given type, or an error describing why
/// the type is not discrete. The error message starts with `"not a
/// discrete type: "` followed by the offending type.
pub fn discrete_for(type_: &Type) -> Result<Arc<dyn Discrete>, String> {
    match type_ {
        Type::Primitive(p) => match p {
            PrimitiveType::Int => Ok(Arc::new(IntDiscrete)),
            PrimitiveType::Char => Ok(Arc::new(CharDiscrete)),
            PrimitiveType::Bool => Ok(Arc::new(BoolDiscrete)),
            PrimitiveType::Unit => Ok(Arc::new(UnitDiscrete)),
            _ => Err(format!("not a discrete type: {}", type_)),
        },
        Type::Tuple(ts) => {
            let components: Result<Vec<_>, _> =
                ts.iter().map(discrete_for).collect();
            Ok(Arc::new(TupleDiscrete {
                components: components?,
            }))
        }
        Type::Record(_, fields) => {
            let components: Result<Vec<_>, _> =
                fields.values().map(discrete_for).collect();
            Ok(Arc::new(TupleDiscrete {
                components: components?,
            }))
        }
        Type::Named(args, name) | Type::Data(name, args) => {
            if name == "descending" && !args.is_empty() {
                let inner = discrete_for(&args[0])?;
                Ok(Arc::new(DescendingDiscrete { inner }))
            } else {
                // Sum types (order, either, option, user-defined
                // enums) are not yet supported. Their morel-rust `Val`
                // representations are special and will land in a
                // follow-up commit.
                Err(format!("not a discrete type: {}", type_))
            }
        }
        _ => Err(format!("not a discrete type: {}", type_)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_next_prev() {
        let d = IntDiscrete;
        assert_eq!(d.next(&Val::Int(3)), Some(Val::Int(4)));
        assert_eq!(d.prev(&Val::Int(3)), Some(Val::Int(2)));
        assert_eq!(d.next(&Val::Int(i32::MAX)), None);
        assert_eq!(d.prev(&Val::Int(i32::MIN)), None);
    }

    #[test]
    fn bool_steps() {
        let d = BoolDiscrete;
        assert_eq!(d.next(&Val::Bool(false)), Some(Val::Bool(true)));
        assert_eq!(d.next(&Val::Bool(true)), None);
        assert_eq!(d.prev(&Val::Bool(false)), None);
        assert_eq!(d.min_value(), Some(Val::Bool(false)));
        assert_eq!(d.max_value(), Some(Val::Bool(true)));
    }

    #[test]
    fn tuple_bool_bool_enumeration() {
        // bool * bool has 4 values: (F,F), (F,T), (T,F), (T,T).
        let d = TupleDiscrete {
            components: vec![Arc::new(BoolDiscrete), Arc::new(BoolDiscrete)],
        };
        let mut v = d.min_value().unwrap();
        let mut seen = vec![v.clone()];
        while let Some(next) = d.next(&v) {
            seen.push(next.clone());
            v = next;
        }
        assert_eq!(seen.len(), 4);
        assert_eq!(
            seen[0],
            Val::List(vec![Val::Bool(false), Val::Bool(false)])
        );
        assert_eq!(seen[3], Val::List(vec![Val::Bool(true), Val::Bool(true)]));
    }

    #[test]
    fn descending_reverses() {
        let d = DescendingDiscrete {
            inner: Arc::new(IntDiscrete),
        };
        let desc_3 = Val::Constructor(val::DESC_ORDINAL, Box::new(Val::Int(3)));
        let desc_2 = Val::Constructor(val::DESC_ORDINAL, Box::new(Val::Int(2)));
        // next(DESC 3) = DESC 2 (reversed).
        assert_eq!(d.next(&desc_3), Some(desc_2));
    }

    #[test]
    fn real_is_not_discrete() {
        match discrete_for(&Type::Primitive(PrimitiveType::Real)) {
            Err(msg) => assert_eq!(msg, "not a discrete type: real"),
            Ok(_) => panic!("expected error"),
        }
    }

    #[test]
    fn string_is_not_discrete() {
        match discrete_for(&Type::Primitive(PrimitiveType::String)) {
            Err(msg) => assert_eq!(msg, "not a discrete type: string"),
            Ok(_) => panic!("expected error"),
        }
    }
}
