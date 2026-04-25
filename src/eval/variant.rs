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

//! Support for the `variant` built-in datatype and the `Variant`
//! structure.

use crate::compile::types::{Label, PrimitiveType, Type, TypeVariable};
use crate::eval::val::Val;
use std::collections::BTreeMap;

/// Wraps a value with its inner type into a `Val::Variant`.
pub(crate) fn variant_of(inner_type: Type, value: Val) -> Val {
    Val::Variant(Box::new((inner_type, value)))
}

/// `Variant.UNIT`.
pub(crate) fn unit() -> Val {
    variant_of(Type::Primitive(PrimitiveType::Unit), Val::Unit)
}

/// Returns a fresh polymorphic type variable, used as the inner type
/// of `VARIANT_NONE` (which has type `'a option variant`).
fn fresh_var() -> Type {
    Type::Variable(TypeVariable::new(0))
}

/// `Variant.VARIANT_NONE`: returns a variant whose inner type is
/// `'a option` and whose value is `Val::Unit` (the runtime form of `NONE`).
pub(crate) fn none() -> Val {
    variant_of(
        Type::Data("option".to_string(), vec![fresh_var()]),
        Val::Unit,
    )
}

/// `Variant.VARIANT_SOME v`: wraps an existing variant `v` into a
/// variant whose inner type is `<v inner type> option` and whose value is
/// `SOME v.value`.
pub(crate) fn some(arg: Val) -> Val {
    let (inner_type, inner_val) = match arg {
        Val::Variant(boxed) => *boxed,
        _ => panic!("Expected variant, got {:?}", arg),
    };
    variant_of(
        Type::Data("option".to_string(), vec![inner_type]),
        Val::Some(Box::new(inner_val)),
    )
}

/// `Variant.LIST xs`: wraps a list of variants into a variant of type
/// `T list` where `T` is the common inner type if all elements share one,
/// otherwise `variant`. The unwrapped element values become the contents.
pub(crate) fn list(arg: Val) -> Val {
    collection(arg, |t| Type::List(Box::new(t)))
}

/// `Variant.BAG xs`: like [`list`] but produces a bag.
pub(crate) fn bag(arg: Val) -> Val {
    collection(arg, |t| Type::Bag(Box::new(t)))
}

/// `Variant.VECTOR xs`: like [`list`] but produces a vector. (Vectors
/// share the runtime list representation.)
pub(crate) fn vector(arg: Val) -> Val {
    // Vectors use Type::Data("vector", [elem]) since there is no
    // dedicated Type::Vector variant.
    collection(arg, |t| Type::Data("vector".to_string(), vec![t]))
}

fn collection(arg: Val, wrap_type: impl FnOnce(Type) -> Type) -> Val {
    let items: Vec<Val> = match arg {
        Val::List(items) => items,
        _ => panic!("Expected list of variants, got {:?}", arg),
    };
    let element_type = common_element_type(&items);
    let unwrapped: Vec<Val> = items
        .into_iter()
        .map(|v| match v {
            Val::Variant(boxed) => boxed.1,
            _ => panic!("Expected variant element, got {:?}", v),
        })
        .collect();
    variant_of(wrap_type(element_type), Val::List(unwrapped))
}

/// Returns the common inner type of a list of variants. If they all
/// agree, returns that type; otherwise returns `variant`.
fn common_element_type(items: &[Val]) -> Type {
    let mut iter = items.iter().filter_map(|v| match v {
        Val::Variant(boxed) => Some(&boxed.0),
        _ => None,
    });
    let Some(first) = iter.next() else {
        // Empty list — fall back to a fresh type variable so the
        // displayed type is, e.g., `'a list variant`.
        return fresh_var();
    };
    let first = first.clone();
    if iter.all(|t| t == &first) {
        first
    } else {
        Type::Data("variant".to_string(), vec![])
    }
}

/// `Variant.RECORD pairs`: takes a list of `(label, variant)` pairs and
/// returns a variant whose inner type is a record with each field typed
/// according to the variant's inner type, and whose value is a list of
/// the unwrapped field values (the runtime representation of records).
pub(crate) fn record(arg: Val) -> Val {
    let pairs: Vec<Val> = match arg {
        Val::List(items) => items,
        _ => panic!("Expected list of (label, variant) pairs, got {:?}", arg),
    };
    let mut fields: BTreeMap<Label, Type> = BTreeMap::new();
    let mut values: Vec<(Label, Val)> = Vec::with_capacity(pairs.len());
    for pair in pairs {
        let (label, variant_val) = match pair {
            Val::List(parts) if parts.len() == 2 => {
                let mut iter = parts.into_iter();
                (iter.next().unwrap(), iter.next().unwrap())
            }
            _ => panic!("Expected pair of (label, variant), got {:?}", pair),
        };
        let label_str = match label {
            Val::String(s) => s,
            _ => panic!("Expected string label, got {:?}", label),
        };
        let label = Label::from(label_str);
        let (inner_type, inner_val) = expect_variant(&variant_val);
        fields.insert(label.clone(), inner_type.clone());
        values.push((label, inner_val.clone()));
    }
    // Records are stored at runtime as a list of values in the order of
    // sorted labels (matching how the BTreeMap iterates).
    let mut sorted: Vec<(Label, Val)> = values;
    sorted.sort_by(|a, b| a.0.cmp(&b.0));
    let value_list = Val::List(sorted.into_iter().map(|(_, v)| v).collect());
    variant_of(Type::Record(false, fields), value_list)
}

/// `Variant.CONSTANT name`: a constructor representing a nullary
/// constructor of an arbitrary datatype, identified by name.
pub(crate) fn constant(arg: Val) -> Val {
    let name = match arg {
        Val::String(s) => s,
        _ => panic!("Expected string, got {:?}", arg),
    };
    // The inner type is "the named datatype" — but at this layer we
    // don't know which datatype. Use a placeholder Named type with no
    // arguments.
    variant_of(
        Type::Named(vec![], name.clone()),
        Val::Constructor(0, Box::new(Val::Unit)),
    )
}

/// `Variant.CONSTRUCT (name, payload)`: a constructor representing a
/// unary constructor of an arbitrary datatype, identified by name and
/// payload variant.
pub(crate) fn construct(arg: Val) -> Val {
    let parts = match arg {
        Val::List(items) if items.len() == 2 => items,
        _ => panic!("Expected (name, variant) pair, got {:?}", arg),
    };
    let mut iter = parts.into_iter();
    let name = match iter.next().unwrap() {
        Val::String(s) => s,
        other => panic!("Expected string name, got {:?}", other),
    };
    let payload = iter.next().unwrap();
    let (_inner_type, inner_val) = expect_variant(&payload);
    variant_of(
        Type::Named(vec![], name.clone()),
        Val::Constructor(0, Box::new(inner_val.clone())),
    )
}

fn expect_variant(v: &Val) -> (&Type, &Val) {
    match v {
        Val::Variant(boxed) => (&boxed.0, &boxed.1),
        _ => panic!("Expected variant, got {:?}", v),
    }
}
