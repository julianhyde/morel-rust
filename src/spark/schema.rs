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

//! The Spark schema of a Morel type, as the JSON that a
//! `LocalRelation` carries; and the questions about Morel types that
//! the translator and the Arrow codec ask.
//!
//! Port of morel-java's `SparkSchema`. Spark to Morel loses
//! information -- `byte`, `short`, `int` and `long` all arrive as `int`
//! -- so Morel to Spark must choose, and it chooses the widest type
//! that Morel can hold without loss: `int` becomes `integer` and `real`
//! becomes `double`. A Spark column is nullable or not; a Morel type
//! says so by being an `option`, and an option of an option cannot be
//! expressed.

use crate::compile::postfix::peel_type;
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::spark::SparkError;
use std::rc::Rc;

/// Precision of an uploaded decimal column: Spark's own default, 38.
pub const DECIMAL_PRECISION: u8 = 38;

/// Scale of an uploaded decimal column: Spark's own default, 18.
pub const DECIMAL_SCALE: i8 = 18;

/// Returns the fields of a record or tuple type, in the order the
/// type holds them (sorted by label), or `None` if the type is not one.
pub fn fields(t: &Type) -> Option<Vec<(String, Rc<Type>)>> {
    match peel_type(t) {
        Type::Record(_, fields) => Some(
            fields
                .iter()
                .map(|(l, t)| (l.to_string(), Rc::clone(t)))
                .collect(),
        ),
        Type::Tuple(types) => Some(
            types
                .iter()
                .enumerate()
                .map(|(i, t)| ((i + 1).to_string(), Rc::clone(t)))
                .collect(),
        ),
        _ => None,
    }
}

/// Returns the element type of a collection type.
pub fn element_type(t: &Type) -> Option<Rc<Type>> {
    match peel_type(t) {
        Type::List(e) | Type::Bag(e) => Some(Rc::clone(e)),
        _ => None,
    }
}

/// Returns whether a type is `decimal`.
pub fn is_decimal(t: &Type) -> bool {
    match peel_type(t) {
        Type::Data(name, args) | Type::Named(args, name) => {
            name == "decimal" && args.is_empty()
        }
        _ => false,
    }
}

/// Returns the type an `option` wraps, or `None` if `t` is not an
/// option. An option of an option has no Spark equivalent, since a
/// column is nullable or not, and is rejected rather than flattened.
pub fn option_value_type(t: &Type) -> Result<Option<Rc<Type>>, SparkError> {
    match peel_type(t) {
        Type::Data(name, args) | Type::Named(args, name)
            if name == "option" && args.len() == 1 =>
        {
            let value_type = Rc::clone(&args[0]);
            if option_value_type(&value_type)?.is_some() {
                return Err(SparkError::new(
                    "UNSUPPORTED_TYPE",
                    format!("Morel type {} is an option of an option", t),
                ));
            }
            Ok(Some(value_type))
        }
        _ => Ok(None),
    }
}

/// Returns the JSON schema of a row type, as `LocalRelation.schema`
/// wants it: an object whose `fields` are the record's fields, in the
/// order the record type holds them.
pub fn schema_json(row_type: &Type) -> Result<String, SparkError> {
    let record = match peel_type(row_type) {
        Type::Record(..) => fields(row_type),
        _ => None,
    };
    let Some(fields) = record else {
        return Err(SparkError::new(
            "UNSUPPORTED_TYPE",
            format!(
                "A relation's rows must be records, and these are {}",
                row_type
            ),
        ));
    };
    let mut b = String::new();
    struct_(&fields, &mut b)?;
    Ok(b)
}

fn struct_(
    fields: &[(String, Rc<Type>)],
    b: &mut String,
) -> Result<(), SparkError> {
    b.push_str("{\"fields\":[");
    for (i, (name, t)) in fields.iter().enumerate() {
        if i > 0 {
            b.push(',');
        }
        b.push_str("{\"metadata\":{},\"name\":");
        quote(name, b);
        let value_type = option_value_type(t)?;
        b.push_str(",\"nullable\":");
        b.push_str(if value_type.is_some() {
            "true"
        } else {
            "false"
        });
        b.push_str(",\"type\":");
        type_(value_type.as_ref().unwrap_or(t), b)?;
        b.push('}');
    }
    b.push_str("],\"type\":\"struct\"}");
    Ok(())
}

fn type_(t: &Type, b: &mut String) -> Result<(), SparkError> {
    match peel_type(t) {
        Type::Record(..) => {
            struct_(&fields(t).unwrap_or_default(), b)?;
        }
        Type::List(element_type) => {
            let value_type = option_value_type(element_type)?;
            b.push_str("{\"containsNull\":");
            b.push_str(if value_type.is_some() {
                "true"
            } else {
                "false"
            });
            b.push_str(",\"elementType\":");
            type_(value_type.as_ref().unwrap_or(element_type), b)?;
            b.push_str(",\"type\":\"array\"}");
        }
        _ => quote(&primitive(t)?, b),
    }
    Ok(())
}

/// Appends a JSON string literal.
fn quote(s: &str, b: &mut String) {
    b.push('"');
    for c in s.chars() {
        if c == '"' || c == '\\' {
            b.push('\\');
        }
        b.push(c);
    }
    b.push('"');
}

fn primitive(t: &Type) -> Result<String, SparkError> {
    if is_decimal(t) {
        // Morel's decimal has no precision or scale of its own, so a
        // column of them has to be given one: the width Spark itself
        // gives a column it infers from a BigDecimal. A value too wide
        // for it is refused rather than rounded.
        return Ok(format!("decimal({},{})", DECIMAL_PRECISION, DECIMAL_SCALE));
    }
    match peel_type(t) {
        Type::Primitive(PrimitiveType::Bool) => Ok("boolean".to_string()),
        Type::Primitive(PrimitiveType::Int) => Ok("integer".to_string()),
        Type::Primitive(PrimitiveType::Real) => Ok("double".to_string()),
        Type::Primitive(PrimitiveType::String) => Ok("string".to_string()),
        _ => Err(no_equivalent(t)),
    }
}

/// The error for a Morel type that Spark has no type for.
pub fn no_equivalent(t: &Type) -> SparkError {
    SparkError::new(
        "UNSUPPORTED_TYPE",
        format!("Morel type {} has no Spark equivalent", t),
    )
}

// End schema.rs
