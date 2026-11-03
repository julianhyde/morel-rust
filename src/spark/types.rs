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

//! Maps Spark types to Morel types.
//!
//! Port of morel-java's `SparkTypes`. A nullable type maps to
//! `option`, except at the top level of a row, where Spark's flag is
//! true of every column of a stored table and therefore says nothing;
//! there, a column is an option only if something declared it so.

use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::spark::SparkError;
use crate::spark::proto::DataType;
use crate::spark::proto::data_type::{Kind, Struct};
use std::collections::{BTreeMap, HashSet};
use std::rc::Rc;

/// Returns the Morel type of a row of the given struct type, where the
/// columns named in `nullable_columns` (in lower case, or `*` for all)
/// are declared nullable and therefore map to `option`.
pub fn row_type(
    schema: &DataType,
    nullable_columns: &HashSet<String>,
) -> Result<Rc<Type>, SparkError> {
    match &schema.kind {
        Some(Kind::Struct(s)) => struct_(s, false, nullable_columns),
        _ => Err(SparkError::new(
            "UNSUPPORTED_TYPE",
            format!("Expected a struct, got {}", describe(schema)),
        )),
    }
}

/// Returns `option` of a type.
pub fn option(t: Rc<Type>) -> Rc<Type> {
    Rc::new(Type::Data("option".to_string(), vec![t]))
}

fn named(name: &str) -> Rc<Type> {
    Rc::new(Type::Data(name.to_string(), Vec::new()))
}

/// Returns the Morel type of a Spark type; a nullable value maps to
/// `option` if `strict`, which it is inside an array, struct or map.
fn to_type_nullable(
    t: &DataType,
    nullable: bool,
    strict: bool,
) -> Result<Rc<Type>, SparkError> {
    let t = to_type(t)?;
    Ok(if nullable && strict { option(t) } else { t })
}

fn to_type(t: &DataType) -> Result<Rc<Type>, SparkError> {
    let primitive = |p| Ok(Rc::new(Type::Primitive(p)));
    match &t.kind {
        Some(Kind::Boolean(_)) => primitive(PrimitiveType::Bool),
        Some(
            Kind::Byte(_) | Kind::Short(_) | Kind::Integer(_) | Kind::Long(_),
        ) => primitive(PrimitiveType::Int),
        Some(Kind::Float(_) | Kind::Double(_)) => {
            primitive(PrimitiveType::Real)
        }
        Some(Kind::Decimal(_)) => Ok(named("decimal")),
        Some(Kind::String(_) | Kind::Char(_) | Kind::VarChar(_)) => {
            primitive(PrimitiveType::String)
        }
        Some(Kind::Binary(_)) => Ok(Rc::new(Type::List(Rc::new(
            Type::Primitive(PrimitiveType::Word),
        )))),
        Some(Kind::Date(_) | Kind::TimestampNtz(_)) => Ok(named("date")),
        Some(Kind::Timestamp(_)) => Ok(named("time")),
        Some(Kind::Array(array)) => {
            let element_type =
                array.element_type.as_deref().cloned().unwrap_or_default();
            Ok(Rc::new(Type::List(to_type_nullable(
                &element_type,
                array.contains_null,
                true,
            )?)))
        }
        Some(Kind::Struct(s)) => struct_(s, true, &HashSet::new()),
        _ => Err(SparkError::new(
            "UNSUPPORTED_TYPE",
            format!("Spark type {} has no Morel equivalent", describe(t)),
        )),
    }
}

fn struct_(
    s: &Struct,
    strict: bool,
    nullable_columns: &HashSet<String>,
) -> Result<Rc<Type>, SparkError> {
    let mut names = HashSet::new();
    let mut fields = BTreeMap::new();
    for field in &s.fields {
        if !names.insert(field.name.clone()) {
            return Err(SparkError::new(
                "UNSUPPORTED_TYPE",
                format!("Duplicate field name {}", field.name),
            ));
        }
        // One level down -- inside a struct, an array or a map --
        // Spark's flag is recorded rather than inferred, so believe it;
        // at the top level of a row it is true of everything, so believe
        // the declaration instead. "*" is a declaration of every column.
        let nullable = if strict {
            field.nullable
        } else {
            nullable_columns.contains("*")
                || nullable_columns.contains(&field.name.to_lowercase())
        };
        let data_type = field.data_type.clone().unwrap_or_default();
        fields.insert(
            Label::from(field.name.as_str()),
            to_type_nullable(&data_type, nullable, true)?,
        );
    }
    Ok(Rc::new(Type::Record(false, fields)))
}

/// Describes a Spark type, for error messages, e.g.
/// `map<string,integer>`.
pub fn describe(t: &DataType) -> String {
    let Some(kind) = &t.kind else {
        return "kind_not_set".to_string();
    };
    match kind {
        Kind::Decimal(d) => format!(
            "decimal({},{})",
            d.precision.unwrap_or(0),
            d.scale.unwrap_or(0)
        ),
        Kind::Array(a) => format!(
            "array<{}>",
            describe(&a.element_type.as_deref().cloned().unwrap_or_default())
        ),
        Kind::Map(m) => format!(
            "map<{},{}>",
            describe(&m.key_type.as_deref().cloned().unwrap_or_default()),
            describe(&m.value_type.as_deref().cloned().unwrap_or_default())
        ),
        Kind::Struct(s) => {
            let fields: Vec<String> = s
                .fields
                .iter()
                .map(|f| {
                    format!(
                        "{}:{}",
                        f.name,
                        describe(&f.data_type.clone().unwrap_or_default())
                    )
                })
                .collect();
            format!("struct<{}>", fields.join(","))
        }
        Kind::Null(_) => "null".to_string(),
        Kind::Binary(_) => "binary".to_string(),
        Kind::Boolean(_) => "boolean".to_string(),
        Kind::Byte(_) => "byte".to_string(),
        Kind::Short(_) => "short".to_string(),
        Kind::Integer(_) => "integer".to_string(),
        Kind::Long(_) => "long".to_string(),
        Kind::Float(_) => "float".to_string(),
        Kind::Double(_) => "double".to_string(),
        Kind::String(_) => "string".to_string(),
        Kind::Char(_) => "char".to_string(),
        Kind::VarChar(_) => "var_char".to_string(),
        Kind::Date(_) => "date".to_string(),
        Kind::Timestamp(_) => "timestamp".to_string(),
        Kind::TimestampNtz(_) => "timestamp_ntz".to_string(),
        Kind::CalendarInterval(_) => "calendar_interval".to_string(),
        Kind::YearMonthInterval(_) => "year_month_interval".to_string(),
        Kind::DayTimeInterval(_) => "day_time_interval".to_string(),
        Kind::Variant(_) => "variant".to_string(),
        Kind::Udt(_) => "udt".to_string(),
        Kind::Unparsed(_) => "unparsed".to_string(),
    }
}

// End types.rs
