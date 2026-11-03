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

//! Morel values as Arrow record batches, which is how Spark Connect
//! carries the rows of a local relation and of a result.
//!
//! Port of morel-java's `ArrowEncoder`. A row is a list of its fields
//! in Morel's order (sorted by label), an `option` is the only type
//! that admits a null, and the Morel type decides what Spark type a
//! column has, as [`crate::spark::schema`] decides it for the schema
//! beside the batch. The two must agree, since the schema says what
//! the bytes mean.

use crate::compile::postfix::peel_type;
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::decimal::Decimal;
use crate::eval::spark::SparkError;
use crate::eval::val::Val;
use crate::spark::schema::{
    self, DECIMAL_PRECISION, DECIMAL_SCALE, option_value_type,
};
use arrow_array::{
    ArrayRef, BooleanArray, Decimal128Array, Float64Array, Int32Array,
    RecordBatch, StringArray,
};
use arrow_ipc::writer::StreamWriter;
use arrow_schema::{DataType, Field, Schema};
use std::fmt::Display;
use std::rc::Rc;
use std::sync::Arc;

/// Encodes rows as one Arrow IPC stream, schema and all.
///
/// Each row is a list of fields in label order, or a value if the row
/// type is not a record.
pub fn encode(rows: &[Val], row_type: &Type) -> Result<Vec<u8>, SparkError> {
    let columns = columns(row_type);
    let mut fields = Vec::new();
    for (label, t) in &columns {
        fields.push(field(label, t)?);
    }
    let schema = Arc::new(Schema::new(fields));
    let has_columns = schema::fields(row_type).is_some();
    let mut arrays: Vec<ArrayRef> = Vec::new();
    for (c, (_, t)) in columns.iter().enumerate() {
        let cells: Vec<&Val> = rows
            .iter()
            .map(|row| {
                if has_columns {
                    &row.expect_list()[c]
                } else {
                    row
                }
            })
            .collect();
        arrays.push(column(&cells, t)?);
    }
    let batch = RecordBatch::try_new(Arc::clone(&schema), arrays)
        .map_err(write_error)?;
    let mut out = Vec::new();
    {
        let mut writer =
            StreamWriter::try_new(&mut out, &schema).map_err(write_error)?;
        writer.write(&batch).map_err(write_error)?;
        writer.finish().map_err(write_error)?;
    }
    Ok(out)
}

fn write_error(e: impl Display) -> SparkError {
    SparkError::new("CONNECTION", format!("Error writing Arrow data: {}", e))
}

/// Returns the label and Morel type of each column of a row type. A
/// collection of values rather than records has one column, which is
/// named as Spark names the one column of a scalar result.
fn columns(row_type: &Type) -> Vec<(String, Rc<Type>)> {
    schema::fields(row_type)
        .unwrap_or_else(|| vec![("it".to_string(), Rc::new(row_type.clone()))])
}

/// Returns the Arrow field for one column.
fn field(label: &str, t: &Type) -> Result<Field, SparkError> {
    let value_type = option_value_type(t)?;
    let nullable = value_type.is_some();
    let data_type = arrow_type(value_type.as_deref().unwrap_or(t))?;
    Ok(Field::new(label, data_type, nullable))
}

/// Returns the Arrow type of a Morel type.
fn arrow_type(t: &Type) -> Result<DataType, SparkError> {
    if schema::is_decimal(t) {
        return Ok(DataType::Decimal128(DECIMAL_PRECISION, DECIMAL_SCALE));
    }
    match peel_type(t) {
        Type::Primitive(PrimitiveType::Bool) => Ok(DataType::Boolean),
        Type::Primitive(PrimitiveType::Int) => Ok(DataType::Int32),
        Type::Primitive(PrimitiveType::Real) => Ok(DataType::Float64),
        Type::Primitive(PrimitiveType::String) => Ok(DataType::Utf8),
        _ => Err(schema::no_equivalent(t)),
    }
}

/// Returns the value inside an option, or `None` for `NONE`; or the
/// value itself if the column is not an option.
fn cell(v: &Val, option: bool) -> Option<&Val> {
    if !option {
        return Some(v);
    }
    match v {
        Val::Some(inner) => Some(inner),
        _ => None,
    }
}

/// Builds the array of one column.
fn column(cells: &[&Val], t: &Type) -> Result<ArrayRef, SparkError> {
    let value_type = option_value_type(t)?;
    let option = value_type.is_some();
    let t = value_type.as_deref().unwrap_or(t);
    let values = || cells.iter().map(|v| cell(v, option));
    if schema::is_decimal(t) {
        let mut column = Vec::new();
        for v in values() {
            column.push(match v {
                Some(Val::Decimal(d)) => Some(decimal(d)?),
                _ => None,
            });
        }
        let array = Decimal128Array::from(column)
            .with_precision_and_scale(DECIMAL_PRECISION, DECIMAL_SCALE)
            .map_err(write_error)?;
        return Ok(Arc::new(array));
    }
    Ok(match peel_type(t) {
        Type::Primitive(PrimitiveType::Bool) => Arc::new(BooleanArray::from(
            values()
                .map(|v| v.map(Val::expect_bool))
                .collect::<Vec<_>>(),
        )),
        Type::Primitive(PrimitiveType::Int) => Arc::new(Int32Array::from(
            values().map(|v| v.map(Val::expect_int)).collect::<Vec<_>>(),
        )),
        Type::Primitive(PrimitiveType::Real) => Arc::new(Float64Array::from(
            values()
                .map(|v| v.map(|v| v.expect_real() as f64))
                .collect::<Vec<_>>(),
        )),
        Type::Primitive(PrimitiveType::String) => Arc::new(StringArray::from(
            values()
                .map(|v| v.map(|v| v.expect_string().to_string()))
                .collect::<Vec<_>>(),
        )),
        _ => return Err(schema::no_equivalent(t)),
    })
}

/// Returns a decimal as the unscaled value of a `decimal(38, 18)`.
///
/// Every value of a column has to carry the column's scale, so each is
/// restated at it. A value that cannot be -- more fractional digits
/// than the scale, or more digits than the precision -- is refused,
/// because the alternative is to round it and send something the
/// program did not say.
fn decimal(d: &Decimal) -> Result<i128, SparkError> {
    let (neg, digits, exp) = d.parts();
    if digits.is_empty() {
        return Ok(0);
    }
    let shown = d.to_string_with('-');
    let width = format!("decimal({}, {})", DECIMAL_PRECISION, DECIMAL_SCALE);
    // The value is digits * 10^exp, so at scale 18 its unscaled value
    // is digits * 10^(exp + 18).
    let shift = exp + DECIMAL_SCALE as i32;
    if shift < 0 {
        return Err(SparkError::new(
            "UNSUPPORTED_TYPE",
            format!(
                "Decimal {} has more digits after the point than Spark's \
                 {} can hold",
                shown, width
            ),
        ));
    }
    if digits.len() + shift as usize > DECIMAL_PRECISION as usize {
        return Err(SparkError::new(
            "UNSUPPORTED_TYPE",
            format!(
                "Decimal {} has more digits than Spark's {} can hold",
                shown, width
            ),
        ));
    }
    let mut unscaled: i128 = digits.parse().map_err(write_error)?;
    for _ in 0..shift {
        unscaled *= 10;
    }
    Ok(if neg { -unscaled } else { unscaled })
}

// End arrow.rs
