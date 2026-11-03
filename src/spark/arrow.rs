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
//! Port of morel-java's `ArrowEncoder` and `ArrowDecoder`. A row is a
//! list of its fields in Morel's order (sorted by label), an `option`
//! is the only type that admits a null, and the Morel type decides
//! what Spark type a column has, as [`crate::spark::schema`] decides
//! it for the schema beside the batch. The two must agree, since the
//! schema says what the bytes mean.

use crate::compile::postfix::peel_type;
use crate::compile::types::{PrimitiveType, Type};
use crate::eval::decimal::Decimal;
use crate::eval::decimal::parse_prefix;
use crate::eval::spark::SparkError;
use crate::eval::val::Val;
use crate::spark::schema::{
    self, DECIMAL_PRECISION, DECIMAL_SCALE, option_value_type,
};
use arrow_array::{
    Array, ArrayRef, BinaryArray, BooleanArray, Date32Array, Decimal128Array,
    Float32Array, Float64Array, Int8Array, Int16Array, Int32Array, Int64Array,
    LargeStringArray, ListArray, RecordBatch, StringArray, StringViewArray,
    StructArray, TimestampMicrosecondArray,
};
use arrow_ipc::reader::StreamReader;
use arrow_ipc::writer::StreamWriter;
use arrow_schema::{DataType, Field, Schema};
use std::fmt::Display;
use std::io::Cursor;
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

/// Decodes Arrow IPC streams, as Spark Connect sends them, into rows.
///
/// Port of morel-java's `ArrowDecoder`. Decoding is driven by the Morel
/// type: an `option` admits a null (as `NONE`), any other type does
/// not, and a null there raises `Spark` with class `NULL_VALUE`.
/// Integers of every width become `int` (raising if a `bigint` does not
/// fit), floats, doubles and decimals `real`, and so on.
///
/// `row_type` is a record type, or the type of the one column if a row
/// is not a record.
pub fn decode(
    batches: &[Vec<u8>],
    row_type: &Type,
) -> Result<Vec<Val>, SparkError> {
    let mut rows = Vec::new();
    for batch in batches {
        let reader = StreamReader::try_new(Cursor::new(batch), None)
            .map_err(read_error)?;
        for record_batch in reader {
            let record_batch = record_batch.map_err(read_error)?;
            decode_batch(&record_batch, row_type, &mut rows)?;
        }
    }
    Ok(rows)
}

fn read_error(e: impl Display) -> SparkError {
    SparkError::new("CONNECTION", format!("Error reading Arrow data: {}", e))
}

fn decode_batch(
    batch: &RecordBatch,
    row_type: &Type,
    rows: &mut Vec<Val>,
) -> Result<(), SparkError> {
    // Rows are numbered within the result, not within the batch: Spark
    // decides how many batches to send, so a batch-relative number would
    // name a different row depending on how the result arrived.
    let offset = rows.len();
    let row_count = batch.num_rows();
    let Some(fields) = schema::fields(row_type) else {
        // A single unnamed column.
        let column = batch.column(0);
        let name = batch.schema().field(0).name().clone();
        for r in 0..row_count {
            rows.push(to_value(
                column.as_ref(),
                r,
                row_type,
                &name,
                offset + r,
            )?);
        }
        return Ok(());
    };
    // Columns are in Spark's order; a record's fields are in Morel's
    // order (sorted by label). Map by name.
    let mut columns = Vec::new();
    for (label, _) in &fields {
        match batch.schema().index_of(label) {
            Ok(i) => columns.push(batch.column(i).clone()),
            Err(_) => {
                return Err(SparkError::new(
                    "CONNECTION",
                    format!("Result has no column {}", label),
                ));
            }
        }
    }
    for r in 0..row_count {
        let mut values = Vec::new();
        for (c, (label, t)) in fields.iter().enumerate() {
            values.push(to_value(
                columns[c].as_ref(),
                r,
                t,
                label,
                offset + r,
            )?);
        }
        rows.push(Val::List(Rc::new(values)));
    }
    Ok(())
}

/// Converts the value at `i` of an array to a Morel value of type `t`.
fn to_value(
    array: &dyn Array,
    i: usize,
    t: &Type,
    column: &str,
    row: usize,
) -> Result<Val, SparkError> {
    if let Some(value_type) = option_value_type(t)? {
        if array.is_null(i) {
            return Ok(Val::Unit);
        }
        let v = to_value(array, i, &value_type, column, row)?;
        return Ok(Val::Some(Box::new(v)));
    }
    if array.is_null(i) {
        return Err(SparkError::new(
            "NULL_VALUE",
            format!(
                "Null in column {} of row {}, whose type {} has no room for it",
                column, row, t
            ),
        ));
    }
    let any = array.as_any();
    let cannot = || {
        SparkError::new(
            "UNSUPPORTED_TYPE",
            format!(
                "Cannot decode {} in column {} as {}",
                array.data_type(),
                column,
                t
            ),
        )
    };
    match peel_type(t) {
        Type::Primitive(PrimitiveType::Bool) => {
            let a = any.downcast_ref::<BooleanArray>().ok_or_else(cannot)?;
            Ok(Val::Bool(a.value(i)))
        }
        Type::Primitive(PrimitiveType::Int) => {
            let v = integer(array, i).ok_or_else(cannot)?;
            if v < i32::MIN as i64 || v > i32::MAX as i64 {
                return Err(SparkError::new(
                    "CAST_OVERFLOW",
                    format!(
                        "Value {} in column {} of row {} does not fit in int",
                        v, column, row
                    ),
                ));
            }
            Ok(Val::Int(v as i32))
        }
        Type::Primitive(PrimitiveType::Real) => {
            if let Some(a) = any.downcast_ref::<Float64Array>() {
                return Ok(Val::Real(a.value(i) as f32));
            }
            if let Some(a) = any.downcast_ref::<Float32Array>() {
                return Ok(Val::Real(a.value(i)));
            }
            if let Some(s) = decimal_text(array, i) {
                return Ok(Val::Real(s.parse::<f32>().map_err(read_error)?));
            }
            integer(array, i)
                .map(|v| Val::Real(v as f32))
                .ok_or_else(cannot)
        }
        Type::Primitive(PrimitiveType::String) => text(array, i)
            .map(|s| Val::String(s.into()))
            .ok_or_else(cannot),
        Type::Primitive(PrimitiveType::Char) => {
            let s = text(array, i).ok_or_else(cannot)?;
            Ok(Val::Char(s.chars().next().unwrap_or('\0')))
        }
        Type::Primitive(PrimitiveType::Unit) => Ok(Val::Unit),
        Type::List(element_type) => {
            if let Some(a) = any.downcast_ref::<BinaryArray>() {
                // binary -> word list
                let words =
                    a.value(i).iter().map(|b| Val::Word(*b as u64)).collect();
                return Ok(Val::List(Rc::new(words)));
            }
            let a = any.downcast_ref::<ListArray>().ok_or_else(cannot)?;
            let values = a.value(i);
            let mut list = Vec::new();
            for j in 0..values.len() {
                list.push(to_value(
                    values.as_ref(),
                    j,
                    element_type,
                    column,
                    row,
                )?);
            }
            Ok(Val::List(Rc::new(list)))
        }
        Type::Record(..) | Type::Tuple(..) => {
            let a = any.downcast_ref::<StructArray>().ok_or_else(cannot)?;
            let mut values = Vec::new();
            for (label, field_type) in schema::fields(t).unwrap_or_default() {
                let child = a.column_by_name(&label).ok_or_else(|| {
                    SparkError::new(
                        "CONNECTION",
                        format!("Result has no column {}.{}", column, label),
                    )
                })?;
                values.push(to_value(
                    child.as_ref(),
                    i,
                    &field_type,
                    &format!("{}.{}", column, label),
                    row,
                )?);
            }
            Ok(Val::List(Rc::new(values)))
        }
        _ if schema::is_decimal(t) => {
            // Spark's decimal has the precision its column declares, and
            // Morel's has 34 digits, so a value is rounded to those -- and
            // one too large for them is no more a decimal than an
            // overflowing bigint is an int.
            let s = decimal_text(array, i)
                .or_else(|| integer(array, i).map(|v| v.to_string()))
                .ok_or_else(cannot)?;
            match parse_prefix(&s) {
                Some(Some(d)) => Ok(Val::Decimal(d)),
                _ => Err(SparkError::new(
                    "CAST_OVERFLOW",
                    format!(
                        "Value {} in column {} of row {} is too large for a \
                         Morel decimal",
                        s, column, row
                    ),
                )),
            }
        }
        Type::Data(name, _) if name == "time" => {
            // timestamp: microseconds since epoch -> nanoseconds
            let a = any
                .downcast_ref::<TimestampMicrosecondArray>()
                .ok_or_else(cannot)?;
            Ok(Val::Time(a.value(i).saturating_mul(1000)))
        }
        Type::Data(name, _) if name == "date" => {
            if let Some(a) = any.downcast_ref::<Date32Array>() {
                // date: days since epoch
                let nanos = a.value(i) as i64 * 86_400 * 1_000_000_000;
                return Ok(Val::Date(nanos, 0));
            }
            if let Some(a) = any.downcast_ref::<TimestampMicrosecondArray>() {
                // timestamp_ntz as microseconds since epoch
                return Ok(Val::Date(a.value(i).saturating_mul(1000), 0));
            }
            Err(cannot())
        }
        _ => Err(cannot()),
    }
}

/// Returns an integer of any width, or `None` if the array is not of
/// integers.
fn integer(array: &dyn Array, i: usize) -> Option<i64> {
    let any = array.as_any();
    if let Some(a) = any.downcast_ref::<Int32Array>() {
        return Some(a.value(i) as i64);
    }
    if let Some(a) = any.downcast_ref::<Int64Array>() {
        return Some(a.value(i));
    }
    if let Some(a) = any.downcast_ref::<Int16Array>() {
        return Some(a.value(i) as i64);
    }
    if let Some(a) = any.downcast_ref::<Int8Array>() {
        return Some(a.value(i) as i64);
    }
    None
}

/// Returns a decimal as text, `-123.45`, or `None` if the array is not
/// of decimals.
fn decimal_text(array: &dyn Array, i: usize) -> Option<String> {
    let a = array.as_any().downcast_ref::<Decimal128Array>()?;
    let scale = a.scale();
    let v = a.value(i);
    let digits = v.unsigned_abs().to_string();
    let mut s = String::new();
    if v < 0 {
        s.push('-');
    }
    if scale <= 0 {
        s.push_str(&digits);
        s.push_str(&"0".repeat(-scale as usize));
    } else {
        let scale = scale as usize;
        let digits = format!("{:0>width$}", digits, width = scale + 1);
        let point = digits.len() - scale;
        s.push_str(&digits[..point]);
        s.push('.');
        s.push_str(&digits[point..]);
    }
    Some(s)
}

/// Returns text, or `None` if the array is not of strings.
fn text(array: &dyn Array, i: usize) -> Option<String> {
    let any = array.as_any();
    if let Some(a) = any.downcast_ref::<StringArray>() {
        return Some(a.value(i).to_string());
    }
    if let Some(a) = any.downcast_ref::<LargeStringArray>() {
        return Some(a.value(i).to_string());
    }
    if let Some(a) = any.downcast_ref::<StringViewArray>() {
        return Some(a.value(i).to_string());
    }
    None
}
