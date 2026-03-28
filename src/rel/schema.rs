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

//! Schema: catalog of tables available for query planning.
//!
//! The [`Schema`] trait is the equivalent of Calcite's `RelOptSchema`.
//! [`TableEntry`] is the equivalent of `RelOptTable`.
//! [`MapSchema`] is a simple in-memory implementation backed by a `HashMap`.
//! [`scott_schema`] returns the classic Scott EMP/DEPT schema used in tests.

use crate::compile::types::{Label, PrimitiveType, Type};
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

// -----------------------------------------------------------------------
// TableEntry
// -----------------------------------------------------------------------

/// A table available for planning: its qualified name and row type.
///
/// The row type is an ordered list of `(column_name, column_type)` pairs.
/// Column ordinals are the indices into this list, consistent with the
/// field-reference convention used by [`crate::rel::Rel`] expressions.
#[derive(Clone, PartialEq, Debug)]
pub struct TableEntry {
    /// Qualified name, e.g. `["scott", "EMP"]`.
    pub name: Vec<String>,
    /// Ordered columns: `(name, type)`.
    pub columns: Vec<(String, Type)>,
}

impl TableEntry {
    /// Creates a new table entry.
    pub fn new(
        name: impl IntoIterator<Item = impl Into<String>>,
        columns: impl IntoIterator<Item = (impl Into<String>, Type)>,
    ) -> Self {
        TableEntry {
            name: name.into_iter().map(Into::into).collect(),
            columns: columns.into_iter().map(|(n, t)| (n.into(), t)).collect(),
        }
    }

    /// Returns the number of columns.
    pub fn column_count(&self) -> usize {
        self.columns.len()
    }

    /// Looks up a column by name, returning its ordinal and type.
    pub fn column(&self, name: &str) -> Option<(usize, &Type)> {
        self.columns
            .iter()
            .enumerate()
            .find(|(_, (n, _))| n == name)
            .map(|(i, (_, t))| (i, t))
    }

    /// Returns the column at the given ordinal.
    pub fn column_at(&self, index: usize) -> Option<&(String, Type)> {
        self.columns.get(index)
    }

    /// Converts the row type to [`Type::Record`] for use by the Morel compiler.
    pub fn row_type(&self) -> Type {
        let fields = self
            .columns
            .iter()
            .map(|(name, ty)| (Label::String(name.clone()), ty.clone()))
            .collect::<BTreeMap<_, _>>();
        Type::Record(false, fields)
    }
}

// -----------------------------------------------------------------------
// Schema trait
// -----------------------------------------------------------------------

/// A catalog of tables available for query planning.
///
/// Equivalent to Calcite's `RelOptSchema`. The `table` method accepts a
/// slice of name parts so that both unqualified (`&["EMP"]`) and
/// schema-qualified (`&["scott", "EMP"]`) lookups are supported by the
/// same implementation.
pub trait Schema: Send + Sync {
    /// Returns the table with the given (possibly qualified) name, or
    /// `None` if not found.
    fn table(&self, name: &[&str]) -> Option<Arc<TableEntry>>;
}

// -----------------------------------------------------------------------
// MapSchema
// -----------------------------------------------------------------------

/// An in-memory [`Schema`] backed by a `HashMap`.
pub struct MapSchema {
    tables: HashMap<Vec<String>, Arc<TableEntry>>,
}

impl MapSchema {
    /// Creates an empty schema.
    pub fn empty() -> Self {
        MapSchema {
            tables: HashMap::new(),
        }
    }

    /// Creates a schema pre-populated with the given tables.
    pub fn new(tables: impl IntoIterator<Item = TableEntry>) -> Self {
        let map = tables
            .into_iter()
            .map(|e| (e.name.clone(), Arc::new(e)))
            .collect();
        MapSchema { tables: map }
    }
}

impl Schema for MapSchema {
    fn table(&self, name: &[&str]) -> Option<Arc<TableEntry>> {
        let key: Vec<String> = name.iter().map(ToString::to_string).collect();
        // Try exact match first.
        if let Some(t) = self.tables.get(&key) {
            return Some(t.clone());
        }
        // Fall back to case-insensitive match.
        let key_lower: Vec<String> =
            key.iter().map(|s| s.to_lowercase()).collect();
        self.tables
            .iter()
            .find(|(k, _)| {
                k.iter().map(|s| s.to_lowercase()).collect::<Vec<_>>()
                    == key_lower
            })
            .map(|(_, v)| v.clone())
    }
}

// -----------------------------------------------------------------------
// Scott schema
// -----------------------------------------------------------------------

/// Returns a [`MapSchema`] containing the classic Scott EMP/DEPT schema
/// used in tests, mirroring the schema in Apache Calcite's `RelBuilderTest`.
///
/// Tables: `["scott", "EMP"]`, `["scott", "DEPT"]`,
///         `["scott", "SALGRADE"]`, `["scott", "BONUS"]`.
///
/// Column types are mapped to the nearest Morel primitive:
/// `INTEGER` → `int`, `VARCHAR` / `DATE` → `string`, `DECIMAL` → `real`.
pub fn scott_schema() -> MapSchema {
    let int = || Type::Primitive(PrimitiveType::Int);
    let str_ = || Type::Primitive(PrimitiveType::String);
    let real = || Type::Primitive(PrimitiveType::Real);

    MapSchema::new([
        TableEntry::new(
            ["scott", "EMP"],
            [
                ("EMPNO", int()),
                ("ENAME", str_()),
                ("JOB", str_()),
                ("MGR", int()),
                ("HIREDATE", str_()),
                ("SAL", real()),
                ("COMM", real()),
                ("DEPTNO", int()),
            ],
        ),
        TableEntry::new(
            ["scott", "DEPT"],
            [("DEPTNO", int()), ("DNAME", str_()), ("LOC", str_())],
        ),
        TableEntry::new(
            ["scott", "SALGRADE"],
            [("GRADE", int()), ("LOSAL", int()), ("HISAL", int())],
        ),
        TableEntry::new(
            ["scott", "BONUS"],
            [
                ("ENAME", str_()),
                ("JOB", str_()),
                ("SAL", real()),
                ("COMM", real()),
            ],
        ),
    ])
}

// -----------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn schema() -> MapSchema {
        scott_schema()
    }

    #[test]
    fn test_table_found_qualified() {
        let s = schema();
        let t = s.table(&["scott", "EMP"]).expect("EMP not found");
        assert_eq!(t.name, vec!["scott", "EMP"]);
        assert_eq!(t.column_count(), 8);
    }

    #[test]
    fn test_table_found_dept() {
        let s = schema();
        let t = s.table(&["scott", "DEPT"]).expect("DEPT not found");
        assert_eq!(t.column_count(), 3);
    }

    #[test]
    fn test_table_not_found() {
        let s = schema();
        assert!(s.table(&["scott", "FOO"]).is_none());
    }

    #[test]
    fn test_table_wrong_schema() {
        let s = schema();
        assert!(s.table(&["public", "EMP"]).is_none());
    }

    #[test]
    fn test_table_unqualified_not_found() {
        // MapSchema requires the full qualified name; bare "EMP" is not found.
        let s = schema();
        assert!(s.table(&["EMP"]).is_none());
    }

    #[test]
    fn test_column_lookup() {
        let s = schema();
        let t = s.table(&["scott", "EMP"]).expect("EMP not found");
        let (ordinal, _) = t.column("SAL").expect("SAL not found");
        assert_eq!(ordinal, 5);
    }

    #[test]
    fn test_column_not_found() {
        let s = schema();
        let t = s.table(&["scott", "EMP"]).unwrap();
        assert!(t.column("NOSUCHCOL").is_none());
    }

    #[test]
    fn test_column_at() {
        let s = schema();
        let t = s.table(&["scott", "EMP"]).unwrap();
        let (name, _) = t.column_at(0).expect("column 0 not found");
        assert_eq!(name, "EMPNO");
    }

    #[test]
    fn test_row_type_is_record() {
        let s = schema();
        let t = s.table(&["scott", "DEPT"]).unwrap();
        let row_type = t.row_type();
        match row_type {
            Type::Record(false, fields) => {
                assert_eq!(fields.len(), 3);
                assert!(fields.contains_key(&Label::String("DEPTNO".into())));
            }
            _ => panic!("expected Type::Record"),
        }
    }

    #[test]
    fn test_case_insensitive_table_name() {
        let s = schema();
        // Lookup is case-insensitive; canonical name is returned.
        let t = s.table(&["SCOTT", "emp"]).expect("should find EMP");
        assert_eq!(t.name, vec!["scott", "EMP"]);
    }
}
