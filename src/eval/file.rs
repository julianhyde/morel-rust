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

//! File-system reader for the progressive `file` built-in.
//!
//! Port of morel-java's `Files.java`. Each [`File`] knows its
//! filesystem path and a [`FileType`] (directory, plain file, or a
//! known data format such as CSV). [`File::expand`] mutates the file's
//! [`FileState`] in place: a not-yet-explored entry becomes either a
//! [`FileState::Directory`] (with the listing of its children) or a
//! [`FileState::Data`] (with the header-derived row type and parsers
//! for each CSV column).
//!
//! The mutation is wired through `RefCell` so a child file can be
//! expanded without taking ownership of (or re-borrowing) its parent
//! directory. Children are held as `Rc<File>`, so expanding a child
//! is automatically visible to anyone holding a reference to it,
//! including the parent's `entries` map.

use crate::compile::types::{Label, PrimitiveType, Type};
use crate::eval::decimal;
use crate::eval::session::Session;
use crate::eval::val::Val;
use crate::shell::prop::{Configurable, Prop};
use chrono::NaiveDate;
use flate2::read::GzDecoder;
use std::any::Any;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fs;
use std::io::{BufRead, BufReader, Read};
use std::path::{Path, PathBuf};
use std::rc::{Rc, Weak};
use std::time::SystemTime;

/// A file-system entry: a directory, a parseable data file, or
/// something we haven't yet decided about (an unexpanded entry whose
/// type was determined only from its file-name suffix).
#[derive(Debug)]
pub struct File {
    /// Absolute or relative path to this file on disk.
    pub path: PathBuf,
    /// File name with the [`FileType`] suffix stripped — used as the
    /// field name when this file appears in a parent directory's
    /// progressive record type.
    pub base_name: String,
    /// Suffix-derived category (directory / plain / CSV / CSV.gz).
    pub file_type: FileType,
    /// Mutable state. Starts as [`FileState::Unexpanded`]; transitions
    /// to [`FileState::Directory`] or [`FileState::Data`] on the first
    /// call to [`Self::expand`].
    pub state: RefCell<FileState>,
    /// The rows last read from a data file, with the file's modification
    /// time and length when they were read. A scan of the file reuses
    /// them while the file is unchanged and something else still holds
    /// them: they are held weakly, so that a table that nothing is using
    /// takes no memory, at the cost of reading it again.
    rows: RefCell<Option<CachedRows>>,
}

/// The rows of a data file, as [`File::rows`] holds them.
#[derive(Debug)]
struct CachedRows {
    modified: Option<SystemTime>,
    len: u64,
    rows: Weak<Vec<Val>>,
}

/// Discovered structure of a [`File`].
#[derive(Debug)]
pub enum FileState {
    /// Not yet expanded. [`File::expand`] decides what it is.
    Unexpanded,
    /// A directory whose listing has been read into `entries`. Each
    /// child starts [`FileState::Unexpanded`] and is expanded
    /// on-demand as its field is accessed.
    Directory { entries: BTreeMap<Label, Rc<File>> },
    /// A data file (CSV / CSV.gz) whose header has been parsed.
    /// `row_type` is the record type of one row; `field_parsers` says
    /// how to convert each header column into a value of that field's
    /// type, given as `(csv_column_index, parser)` pairs in
    /// `row_type` field order.
    Data {
        row_type: Rc<Type>,
        field_parsers: Vec<(usize, Column)>,
    },
}

/// File category derived from the suffix of the file name.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum FileType {
    /// A directory; expands into a record of its entries.
    Directory,
    /// A plain file with an unrecognised suffix — never expands.
    Plain,
    /// `*.csv` — UTF-8, comma-separated, first row is header.
    Csv,
    /// `*.csv.gz` — gzipped CSV.
    CsvGz,
}

impl FileType {
    /// Returns true when files of this type represent a list of
    /// records (i.e. the progressive record's field type should be
    /// `_ list`, not a bare record).
    pub fn is_list(self) -> bool {
        matches!(self, FileType::Csv | FileType::CsvGz)
    }

    /// Returns the suffix this file type's path ends with, including
    /// the leading `.`, or `""` for directory / plain.
    pub fn suffix(self) -> &'static str {
        match self {
            FileType::Directory | FileType::Plain => "",
            FileType::Csv => ".csv",
            FileType::CsvGz => ".csv.gz",
        }
    }

    /// Suffix-matching order — longest first, so that `*.csv.gz` is
    /// recognised as `CsvGz` rather than `Csv`.
    const INSTANCES: &'static [FileType] = &[FileType::CsvGz, FileType::Csv];

    /// Derives the file type from a path: `Directory` if the path is
    /// a directory, `Csv`/`CsvGz` if the name matches a known suffix,
    /// or `Plain` otherwise.
    pub fn of(path: &Path) -> FileType {
        if path.is_dir() {
            return FileType::Directory;
        }
        let name = path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or_default();
        for &ft in FileType::INSTANCES {
            if name.ends_with(ft.suffix()) {
                return ft;
            }
        }
        FileType::Plain
    }
}

/// The type of a column of a CSV file, as its header declares it.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum ColumnKind {
    Bool,
    Date,
    Decimal,
    Int,
    Real,
    String,
}

/// A column of a CSV file: its name, its type, and whether it is an
/// `option`. It is morel-java's `Files.Column`.
///
/// The header of a file declares each column as `name:type`, where
/// type is `bool`, `int`, `real` (or its synonym `double`), `decimal`,
/// `date` or `string`, optionally followed by `option`; a missing or
/// unknown type is `string`. In an option column, an empty field or
/// `NULL` is `NONE`; in any other column, it raises `Fail` when the
/// file is read, because the column's type has no room for it, except
/// that in a `string` column an empty field is the empty string. A
/// field that is not a value of its column's type (a `bool` other than
/// `true` or `false`, a malformed number or date) raises `Fail`. A
/// field may be quoted, whatever its type.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Column {
    pub name: String,
    pub kind: ColumnKind,
    pub optional: bool,
}

impl Column {
    /// Creates a column from its name and type, as the header gives them.
    fn of(name: &str, type_: &str) -> Column {
        let words: Vec<&str> = type_.split_whitespace().collect();
        let optional = words.len() == 2 && words[1] == "option";
        let kind = match words.first().copied().unwrap_or("") {
            "bool" => ColumnKind::Bool,
            "date" => ColumnKind::Date,
            "decimal" => ColumnKind::Decimal,
            "double" | "real" => ColumnKind::Real,
            "int" => ColumnKind::Int,
            _ => ColumnKind::String,
        };
        Column {
            name: name.to_string(),
            kind,
            optional,
        }
    }

    /// The name of the column's type, without `option`.
    fn kind_name(&self) -> &'static str {
        match self.kind {
            ColumnKind::Bool => "bool",
            ColumnKind::Date => "date",
            ColumnKind::Decimal => "decimal",
            ColumnKind::Int => "int",
            ColumnKind::Real => "real",
            ColumnKind::String => "string",
        }
    }

    /// The type of the column's values.
    fn type_(&self) -> Type {
        let t = match self.kind {
            ColumnKind::Bool => Type::Primitive(PrimitiveType::Bool),
            ColumnKind::Date => Type::Data("date".to_string(), vec![]),
            ColumnKind::Decimal => Type::Data("decimal".to_string(), vec![]),
            ColumnKind::Int => Type::Primitive(PrimitiveType::Int),
            ColumnKind::Real => Type::Primitive(PrimitiveType::Real),
            ColumnKind::String => Type::Primitive(PrimitiveType::String),
        };
        if self.optional {
            Type::Data("option".to_string(), vec![Rc::new(t)])
        } else {
            t
        }
    }

    /// Converts a field to a value of the column's type, or returns the
    /// message of the `Fail` it raises.
    pub fn parse(&self, field: &str) -> Result<Val, String> {
        let is_null = field.is_empty() || field == "NULL";
        if self.optional {
            if is_null {
                return Ok(Val::Unit);
            }
            return self.parse_value(field).map(|v| Val::Some(Box::new(v)));
        }
        if field == "NULL" || is_null && self.kind != ColumnKind::String {
            return Err(format!(
                "null in column {}, whose type {} has no room for it",
                self.name,
                self.kind_name()
            ));
        }
        self.parse_value(field)
    }

    /// Converts a field that is not null.
    fn parse_value(&self, field: &str) -> Result<Val, String> {
        let s = unquote(field);
        let invalid = || {
            format!(
                "value {} in column {} is not a valid {}",
                field,
                self.name,
                self.kind_name()
            )
        };
        match self.kind {
            ColumnKind::Bool => match s {
                "true" => Ok(Val::Bool(true)),
                "false" => Ok(Val::Bool(false)),
                _ => Err(invalid()),
            },
            ColumnKind::Date => {
                let date = NaiveDate::parse_from_str(s, "%Y-%m-%d")
                    .map_err(|_| invalid())?;
                let midnight = date
                    .and_hms_opt(0, 0, 0)
                    .ok_or_else(invalid)?
                    .and_utc()
                    .timestamp_nanos_opt()
                    .ok_or_else(invalid)?;
                Ok(Val::Date(midnight, 0))
            }
            ColumnKind::Decimal => decimal::parse_exact(s)
                .map(Val::Decimal)
                .ok_or_else(invalid),
            ColumnKind::Int => s.parse().map(Val::Int).map_err(|_| invalid()),
            ColumnKind::Real => s.parse().map(Val::Real).map_err(|_| invalid()),
            ColumnKind::String => Ok(Val::String(s.into())),
        }
    }
}

/// Splits a line of a CSV file into its fields.
///
/// Fields are separated by commas. A field that starts with a single
/// quote runs to the next single quote that is not doubled, and may
/// contain commas; a doubled quote inside it stands for one quote. The
/// quotes stay in the field, so that a quoted empty string, `''`, can be
/// told from an empty field; [`unquote`] removes them. A trailing empty
/// field is a field, so that "1," has two. It is morel-java's
/// `Files.LineParser`.
fn split_line(line: &str) -> Vec<String> {
    let chars: Vec<char> = line.chars().collect();
    let n = chars.len();
    let mut fields = Vec::new();
    let mut i = 0;
    loop {
        let mut field = String::new();
        if i < n && chars[i] == '\'' {
            // A quoted field. Find the closing quote, skipping doubled
            // quotes, which stand for one.
            field.push('\'');
            i += 1;
            while i < n {
                let c = chars[i];
                i += 1;
                if c == '\'' {
                    field.push('\'');
                    if i < n && chars[i] == '\'' {
                        i += 1;
                        continue;
                    }
                    break;
                }
                field.push(c);
            }
        }
        // Anything up to the comma is part of the field.
        while i < n && chars[i] != ',' {
            field.push(chars[i]);
            i += 1;
        }
        fields.push(field);
        if i >= n {
            return fields;
        }
        i += 1; // skip the comma
    }
}

/// A value that knows its own (potentially progressive) type. Used
/// by the type-resolver to widen progressive record types on
/// demand. The Rust analog of morel-java's `TypedValue`.
pub trait TypedValue {
    /// Current type of this value. May widen over the lifetime of the
    /// value as `discover_field` succeeds.
    fn type_(&self) -> Rc<Type>;

    /// Tries to widen the type to include `field_name`. Returns
    /// `true` if the type widened (so the caller should re-resolve
    /// the field access), `false` if the field is unknown.
    fn discover_field(&self, field_name: &str) -> bool {
        let _ = field_name;
        false
    }

    /// Cast to `Any` so resolver hooks that only know they have a
    /// `Rc<dyn TypedValue>` can downcast to specific implementors
    /// (currently only [`File`]) to extract child values.
    fn as_any(&self) -> &dyn Any;
}

impl TypedValue for File {
    fn type_(&self) -> Rc<Type> {
        match &*self.state.borrow() {
            FileState::Unexpanded => {
                // We know the file's `FileType` (from its suffix)
                // even before we've parsed its contents: a CSV /
                // CSV.gz is a `_ list` (with `_` itself progressive
                // and empty until the header is parsed); anything
                // else acts as a progressive empty record.
                if self.file_type.is_list() {
                    Rc::new(Type::List(Rc::new(Type::Record(
                        true,
                        BTreeMap::new(),
                    ))))
                } else {
                    Rc::new(Type::Record(true, BTreeMap::new()))
                }
            }
            FileState::Directory { entries } => {
                let mut fields: BTreeMap<Label, Rc<Type>> = BTreeMap::new();
                for (label, child) in entries {
                    fields.insert(label.clone(), child.type_());
                }
                Rc::new(Type::Record(true, fields))
            }
            FileState::Data { row_type, .. } => {
                Rc::new(Type::List(Rc::clone(row_type)))
            }
        }
    }

    fn discover_field(&self, field_name: &str) -> bool {
        // Make sure top-level is expanded so we know our children.
        self.expand();
        // Look up the child by name and expand it. If we're not a
        // directory (or the child doesn't exist), no widening.
        let child = match &*self.state.borrow() {
            FileState::Directory { entries } => {
                entries.get(&Label::from(field_name)).cloned()
            }
            _ => None,
        };
        match child {
            Some(c) => {
                let before = matches!(*c.state.borrow(), FileState::Unexpanded);
                c.expand();
                before
            }
            None => false,
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl File {
    /// Constructs an [`Rc<File>`] for the given path. The file's
    /// [`FileType`] is determined from `path`; the state starts
    /// [`FileState::Unexpanded`]. Callers typically follow up with
    /// [`Self::expand`] (or with the type-resolver's progressive
    /// discovery path).
    pub fn create(path: &Path) -> Rc<File> {
        let file_type = FileType::of(path);
        let base_name = base_name(path, file_type);
        Rc::new(File {
            path: path.to_path_buf(),
            base_name,
            file_type,
            state: RefCell::new(FileState::Unexpanded),
            rows: RefCell::new(None),
        })
    }

    /// If the file is still [`FileState::Unexpanded`], decides what it
    /// is and stores the result. A no-op if already expanded.
    pub fn expand(&self) {
        // Avoid double-expansion. Borrow immutably first so we can
        // short-circuit without taking a mutable borrow that might
        // conflict with re-entrant access.
        if !matches!(*self.state.borrow(), FileState::Unexpanded) {
            return;
        }
        let new_state = match self.file_type {
            FileType::Directory => expand_directory(&self.path),
            FileType::Plain => return,
            FileType::Csv | FileType::CsvGz => {
                match expand_data(&self.path, self.file_type) {
                    Some(s) => s,
                    None => return,
                }
            }
        };
        *self.state.borrow_mut() = new_state;
    }

    /// Reads the file's rows as `Vec<Vec<ParsedField>>`, one inner
    /// vector per row, in field-declaration order. Returns `None` if
    /// the file is not a data file or cannot be opened. Only valid
    /// after [`Self::expand`] has been called.
    pub fn read_rows(&self) -> Option<Result<Vec<Vec<Val>>, String>> {
        let parsers: Vec<(usize, Column)> = match &*self.state.borrow() {
            FileState::Data { field_parsers, .. } => field_parsers.clone(),
            _ => return None,
        };
        let reader = open_reader(&self.path, self.file_type)?;
        let mut rows = Vec::new();
        let mut lines = reader.lines();
        // Skip the header line.
        let Some(header) = lines.next() else {
            return Some(Ok(rows));
        };
        let column_count = header.ok()?.split(',').count();
        for line in lines {
            let line = line.ok()?;
            let cells = split_line(&line);
            if cells.len() < column_count {
                return Some(Err(format!(
                    "line has {} fields, but the header has {}: {}",
                    cells.len(),
                    column_count,
                    line
                )));
            }
            // Reorder cells from CSV-column order into row_type field
            // order: parsers[j] = (i, c) means field j's value comes
            // from CSV column `i`, parsed as column `c`.
            let mut values = Vec::with_capacity(parsers.len());
            for (i, column) in &parsers {
                match column.parse(&cells[*i]) {
                    Ok(v) => values.push(v),
                    Err(message) => return Some(Err(message)),
                }
            }
            rows.push(values);
        }
        Some(Ok(rows))
    }
}

/// Returns the [`File`] for this session — the directory configured by
/// the `directory` property, or `"."` if unset. Each call produces a
/// fresh unexpanded file; callers that need expansion to persist
/// across multiple `file` references must hold onto the `Rc` they
/// receive. (Caching the value per session is Stage 3b's job.)
pub fn session_file(session: &Session) -> Rc<File> {
    use crate::shell::prop::PropVal;
    let val = session.config.get(Prop::Directory);
    let path = match val {
        PropVal::PathBuf(p) => (*p).clone(),
        PropVal::String(s) => PathBuf::from(s.as_str()),
        _ => PathBuf::new(),
    };
    let path = if path.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        path
    };
    File::create(&path)
}

/// Converts a [`File`] to its Morel runtime value: a directory becomes
/// a `Val::File`, a data file becomes `Val::List` of record values
/// (one per CSV row), and an unexpanded / plain file becomes
/// `Val::Unit`. Used when projecting a directory entry through field
/// access.
///
/// Returns the message of the `Fail` that reading a data file raises, if
/// a field is not a value of its column's type.
pub fn file_as_val(file: &Rc<File>) -> Result<Val, String> {
    file.expand();
    match &*file.state.borrow() {
        FileState::Directory { .. } | FileState::Unexpanded => {
            Ok(Val::File(Rc::clone(file)))
        }
        FileState::Data { .. } => {
            // Reuse the rows last read, if the file has not changed since,
            // and they are still held.
            let metadata = fs::metadata(&file.path).ok();
            let modified = metadata.as_ref().and_then(|m| m.modified().ok());
            let len = metadata.as_ref().map_or(0, fs::Metadata::len);
            if let Some(cached) = &*file.rows.borrow()
                && cached.modified == modified
                && cached.len == len
                && let Some(rows) = cached.rows.upgrade()
            {
                return Ok(Val::List(rows));
            }
            let rows = file.read_rows().unwrap_or(Ok(Vec::new()))?;
            let rows: Rc<Vec<Val>> = Rc::new(
                rows.into_iter()
                    .map(|row| Val::List(Rc::new(row)))
                    .collect(),
            );
            *file.rows.borrow_mut() = Some(CachedRows {
                modified,
                len,
                rows: Rc::downgrade(&rows),
            });
            Ok(Val::List(rows))
        }
    }
}

/// Formats a [`File`] for the runtime printer. Directories show
/// as `{name1=...,name2=...}` (mirroring morel-java); data files
/// show as `<relation>`; unexpanded files show as `{}` (a stub).
pub fn display_file(file: &File) -> String {
    match &*file.state.borrow() {
        FileState::Unexpanded => "{}".to_string(),
        FileState::Directory { entries } => {
            let mut s = String::from("{");
            let mut first = true;
            for (label, child) in entries {
                if !first {
                    s.push(',');
                }
                first = false;
                s.push_str(&format!("{}=", label));
                s.push_str(&display_file(child));
            }
            s.push('}');
            s
        }
        FileState::Data { .. } => "<relation>".to_string(),
    }
}

/// Strips a trailing suffix from a path's file name. For directories
/// (suffix `""`) or unknown plain files, the whole file name is the
/// base name.
fn base_name(path: &Path, file_type: FileType) -> String {
    let name = path
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or_default();
    let suffix = file_type.suffix();
    if !suffix.is_empty() && name.ends_with(suffix) {
        name[..name.len() - suffix.len()].to_string()
    } else {
        name.to_string()
    }
}

/// Reads the directory listing at `dir` and returns a
/// [`FileState::Directory`] whose `entries` map is keyed on the
/// children's base names. Each child starts unexpanded.
fn expand_directory(dir: &Path) -> FileState {
    let mut entries: BTreeMap<Label, Rc<File>> = BTreeMap::new();
    if let Ok(read_dir) = fs::read_dir(dir) {
        for entry in read_dir.flatten() {
            let child = File::create(&entry.path());
            // Skip plain files (no recognised suffix) — they would
            // never have a useful expansion and just pollute the
            // type's field list.
            if matches!(child.file_type, FileType::Plain) {
                continue;
            }
            let label = Label::from(child.base_name.clone());
            entries.insert(label, child);
        }
    }
    FileState::Directory { entries }
}

/// Reads the header of a CSV / CSV.gz file and returns a
/// [`FileState::Data`] describing the row type. Returns `None` if the
/// file cannot be opened (caller leaves the state `Unexpanded`).
fn expand_data(path: &Path, file_type: FileType) -> Option<FileState> {
    let reader = open_reader(path, file_type)?;
    let mut lines = reader.lines();
    let header = lines.next()?.ok()?;
    if header.is_empty() {
        // Empty header — treat as `unit` row type.
        return Some(FileState::Data {
            row_type: Rc::new(Type::Primitive(PrimitiveType::Unit)),
            field_parsers: vec![],
        });
    }
    // Parse each "name[:type]" header column; default type is string.
    let mut declared: Vec<Column> = Vec::new();
    for field in header.split(',') {
        let mut split = field.splitn(2, ':');
        let name = split.next().unwrap_or("");
        let ty = split.next().unwrap_or("string");
        declared.push(Column::of(name, ty));
    }
    // Row type: BTreeMap, so fields end up in label order. We
    // remember each field's *CSV column index* so `read_rows` can
    // reorder the cells at parse time.
    let mut field_types: BTreeMap<Label, Rc<Type>> = BTreeMap::new();
    let mut name_to_csv_index: BTreeMap<String, usize> = BTreeMap::new();
    for (i, column) in declared.iter().enumerate() {
        field_types
            .insert(Label::from(column.name.clone()), Rc::new(column.type_()));
        name_to_csv_index.insert(column.name.clone(), i);
    }
    let mut field_parsers: Vec<(usize, Column)> = Vec::new();
    for label in field_types.keys() {
        let name = match label {
            Label::String(s) => s.to_string(),
            Label::Ordinal(n) => n.to_string(),
        };
        let csv_index = name_to_csv_index[&name];
        field_parsers.push((csv_index, declared[csv_index].clone()));
    }
    let row_type = Type::Record(false, field_types);
    Some(FileState::Data {
        row_type: Rc::new(row_type),
        field_parsers,
    })
}

/// Strips a single pair of leading/trailing `'` quotes, if present.
/// `"abc"` and `"'abc, def'"` both round-trip (the latter strips the
/// quotes to `abc, def`).
fn unquote(s: &str) -> &str {
    if s.starts_with('\'') && s.ends_with('\'') && s.len() >= 2 {
        &s[1..s.len() - 1]
    } else {
        s
    }
}

/// Opens `path` for line-by-line reading, transparently decompressing
/// `.csv.gz` files. Returns `None` if the file cannot be opened.
fn open_reader(
    path: &Path,
    file_type: FileType,
) -> Option<BufReader<Box<dyn Read>>> {
    let file = fs::File::open(path).ok()?;
    let inner: Box<dyn Read> = match file_type {
        FileType::CsvGz => Box::new(GzDecoder::new(file)),
        _ => Box::new(file),
    };
    Some(BufReader::new(inner))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn data_dir() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/data")
    }

    #[test]
    fn read_csv_header_deduces_types() {
        let path = data_dir().join("scott/depts.csv");
        let file = File::create(&path);
        file.expand();
        match &*file.state.borrow() {
            FileState::Data { row_type, .. } => match row_type.as_ref() {
                Type::Record(false, fields) => {
                    let names: Vec<&str> = fields
                        .keys()
                        .filter_map(|l| match l {
                            Label::String(s) => Some(s.as_str()),
                            _ => None,
                        })
                        .collect();
                    assert_eq!(names, vec!["deptno", "dname", "loc"]);
                }
                other => panic!("unexpected row type: {:?}", other),
            },
            _ => panic!("expected Data state"),
        }
    }

    #[test]
    fn split_line_honors_quotes() {
        assert_eq!(split_line("1,2"), vec!["1", "2"]);
        assert_eq!(split_line("1,"), vec!["1", ""]);
        assert_eq!(split_line("'a, b',c"), vec!["'a, b'", "c"]);
        assert_eq!(split_line("'it''s',x"), vec!["'it's'", "x"]);
        assert_eq!(split_line("'',x"), vec!["''", "x"]);
    }

    #[test]
    fn column_parses_by_type() {
        let int = Column::of("i", "int");
        assert_eq!(int.parse("7"), Ok(Val::Int(7)));
        assert_eq!(int.parse("'7'"), Ok(Val::Int(7)));
        assert!(int.parse("NULL").is_err());
        assert!(int.parse("").is_err());
        assert!(int.parse("x").is_err());
        let opt = Column::of("i", "int option");
        assert_eq!(opt.parse("NULL"), Ok(Val::Unit));
        assert_eq!(opt.parse(""), Ok(Val::Unit));
        assert_eq!(opt.parse("7"), Ok(Val::Some(Box::new(Val::Int(7)))));
        let string = Column::of("s", "string");
        assert_eq!(string.parse(""), Ok(Val::String("".into())));
        assert!(string.parse("NULL").is_err());
        let boolean = Column::of("b", "bool");
        assert_eq!(boolean.parse("true"), Ok(Val::Bool(true)));
        assert!(boolean.parse("t").is_err());
        let date = Column::of("d", "date");
        assert_eq!(
            date.parse("1970-01-02"),
            Ok(Val::Date(86_400_000_000_000, 0))
        );
        assert!(date.parse("1970-13-01").is_err());
    }

    #[test]
    fn read_csv_gz_decompresses() {
        let path = data_dir().join("scott/emps.csv.gz");
        let file = File::create(&path);
        file.expand();
        assert!(matches!(*file.state.borrow(), FileState::Data { .. }));
        let rows = file.read_rows().unwrap().unwrap();
        assert!(!rows.is_empty());
    }

    #[test]
    fn directory_lists_csv_children() {
        let path = data_dir().join("scott");
        let dir = File::create(&path);
        dir.expand();
        match &*dir.state.borrow() {
            FileState::Directory { entries } => {
                let names: Vec<String> =
                    entries.keys().map(|l| format!("{}", l)).collect();
                assert!(names.contains(&"depts".to_string()));
                assert!(names.contains(&"emps".to_string()));
            }
            _ => panic!("expected Directory state"),
        }
    }
}

// End file.rs
