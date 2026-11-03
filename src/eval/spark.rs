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

//! Connections to Apache Spark, and their catalogs.
//!
//! Port of morel-java's `MockSparkConnection`, `SparkCatalog` and
//! `SparkConnections`. This port has no Spark adapter, so the only
//! connection it can open is the offline one, whose URI is `mock:` and
//! whose catalog is the session's data sets. Opening any other URI,
//! and preparing a plan, raise `Spark` with error class `CONNECTION`,
//! as morel-java does where its adapter is absent.
//!
//! A catalog is a progressive record whose fields are databases, whose
//! fields in turn are tables, each a bag of records. Nothing is fetched
//! until it is needed: the databases when the root's type is first
//! asked for, a database's tables when the database is first
//! discovered, a table's type when the table is first discovered, and
//! its rows when its value is first read. Each fetch happens once.

use crate::compile::library::{BuiltInExn, BuiltInFunction};
use crate::compile::span::Span;
use crate::compile::types::{Label, Type};
use crate::eval::typed_value::{Child, TypedValue};
use crate::eval::val::Val;
use crate::shell::kernel::MorelError;
use std::cell::{Cell, Ref, RefCell};
use std::collections::BTreeMap;
use std::env;
use std::fmt;
use std::rc::Rc;

/// The URI that opens the offline connection.
pub const MOCK_URI: &str = "mock:";

/// Environment variable that names the default server.
pub const SPARK_REMOTE: &str = "SPARK_REMOTE";

/// Message of the `CONNECTION` error that every operation needing the
/// Spark adapter raises, since this port has none.
pub const ADAPTER_UNAVAILABLE: &str = "The Spark adapter is not available; \
     it needs JDK 17 or later and the 'spark' Maven profile";

/// A failure that the Morel exception `Spark` reports: Spark's error
/// class, such as `TABLE_OR_VIEW_NOT_FOUND`, or one of the adapter's
/// own, such as `CONNECTION` or `CLOSED`, and a message.
#[derive(Clone, Debug)]
pub struct SparkError {
    pub error_class: &'static str,
    pub message: String,
}

impl SparkError {
    fn new(error_class: &'static str, message: String) -> Self {
        SparkError {
            error_class,
            message,
        }
    }

    /// Converts this error into the Morel exception
    /// `Spark {errorClass, message}`, raised at `span`.
    pub fn raise(&self, span: &Span) -> MorelError {
        MorelError::Runtime2(
            BuiltInExn::Spark,
            Some(format!("{}: {}", self.error_class, self.message)),
            span.clone(),
        )
    }

    /// Converts this error into the Morel exception, raised at no
    /// position. A catalog is browsed during type resolution as well as
    /// during evaluation, and has no position of its own to blame.
    fn raise_anywhere(&self) -> MorelError {
        self.raise(&Span::new("0.0-0.0"))
    }
}

/// Returns the error raised by an operation that needs the Spark
/// adapter.
pub fn adapter_unavailable() -> SparkError {
    SparkError::new("CONNECTION", ADAPTER_UNAVAILABLE.to_string())
}

/// A data set of the session: a record of relations, by name. The
/// offline connection's catalog is made of these.
#[derive(Clone, Debug)]
pub struct DataSet {
    pub name: String,
    pub type_: Rc<Type>,
    pub value: Val,
}

/// A connection. This port can open only the offline one, whose
/// catalog is the session's data sets and which can execute nothing.
pub struct Connection {
    data_sets: BTreeMap<String, DataSet>,
    closed: Cell<bool>,
    /// The connection's catalog, created on first use, so that what is
    /// discovered accumulates; forgotten when the connection closes.
    catalog: RefCell<Option<Rc<Catalog>>>,
}

impl fmt::Debug for Connection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Connection({})", MOCK_URI)
    }
}

impl fmt::Display for Connection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<connection {}>", MOCK_URI)
    }
}

impl Connection {
    /// Opens a connection to `uri`, which must be the offline one.
    pub fn open(
        uri: &str,
        data_sets: Vec<DataSet>,
    ) -> Result<Rc<Connection>, SparkError> {
        if uri != MOCK_URI {
            return Err(adapter_unavailable());
        }
        Ok(Rc::new(Connection {
            data_sets: data_sets
                .into_iter()
                .map(|d| (d.name.clone(), d))
                .collect(),
            closed: Cell::new(false),
            catalog: RefCell::new(None),
        }))
    }

    /// Returns the URI of the default server, from `SPARK_REMOTE`.
    pub fn default_uri() -> Result<String, SparkError> {
        match env::var(SPARK_REMOTE) {
            Ok(uri) if !uri.is_empty() => Ok(uri),
            _ => Err(SparkError::new(
                "CONNECTION",
                format!(
                    "No default Spark Connect server: {} is not set",
                    SPARK_REMOTE
                ),
            )),
        }
    }

    /// Returns the type of a connection, `Spark.connection`.
    pub fn type_() -> Rc<Type> {
        // The parameter type of `Spark.close`, so that it is the type
        // the type parser makes of the name.
        match BuiltInFunction::SparkClose.get_type().as_ref() {
            Type::Fn(param, _) => Rc::clone(param),
            t => panic!("unexpected type of Spark.close: {:?}", t),
        }
    }

    /// Returns the catalog of this connection, creating it on first use.
    pub fn catalog(self: &Rc<Self>) -> Rc<Catalog> {
        let mut slot = self.catalog.borrow_mut();
        Rc::clone(slot.get_or_insert_with(|| {
            Rc::new(Catalog {
                connection: Rc::clone(self),
                databases: RefCell::new(None),
            })
        }))
    }

    /// Closes this connection and forgets its catalog. Any later use of
    /// it raises `Spark`.
    pub fn close(&self) {
        self.catalog.borrow_mut().take();
        self.closed.set(true);
    }

    fn check_open(&self) -> Result<(), SparkError> {
        if self.closed.get() {
            return Err(SparkError::new(
                "CLOSED",
                format!("Connection to {} is closed", MOCK_URI),
            ));
        }
        Ok(())
    }

    fn databases(&self) -> Result<Vec<String>, SparkError> {
        self.check_open()?;
        Ok(self.data_sets.keys().cloned().collect())
    }

    fn database(&self, database: &str) -> Result<&DataSet, SparkError> {
        self.check_open()?;
        self.data_sets.get(database).ok_or_else(|| {
            SparkError::new(
                "SCHEMA_NOT_FOUND",
                format!("Database {} not found", database),
            )
        })
    }

    fn table_types(
        &self,
        database: &str,
    ) -> Result<&BTreeMap<Label, Rc<Type>>, SparkError> {
        match self.database(database)?.type_.as_ref() {
            Type::Record(_, fields) => Ok(fields),
            _ => Err(SparkError::new(
                "SCHEMA_NOT_FOUND",
                format!("Data set {} is not a record", database),
            )),
        }
    }

    fn tables(&self, database: &str) -> Result<Vec<Label>, SparkError> {
        Ok(self.table_types(database)?.keys().cloned().collect())
    }

    fn table_not_found(database: &str, table: &str) -> SparkError {
        SparkError::new(
            "TABLE_OR_VIEW_NOT_FOUND",
            format!("Table {}.{} not found", database, table),
        )
    }

    fn table_type(
        &self,
        database: &str,
        table: &str,
    ) -> Result<Rc<Type>, SparkError> {
        self.table_types(database)?
            .get(&Label::from(table))
            .cloned()
            .ok_or_else(|| Self::table_not_found(database, table))
    }

    fn rows(&self, database: &str, table: &str) -> Result<Val, SparkError> {
        let index = self
            .table_types(database)?
            .keys()
            .position(|label| *label == Label::from(table))
            .ok_or_else(|| Self::table_not_found(database, table))?;
        Ok(self.database(database)?.value.expect_list()[index].clone())
    }
}

/// Key of the type `{...}`, a progressive record with no known fields.
fn progressive_unit() -> Rc<Type> {
    Rc::new(Type::Record(true, BTreeMap::new()))
}

/// Calls the connection, converting an error into the Morel exception
/// `Spark`.
fn call<T>(result: Result<T, SparkError>) -> Result<T, MorelError> {
    result.map_err(|e| e.raise_anywhere())
}

/// The record `{catalog, connection}` that `Spark.connect` returns.
///
/// It is a typed value, so that the type of a name bound to it grows as
/// its catalog is browsed: `spark.catalog.scott.emps` is typed from the
/// value bound to `spark`.
#[derive(Debug)]
pub struct ConnectionRecord {
    pub connection: Rc<Connection>,
    pub catalog: Rc<Catalog>,
}

impl ConnectionRecord {
    /// Opens a connection and returns the record that `Spark.connect`
    /// returns.
    pub fn open(
        uri: &str,
        data_sets: Vec<DataSet>,
    ) -> Result<Rc<ConnectionRecord>, SparkError> {
        let connection = Connection::open(uri, data_sets)?;
        let catalog = connection.catalog();
        Ok(Rc::new(ConnectionRecord {
            connection,
            catalog,
        }))
    }
}

impl TypedValue for ConnectionRecord {
    fn current_type(&self) -> Result<Rc<Type>, MorelError> {
        let mut fields = BTreeMap::new();
        fields.insert(Label::from("catalog"), self.catalog.current_type()?);
        fields.insert(Label::from("connection"), Connection::type_());
        Ok(Rc::new(Type::Record(false, fields)))
    }

    fn discover_field(&self, _field_name: &str) -> Result<bool, MorelError> {
        Ok(false)
    }

    fn child(&self, field_name: &str) -> Result<Option<Child>, MorelError> {
        // A connection is not a typed value: there is nothing in it to
        // discover, and `c.prepare f` names a method of a connection,
        // not a field of one.
        Ok(match field_name {
            "catalog" => {
                Some((Rc::clone(&self.catalog) as Rc<dyn TypedValue>, false))
            }
            _ => None,
        })
    }

    fn field_value(&self, field_name: &str) -> Result<Option<Val>, MorelError> {
        Ok(match field_name {
            "catalog" => Some(Val::Progressive(
                Rc::clone(&self.catalog) as Rc<dyn TypedValue>
            )),
            "connection" => Some(Val::Connection(Rc::clone(&self.connection))),
            _ => None,
        })
    }

    fn known_fields(&self) -> Vec<(Label, Val)> {
        vec![
            (
                Label::from("catalog"),
                Val::Progressive(Rc::clone(&self.catalog) as Rc<dyn TypedValue>),
            ),
            (
                Label::from("connection"),
                Val::Connection(Rc::clone(&self.connection)),
            ),
        ]
    }

    fn describe(&self) -> String {
        format!(
            "{{catalog={},connection={}}}",
            self.catalog.describe(),
            self.connection
        )
    }
}

/// The catalog of a connection: a progressive record of databases.
pub struct Catalog {
    connection: Rc<Connection>,
    databases: RefCell<Option<BTreeMap<Label, Rc<Database>>>>,
}

impl fmt::Debug for Catalog {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Catalog({:?})", self.connection)
    }
}

impl Catalog {
    fn databases(
        &self,
    ) -> Result<Ref<'_, BTreeMap<Label, Rc<Database>>>, MorelError> {
        if self.databases.borrow().is_none() {
            let mut map = BTreeMap::new();
            for name in call(self.connection.databases())? {
                map.insert(
                    Label::from(name.as_str()),
                    Rc::new(Database {
                        connection: Rc::clone(&self.connection),
                        name,
                        tables: RefCell::new(None),
                    }),
                );
            }
            *self.databases.borrow_mut() = Some(map);
        }
        Ok(Ref::map(self.databases.borrow(), |d| {
            d.as_ref().expect("databases were just fetched")
        }))
    }

    fn database(&self, name: &str) -> Result<Option<Rc<Database>>, MorelError> {
        Ok(self.databases()?.get(&Label::from(name)).cloned())
    }
}

impl TypedValue for Catalog {
    fn current_type(&self) -> Result<Rc<Type>, MorelError> {
        let mut fields = BTreeMap::new();
        for (label, database) in self.databases()?.iter() {
            fields.insert(label.clone(), database.type_());
        }
        Ok(Rc::new(Type::Record(true, fields)))
    }

    fn discover_field(&self, field_name: &str) -> Result<bool, MorelError> {
        match self.database(field_name)? {
            Some(database) if database.tables.borrow().is_none() => {
                database.tables()?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn child(&self, field_name: &str) -> Result<Option<Child>, MorelError> {
        let Some(database) = self.database(field_name)? else {
            return Ok(None);
        };
        let widened = database.tables.borrow().is_none();
        database.tables()?;
        Ok(Some((database as Rc<dyn TypedValue>, widened)))
    }

    fn field_value(&self, field_name: &str) -> Result<Option<Val>, MorelError> {
        // Asking the catalog for a database it does not have is the
        // user's mistake, not the adapter's, so it reads as Spark's own
        // error for it.
        match self.database(field_name)? {
            Some(database) => {
                Ok(Some(Val::Progressive(database as Rc<dyn TypedValue>)))
            }
            None => Err(SparkError::new(
                "SCHEMA_NOT_FOUND",
                format!("Database {} not found", field_name),
            )
            .raise_anywhere()),
        }
    }

    fn known_fields(&self) -> Vec<(Label, Val)> {
        match &*self.databases.borrow() {
            Some(databases) => databases
                .iter()
                .map(|(label, database)| {
                    (
                        label.clone(),
                        Val::Progressive(
                            Rc::clone(database) as Rc<dyn TypedValue>
                        ),
                    )
                })
                .collect(),
            None => Vec::new(),
        }
    }

    fn describe(&self) -> String {
        "<catalog>".to_string()
    }
}

/// A database: a progressive record of tables.
pub struct Database {
    connection: Rc<Connection>,
    name: String,
    tables: RefCell<Option<BTreeMap<Label, Rc<Table>>>>,
}

impl fmt::Debug for Database {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Database({})", self.name)
    }
}

impl Database {
    fn tables(
        &self,
    ) -> Result<Ref<'_, BTreeMap<Label, Rc<Table>>>, MorelError> {
        if self.tables.borrow().is_none() {
            let mut map = BTreeMap::new();
            for label in call(self.connection.tables(&self.name))? {
                map.insert(
                    label.clone(),
                    Rc::new(Table {
                        connection: Rc::clone(&self.connection),
                        database: self.name.clone(),
                        name: label.to_string(),
                        type_: RefCell::new(None),
                        rows: RefCell::new(None),
                    }),
                );
            }
            *self.tables.borrow_mut() = Some(map);
        }
        Ok(Ref::map(self.tables.borrow(), |t| {
            t.as_ref().expect("tables were just fetched")
        }))
    }

    fn table(&self, name: &str) -> Result<Option<Rc<Table>>, MorelError> {
        Ok(self.tables()?.get(&Label::from(name)).cloned())
    }

    /// Returns the type as far as it is known, fetching nothing.
    fn type_(&self) -> Rc<Type> {
        match &*self.tables.borrow() {
            None => progressive_unit(),
            Some(tables) => Rc::new(Type::Record(
                true,
                tables
                    .iter()
                    .map(|(label, table)| (label.clone(), table.type_()))
                    .collect(),
            )),
        }
    }
}

impl TypedValue for Database {
    fn current_type(&self) -> Result<Rc<Type>, MorelError> {
        Ok(self.type_())
    }

    fn discover_field(&self, field_name: &str) -> Result<bool, MorelError> {
        match self.table(field_name)? {
            Some(table) if table.type_.borrow().is_none() => {
                table.fetch_type()?;
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn child(&self, field_name: &str) -> Result<Option<Child>, MorelError> {
        let Some(table) = self.table(field_name)? else {
            return Ok(None);
        };
        let widened = table.type_.borrow().is_none();
        table.fetch_type()?;
        Ok(Some((table as Rc<dyn TypedValue>, widened)))
    }

    fn field_value(&self, field_name: &str) -> Result<Option<Val>, MorelError> {
        match self.table(field_name)? {
            Some(table) => Ok(Some(table.rows()?)),
            None => Err(Connection::table_not_found(&self.name, field_name)
                .raise_anywhere()),
        }
    }

    fn known_fields(&self) -> Vec<(Label, Val)> {
        match &*self.tables.borrow() {
            Some(tables) => {
                tables
                    .iter()
                    .map(|(label, table)| {
                        (
                            label.clone(),
                            Val::Progressive(
                                Rc::clone(table) as Rc<dyn TypedValue>
                            ),
                        )
                    })
                    .collect()
            }
            None => Vec::new(),
        }
    }

    fn describe(&self) -> String {
        format!("<database {}>", self.name)
    }
}

/// A table: a bag of records, fetched when first read.
pub struct Table {
    connection: Rc<Connection>,
    database: String,
    name: String,
    type_: RefCell<Option<Rc<Type>>>,
    rows: RefCell<Option<Val>>,
}

impl fmt::Debug for Table {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Table({}.{})", self.database, self.name)
    }
}

impl Table {
    /// Returns the type as far as it is known: `{...} bag` until the
    /// table's type has been fetched.
    fn type_(&self) -> Rc<Type> {
        match &*self.type_.borrow() {
            Some(t) => Rc::clone(t),
            None => Rc::new(Type::Bag(progressive_unit())),
        }
    }

    fn fetch_type(&self) -> Result<Rc<Type>, MorelError> {
        if self.type_.borrow().is_none() {
            let t =
                call(self.connection.table_type(&self.database, &self.name))?;
            *self.type_.borrow_mut() = Some(t);
        }
        Ok(self.type_())
    }

    fn rows(&self) -> Result<Val, MorelError> {
        if self.rows.borrow().is_none() {
            let rows = call(self.connection.rows(&self.database, &self.name))?;
            *self.rows.borrow_mut() = Some(rows);
        }
        Ok(self.rows.borrow().clone().expect("rows were just fetched"))
    }
}

impl TypedValue for Table {
    fn current_type(&self) -> Result<Rc<Type>, MorelError> {
        Ok(self.type_())
    }

    fn discover_field(&self, _field_name: &str) -> Result<bool, MorelError> {
        Ok(false)
    }

    fn child(&self, _field_name: &str) -> Result<Option<Child>, MorelError> {
        Ok(None)
    }

    fn field_value(
        &self,
        _field_name: &str,
    ) -> Result<Option<Val>, MorelError> {
        Ok(None)
    }

    fn known_fields(&self) -> Vec<(Label, Val)> {
        Vec::new()
    }

    fn describe(&self) -> String {
        "<relation>".to_string()
    }
}

// End spark.rs
