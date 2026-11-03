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
//! Port of morel-java's `MockSparkConnection`, `SparkCatalog`,
//! `SparkConnections` and `PreparedPlan`: the side of the `Spark`
//! structure that does not need the Spark adapter, [`crate::spark`],
//! which translates a query to a plan and talks to a server. The
//! offline connection, whose URI is `mock:`, has the session's data
//! sets as its catalog; a plan can be prepared on it, but not
//! executed. Any other URI names a Spark Connect server, whose catalog
//! is the server's. Where the adapter is absent, as in a wasm build,
//! connecting to a server or preparing a plan raises `Spark` with
//! error class `CONNECTION`, as morel-java does.
//!
//! A catalog is a progressive record whose fields are databases, whose
//! fields in turn are tables, each a bag of records. Nothing is fetched
//! until it is needed: the databases when the root's type is first
//! asked for, a database's tables when the database is first
//! discovered, a table's type when the table is first discovered, and
//! its rows when its value is first read. Each fetch happens once.

use crate::compile::core::Expr;
use crate::compile::library::{BuiltInExn, BuiltInFunction};
use crate::compile::rel_lowerer::{map_children, map_steps};
use crate::compile::span::Span;
use crate::compile::types::{Label, Type};
use crate::eval::typed_value::{Child, TypedValue};
use crate::eval::val::Val;
use crate::shell::kernel::MorelError;
use crate::spark as spark_adapter;
use std::cell::{Cell, Ref, RefCell};
use std::collections::BTreeMap;
use std::env;
use std::fmt;
use std::rc::{Rc, Weak};

/// The URI that opens the offline connection.
pub const MOCK_URI: &str = "mock:";

/// Environment variable that names the default server.
pub const SPARK_REMOTE: &str = "SPARK_REMOTE";

/// Message of the `CONNECTION` error that every operation needing the
/// Spark adapter raises where the adapter is absent, as in a wasm
/// build.
pub const ADAPTER_UNAVAILABLE: &str = "The Spark adapter is not available; \
     it needs JDK 17 or later and the 'spark' Maven profile";

/// A failure that the Morel exception `Spark` reports: Spark's error
/// class, such as `TABLE_OR_VIEW_NOT_FOUND`, or one of the adapter's
/// own, such as `CONNECTION` or `CLOSED`, and a message.
#[derive(Clone, Debug)]
pub struct SparkError {
    pub error_class: String,
    pub message: String,
}

impl fmt::Display for SparkError {
    /// Writes the error as morel-java's `SparkException` writes itself,
    /// which is how it reads where it escapes uncaught as an error of
    /// the implementation rather than as the Morel exception.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Spark {{errorClass = \"{}\", message = \"{}\"}}",
            self.error_class, self.message
        )
    }
}

impl SparkError {
    pub fn new(
        error_class: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        SparkError {
            error_class: error_class.into(),
            message: message.into(),
        }
    }

    /// Returns whether this error is a refusal to translate, as against
    /// a failure of something else. Only a refusal has a local answer
    /// that is the same answer.
    pub fn is_refusal(&self) -> bool {
        matches!(
            self.error_class.as_str(),
            "UNSUPPORTED" | "UNSUPPORTED_TYPE"
        )
    }

    /// Converts this error into a Morel exception, raised at `span`.
    ///
    /// A failure that local evaluation has a name for raises the
    /// exception it raises locally, so that a query fails the same way
    /// wherever it ran: dividing by zero is `Div` whether Spark noticed
    /// it or Morel did. Everything else raises `Spark {errorClass,
    /// message}`.
    pub fn raise(&self, span: &Span) -> MorelError {
        match self.error_class.as_str() {
            "DIVIDE_BY_ZERO" | "INTERVAL_DIVIDED_BY_ZERO" => {
                MorelError::Runtime(BuiltInExn::Div, span.clone())
            }
            "ARITHMETIC_OVERFLOW"
            | "CAST_OVERFLOW"
            | "BINARY_ARITHMETIC_OVERFLOW" => {
                MorelError::Runtime(BuiltInExn::Overflow, span.clone())
            }
            _ => MorelError::Runtime2(
                BuiltInExn::Spark,
                Some(format!("{}: {}", self.error_class, self.message)),
                span.clone(),
            ),
        }
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

/// A connection: to a Spark Connect server, or the offline one, whose
/// catalog is the session's data sets and which can execute nothing.
pub struct Connection {
    uri: String,
    backend: Backend,
    closed: Cell<bool>,
    /// The connection's catalog, created on first use, so that what is
    /// discovered accumulates; forgotten when the connection closes.
    catalog: RefCell<Option<Rc<Catalog>>>,
}

/// What a connection talks to.
enum Backend {
    /// The offline connection, and the data sets that are its catalog.
    Mock(BTreeMap<String, DataSet>),
    /// A server.
    Remote(spark_adapter::RemoteConnection),
}

impl fmt::Debug for Connection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Connection({})", self.uri)
    }
}

impl fmt::Display for Connection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<connection {}>", self.uri)
    }
}

impl Connection {
    /// Opens a connection to `uri`: the offline one if it is `mock:`,
    /// whose catalog is `data_sets`; otherwise a server, which needs
    /// the adapter.
    pub fn open(
        uri: &str,
        data_sets: Vec<DataSet>,
    ) -> Result<Rc<Connection>, SparkError> {
        let backend = if uri == MOCK_URI {
            Backend::Mock(
                data_sets.into_iter().map(|d| (d.name.clone(), d)).collect(),
            )
        } else if !spark_adapter::is_available() {
            return Err(adapter_unavailable());
        } else {
            Backend::Remote(spark_adapter::RemoteConnection::open(uri)?)
        };
        Ok(Rc::new(Connection {
            uri: uri.to_string(),
            backend,
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
        if !self.closed.replace(true)
            && let Backend::Remote(remote) = &self.backend
        {
            remote.close();
        }
    }

    fn check_open(&self) -> Result<(), SparkError> {
        if self.closed.get() {
            return Err(SparkError::new(
                "CLOSED",
                format!("Connection to {} is closed", self.uri),
            ));
        }
        Ok(())
    }

    fn databases(&self) -> Result<Vec<String>, SparkError> {
        self.check_open()?;
        match &self.backend {
            Backend::Mock(data_sets) => Ok(data_sets.keys().cloned().collect()),
            Backend::Remote(remote) => remote.databases(),
        }
    }

    fn data_set<'a>(
        data_sets: &'a BTreeMap<String, DataSet>,
        database: &str,
    ) -> Result<&'a DataSet, SparkError> {
        data_sets.get(database).ok_or_else(|| {
            SparkError::new(
                "SCHEMA_NOT_FOUND",
                format!("Database {} not found", database),
            )
        })
    }

    fn table_types<'a>(
        data_sets: &'a BTreeMap<String, DataSet>,
        database: &str,
    ) -> Result<&'a BTreeMap<Label, Rc<Type>>, SparkError> {
        match Self::data_set(data_sets, database)?.type_.as_ref() {
            Type::Record(_, fields) => Ok(fields),
            _ => Err(SparkError::new(
                "SCHEMA_NOT_FOUND",
                format!("Data set {} is not a record", database),
            )),
        }
    }

    fn tables(&self, database: &str) -> Result<Vec<Label>, SparkError> {
        self.check_open()?;
        match &self.backend {
            Backend::Mock(data_sets) => {
                Ok(Self::table_types(data_sets, database)?
                    .keys()
                    .cloned()
                    .collect())
            }
            Backend::Remote(remote) => Ok(remote
                .tables(database)?
                .iter()
                .map(|t| Label::from(t.as_str()))
                .collect()),
        }
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
        self.check_open()?;
        match &self.backend {
            Backend::Mock(data_sets) => Self::table_types(data_sets, database)?
                .get(&Label::from(table))
                .cloned()
                .ok_or_else(|| Self::table_not_found(database, table)),
            Backend::Remote(remote) => remote.table_type(database, table),
        }
    }

    /// Executes a plan and returns its rows, as Morel values of
    /// `element_type`. The offline connection translates a query but
    /// cannot run one, and says so rather than pretending to have no
    /// rows.
    pub fn execute(
        &self,
        plan: &spark_adapter::Plan,
        element_type: &Type,
    ) -> Result<Vec<Val>, SparkError> {
        self.check_open()?;
        match &self.backend {
            Backend::Mock(_) => Err(SparkError::new(
                "MOCK",
                "The offline connection cannot execute a plan; connect to a \
                 server",
            )),
            Backend::Remote(remote) => remote.execute(plan, element_type),
        }
    }

    fn rows(&self, database: &str, table: &str) -> Result<Val, SparkError> {
        self.check_open()?;
        match &self.backend {
            Backend::Mock(data_sets) => {
                let index = Self::table_types(data_sets, database)?
                    .keys()
                    .position(|label| *label == Label::from(table))
                    .ok_or_else(|| Self::table_not_found(database, table))?;
                Ok(Self::data_set(data_sets, database)?.value.expect_list()
                    [index]
                    .clone())
            }
            Backend::Remote(remote) => {
                Ok(Val::List(Rc::new(remote.rows(database, table)?)))
            }
        }
    }
}

/// A plan prepared on a connection: the value of Morel's `('a, 'b)
/// plan`.
///
/// `prepare` translates a function for a connection, and afterwards
/// both are needed: the plan to print or to run, and the connection to
/// run it on. So is the Morel type of the result, because that is the
/// type the program was typed against, and the rows have to come back
/// as values of it.
///
/// A function with parameters is held as the query rather than as a
/// plan, and translated at each execution with the argument in place
/// of them, because Spark has nowhere in a plan to keep a parameter.
///
/// It prints as `<plan>`; asking for its text is what `Spark.toString`
/// is for.
pub struct PreparedPlan {
    connection: Rc<Connection>,
    query: Expr,
    parameters: Vec<String>,
    plan: Option<spark_adapter::Plan>,
    element_type: Rc<Type>,
    collection: bool,
}

impl fmt::Debug for PreparedPlan {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<plan>")
    }
}

impl PreparedPlan {
    /// Creates a prepared plan. A query with no parameters is
    /// translated once, here, so that its plan is the same plan however
    /// often it is used.
    pub fn new(
        connection: Rc<Connection>,
        query: Expr,
        parameters: Vec<String>,
        element_type: Rc<Type>,
        collection: bool,
    ) -> Result<PreparedPlan, SparkError> {
        let plan = if parameters.is_empty() {
            Some(spark_adapter::translate(&query)?)
        } else {
            None
        };
        Ok(PreparedPlan {
            connection,
            query,
            parameters,
            plan,
            element_type,
            collection,
        })
    }

    /// Describes the plan where a plan description shows it, as
    /// `Sys.plan` does: `spark(plan ...)`, or, for a plan with a
    /// parameter, which has no text until it is executed, the
    /// parameters it is waiting for.
    pub fn describe(&self) -> String {
        match &self.plan {
            Some(plan) => format!("spark(plan {})", plan.text()),
            None => {
                format!("spark(parameters [{}])", self.parameters.join(", "))
            }
        }
    }

    /// Returns the plan as text.
    pub fn text(&self) -> Result<String, SparkError> {
        match &self.plan {
            Some(plan) => Ok(plan.text()),
            None => Err(SparkError::new(
                "UNSUPPORTED",
                "A plan with a parameter has no text until it is given one; \
                 execute it instead",
            )),
        }
    }

    /// Executes the plan on an argument and returns its result: the
    /// rows, or, where the query computes a single value, that value.
    pub fn execute(&self, arg: &Val) -> Result<Val, SparkError> {
        let rows = if let Some(plan) = &self.plan {
            self.connection.execute(plan, &self.element_type)?
        } else {
            let plan = spark_adapter::translate(&self.substitute(arg))?;
            self.connection.execute(&plan, &self.element_type)?
        };
        if self.collection {
            return Ok(Val::List(Rc::new(rows)));
        }
        if rows.len() != 1 {
            return Err(SparkError::new(
                "CONNECTION",
                format!(
                    "Query computes one value, but Spark returned {} rows",
                    rows.len()
                ),
            ));
        }
        Ok(rows.into_iter().next().expect("one row"))
    }

    /// Returns the query with an argument in place of its parameters.
    /// One parameter takes the whole argument; several take its
    /// components, one each.
    fn substitute(&self, arg: &Val) -> Expr {
        let mut values = BTreeMap::new();
        if self.parameters.len() == 1 {
            values.insert(self.parameters[0].clone(), arg.clone());
        } else {
            for (p, v) in self.parameters.iter().zip(arg.expect_list()) {
                values.insert(p.clone(), v.clone());
            }
        }
        substitute(&self.query, &values)
    }
}

/// Returns `e` with each identifier that `values` names replaced by a
/// literal of its value.
fn substitute(e: &Expr, values: &BTreeMap<String, Val>) -> Expr {
    match e {
        Expr::Identifier(t, name) if values.contains_key(name) => {
            Expr::Literal(t.clone(), values[name].clone())
        }
        Expr::Rel(t, rel) => Expr::Rel(
            t.clone(),
            Box::new(rel.map_children(&|c| substitute(c, values))),
        ),
        Expr::From(t, steps) => {
            Expr::From(t.clone(), map_steps(steps, &|c| substitute(c, values)))
        }
        _ => map_children(e, &|c| substitute(c, values)),
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
            // The rows are a list of the table's own, so that a list
            // that is these rows is known to be this table, however the
            // program reached it; a data set of the session's that holds
            // the same rows is not.
            let rows = Rc::new(rows.expect_list().to_vec());
            TABLE_ROWS.with(|t| {
                let mut t = t.borrow_mut();
                t.retain(|(rows, _)| rows.strong_count() > 0);
                t.push((Rc::downgrade(&rows), self.qualified()));
            });
            *self.rows.borrow_mut() = Some(Val::List(rows));
        }
        Ok(self.rows.borrow().clone().expect("rows were just fetched"))
    }

    /// Returns the name Spark knows this table by.
    fn qualified(&self) -> String {
        format!("{}.{}", self.database, self.name)
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

    fn qualified_name(&self) -> Option<String> {
        Some(self.qualified())
    }
}

thread_local! {
    /// The rows of each table that has been read, and the name Spark
    /// knows the table by.
    static TABLE_ROWS: RefCell<Vec<(Weak<Vec<Val>>, String)>> =
        const { RefCell::new(Vec::new()) };
}

/// Returns the name of the table whose rows `rows` are, if they are
/// the rows of a table of a catalog.
///
/// A query that reads a name bound to a table -- `val emps =
/// spark.catalog.scott.emps` -- reads its rows, and the rows remember
/// the table, so that the query is a scan of it rather than rows to
/// send.
pub fn table_of_rows(rows: &Rc<Vec<Val>>) -> Option<String> {
    TABLE_ROWS.with(|t| {
        t.borrow()
            .iter()
            .find(|(r, _)| r.upgrade().is_some_and(|r| Rc::ptr_eq(&r, rows)))
            .map(|(_, name)| name.clone())
    })
}

// End spark.rs
