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

//! A connection to a Spark Connect server, over gRPC.
//!
//! Port of morel-java's `SparkConnection`. The channel does not dial
//! until the first call, so a connection opens whether or not the
//! server is up, and a server that is not there is reported where it
//! is noticed. Each call blocks until its answer has arrived.

use crate::compile::types::Type;
use crate::eval::spark::SparkError;
use crate::eval::val::Val;
use crate::spark::arrow;
use crate::spark::plan::Plan;
use crate::spark::proto::analyze_plan_request::{self, Analyze};
use crate::spark::proto::analyze_plan_response;
use crate::spark::proto::execute_plan_response::ResponseType;
use crate::spark::proto::plan::OpType;
use crate::spark::proto::read::{NamedTable, ReadType};
use crate::spark::proto::relation::RelType;
use crate::spark::proto::{
    self as proto, AnalyzePlanRequest, AnalyzePlanResponse, DataType,
    ExecutePlanRequest, ExecutePlanResponse, Read, Relation, Sql, UserContext,
};
use crate::spark::types;
use prost::Message;
use std::cell::RefCell;
use std::collections::hash_map::RandomState;
use std::collections::{HashMap, HashSet};
use std::env;
use std::hash::{BuildHasher, Hasher};
use std::rc::Rc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::runtime::{Builder, Runtime};
use tonic::client::Grpc;
use tonic::codegen::http::uri::PathAndQuery;
use tonic::transport::{Channel, Endpoint};
use tonic::{Request, Status};
use tonic_prost::ProstCodec;

/// Default port of a Spark Connect server.
const DEFAULT_PORT: u16 = 15002;

/// The largest message the connection accepts from the server. A batch
/// of rows is one message, and Spark sizes its batches to about 4 MiB,
/// which is gRPC's default limit; this leaves room.
const MAX_MESSAGE_SIZE: usize = 256 * 1024 * 1024;

/// How long the connection waits for the server to accept a channel.
/// It bounds only the dialing, not a query, which may run as long as
/// it needs.
const CONNECT_TIMEOUT: Duration = Duration::from_secs(30);

/// Name of the table property that says which of a table's columns may
/// be null, because Spark keeps no such constraint of its own.
const NULLABLE_PROPERTY: &str = "morel.nullable";

const EXECUTE_PLAN: &str = "/spark.connect.SparkConnectService/ExecutePlan";
const ANALYZE_PLAN: &str = "/spark.connect.SparkConnectService/AnalyzePlan";

/// The status that a gRPC failure carries in its details, as
/// `google.rpc.Status`.
#[derive(Clone, PartialEq, Message)]
struct RpcStatus {
    #[prost(int32, tag = "1")]
    code: i32,
    #[prost(string, tag = "2")]
    message: String,
    #[prost(message, repeated, tag = "3")]
    details: Vec<prost_types::Any>,
}

/// `google.rpc.ErrorInfo`, which Spark attaches to a failure: the reason
/// is the Java exception class, and the metadata includes `errorClass`,
/// Spark's error condition, when the error has one.
#[derive(Clone, PartialEq, Message)]
struct ErrorInfo {
    #[prost(string, tag = "1")]
    reason: String,
    #[prost(string, tag = "2")]
    domain: String,
    #[prost(map = "string, string", tag = "3")]
    metadata: HashMap<String, String>,
}

/// A connection to a Spark Connect server.
pub struct RemoteConnection {
    runtime: Runtime,
    /// The channel, until the connection is closed.
    channel: RefCell<Option<Channel>>,
    session_id: String,
    user_id: String,
    /// Columns the connection was told may be null, as
    /// "database.table.column" in lower case.
    nullable_columns: HashSet<String>,
}

impl RemoteConnection {
    /// Opens a connection to the server that `uri` names,
    /// `sc://host[:port][/;param=value...]`.
    pub fn open(uri: &str) -> Result<RemoteConnection, SparkError> {
        let invalid = || {
            SparkError::new(
                "CONNECTION",
                format!(
                    "Invalid Spark Connect URI: {} (expected \
                     sc://host[:port][/;param=value...])",
                    uri
                ),
            )
        };
        let rest = uri.strip_prefix("sc://").ok_or_else(invalid)?;
        let (authority, path) = match rest.find(['/', ';']) {
            Some(i) => (&rest[..i], &rest[i..]),
            None => (rest, ""),
        };
        let (host, port) = match authority.rsplit_once(':') {
            Some((host, port)) => {
                (host, port.parse::<u16>().map_err(|_| invalid())?)
            }
            None => (authority, DEFAULT_PORT),
        };
        if host.is_empty() {
            return Err(invalid());
        }
        let mut user_id = env::var("USER").unwrap_or_else(|_| "morel".into());
        let mut nullable_columns = HashSet::new();
        // Parameters follow the path, separated by ';', e.g.
        // "sc://host:port/;user_id=fred;token=...".
        for param in path.split(';') {
            let Some((key, value)) = param.split_once('=') else {
                continue;
            };
            if key.is_empty() {
                continue;
            }
            if key == "user_id" {
                user_id = value.to_string();
            } else if key == "nullable" {
                // Which columns may be null, as "database.table.column",
                // separated by commas. Spark cannot tell us -- it calls
                // every column of a stored table nullable -- so whoever
                // knows the data says so here.
                for column in value.split(',') {
                    if !column.is_empty() {
                        nullable_columns.insert(column.to_lowercase());
                    }
                }
            }
        }
        let runtime = Builder::new_current_thread()
            .enable_all()
            .build()
            .map_err(|e| SparkError::new("CONNECTION", e.to_string()))?;
        let endpoint =
            Endpoint::from_shared(format!("http://{}:{}", host, port))
                .map_err(|_| invalid())?
                .connect_timeout(CONNECT_TIMEOUT);
        let channel = {
            let _guard = runtime.enter();
            endpoint.connect_lazy()
        };
        Ok(RemoteConnection {
            runtime,
            channel: RefCell::new(Some(channel)),
            session_id: session_id(),
            user_id,
            nullable_columns,
        })
    }

    /// Closes the connection.
    pub fn close(&self) {
        self.channel.borrow_mut().take();
    }

    fn channel(&self) -> Result<Channel, SparkError> {
        self.channel.borrow().clone().ok_or_else(|| {
            SparkError::new("CLOSED", "Connection is closed".to_string())
        })
    }

    fn user_context(&self) -> Option<UserContext> {
        Some(UserContext {
            user_id: self.user_id.clone(),
            ..Default::default()
        })
    }

    /// Runs a plan whose root is `relation`, and returns what comes back
    /// undecoded: the schema Spark gave, and the Arrow batches.
    fn batches(
        &self,
        relation: Relation,
    ) -> Result<(DataType, Vec<Vec<u8>>), SparkError> {
        let request = ExecutePlanRequest {
            session_id: self.session_id.clone(),
            user_context: self.user_context(),
            client_type: Some("morel".to_string()),
            plan: Some(proto::Plan {
                op_type: Some(OpType::Root(relation)),
            }),
            ..Default::default()
        };
        let channel = self.channel()?;
        let result = self.runtime.block_on(async move {
            let mut grpc =
                Grpc::new(channel).max_decoding_message_size(MAX_MESSAGE_SIZE);
            grpc.ready()
                .await
                .map_err(|e| Status::unavailable(e.to_string()))?;
            let codec: ProstCodec<ExecutePlanRequest, ExecutePlanResponse> =
                ProstCodec::default();
            let mut stream = grpc
                .server_streaming(
                    Request::new(request),
                    PathAndQuery::from_static(EXECUTE_PLAN),
                    codec,
                )
                .await?
                .into_inner();
            let mut schema = None;
            let mut batches = Vec::new();
            while let Some(response) = stream.message().await? {
                if response.schema.is_some() {
                    schema = response.schema;
                }
                if let Some(ResponseType::ArrowBatch(batch)) =
                    response.response_type
                {
                    batches.push(batch.data);
                }
            }
            Ok::<_, Status>((schema, batches))
        });
        let (schema, batches) = result.map_err(|s| to_error(&s))?;
        match schema {
            Some(schema) => Ok((schema, batches)),
            None => Err(SparkError::new(
                "CONNECTION",
                "Spark returned no schema for the query",
            )),
        }
    }

    /// Returns the schema of a plan whose root is `relation`.
    fn analyze(&self, relation: Relation) -> Result<DataType, SparkError> {
        let request = AnalyzePlanRequest {
            session_id: self.session_id.clone(),
            user_context: self.user_context(),
            client_type: Some("morel".to_string()),
            analyze: Some(Analyze::Schema(analyze_plan_request::Schema {
                plan: Some(proto::Plan {
                    op_type: Some(OpType::Root(relation)),
                }),
            })),
            ..Default::default()
        };
        let channel = self.channel()?;
        let response = self.runtime.block_on(async move {
            let mut grpc =
                Grpc::new(channel).max_decoding_message_size(MAX_MESSAGE_SIZE);
            grpc.ready()
                .await
                .map_err(|e| Status::unavailable(e.to_string()))?;
            let codec: ProstCodec<AnalyzePlanRequest, AnalyzePlanResponse> =
                ProstCodec::default();
            grpc.unary(
                Request::new(request),
                PathAndQuery::from_static(ANALYZE_PLAN),
                codec,
            )
            .await
        });
        let response = response.map_err(|s| to_error(&s))?.into_inner();
        match response.result {
            Some(analyze_plan_response::Result::Schema(s)) => {
                Ok(s.schema.unwrap_or_default())
            }
            _ => Ok(DataType::default()),
        }
    }

    /// Executes a SQL query and returns the type of its rows, and its
    /// rows.
    fn sql(&self, sql: &str) -> Result<(Rc<Type>, Vec<Val>), SparkError> {
        let relation = Relation {
            common: None,
            rel_type: Some(RelType::Sql(Sql {
                query: sql.to_string(),
                ..Default::default()
            })),
        };
        let (schema, batches) = self.batches(relation)?;
        let row_type = types::row_type(&schema, &HashSet::new())?;
        let rows = arrow::decode(&batches, &row_type)?;
        Ok((row_type, rows))
    }

    /// Executes a plan and returns its rows, as Morel values of
    /// `element_type`, which is the type the query has in Morel, rather
    /// than whatever Spark's schema says.
    pub fn execute(
        &self,
        plan: &Plan,
        element_type: &Type,
    ) -> Result<Vec<Val>, SparkError> {
        let Some(OpType::Root(root)) = &plan.proto().op_type else {
            return Err(SparkError::new("UNSUPPORTED", "Not a Spark plan"));
        };
        let (_, batches) = self.batches(root.clone())?;
        arrow::decode(&batches, element_type)
    }

    /// Returns the names of the databases in the catalog.
    pub fn databases(&self) -> Result<Vec<String>, SparkError> {
        column(self.sql("SHOW DATABASES")?, "namespace")
    }

    /// Returns the names of the tables in a database.
    pub fn tables(&self, database: &str) -> Result<Vec<String>, SparkError> {
        column(
            self.sql(&format!("SHOW TABLES IN {}", quote(database)))?,
            "tableName",
        )
    }

    /// Returns the columns of one table that the URI declared nullable,
    /// by their own names; `*` means every column.
    fn uri_nullable_columns(
        &self,
        database: &str,
        table: &str,
    ) -> HashSet<String> {
        if self.nullable_columns.contains("*") {
            return HashSet::from(["*".to_string()]);
        }
        let prefix = format!("{}.{}.", database, table).to_lowercase();
        self.nullable_columns
            .iter()
            .filter_map(|c| c.strip_prefix(&prefix).map(str::to_string))
            .collect()
    }

    /// Returns the columns that a table's own metadata declares
    /// nullable, or `None` if it declares nothing. The property is a
    /// complete answer for the table it is on.
    fn property_nullable_columns(
        &self,
        database: &str,
        table: &str,
    ) -> Result<Option<HashSet<String>>, SparkError> {
        let (_, rows) = self.sql(&format!(
            "SHOW TBLPROPERTIES {}.{}",
            quote(database),
            quote(table)
        ))?;
        for row in &rows {
            if let Val::List(pair) = row
                && pair.len() == 2
                && let (Val::String(key), Val::String(value)) =
                    (&pair[0], &pair[1])
                && key.as_ref() == NULLABLE_PROPERTY
            {
                return Ok(Some(
                    value
                        .split(',')
                        .map(|c| c.trim().to_lowercase())
                        .filter(|c| !c.is_empty())
                        .collect(),
                ));
            }
        }
        Ok(None)
    }

    /// Returns which of a table's columns may be null, from whichever
    /// source says: the connection's own declaration first, then the
    /// table's property; if neither speaks, no column is optional.
    fn nullable_columns_of(
        &self,
        database: &str,
        table: &str,
    ) -> Result<HashSet<String>, SparkError> {
        let uri_columns = self.uri_nullable_columns(database, table);
        if !uri_columns.is_empty() {
            return Ok(uri_columns);
        }
        Ok(self
            .property_nullable_columns(database, table)?
            .unwrap_or_default())
    }

    /// Returns the Morel type of a table: a bag of records.
    pub fn table_type(
        &self,
        database: &str,
        table: &str,
    ) -> Result<Rc<Type>, SparkError> {
        let schema = self.analyze(read(database, table))?;
        let row_type = types::row_type(
            &schema,
            &self.nullable_columns_of(database, table)?,
        )?;
        Ok(Rc::new(Type::Bag(row_type)))
    }

    /// Returns the rows of a table, decoded as the type this connection
    /// says the table has, which is not always the type Spark's own
    /// schema would give.
    pub fn rows(
        &self,
        database: &str,
        table: &str,
    ) -> Result<Vec<Val>, SparkError> {
        let row_type = match self.table_type(database, table)?.as_ref() {
            Type::Bag(row_type) => Rc::clone(row_type),
            t => Rc::new(t.clone()),
        };
        let (_, batches) = self.batches(read(database, table))?;
        arrow::decode(&batches, &row_type)
    }
}

/// Returns a column of a result as strings.
fn column(
    (row_type, rows): (Rc<Type>, Vec<Val>),
    name: &str,
) -> Result<Vec<String>, SparkError> {
    let index = match row_type.as_ref() {
        Type::Record(_, fields) => {
            fields.keys().position(|l| l.to_string() == name)
        }
        _ => None,
    };
    let Some(index) = index else {
        return Err(SparkError::new(
            "CONNECTION",
            format!("Result has no column {}", name),
        ));
    };
    Ok(rows
        .iter()
        .map(|row| match &row.expect_list()[index] {
            Val::String(s) => s.to_string(),
            v => v.to_string(),
        })
        .collect())
}

/// Returns a relation that reads a table.
fn read(database: &str, table: &str) -> Relation {
    Relation {
        common: None,
        rel_type: Some(RelType::Read(Read {
            read_type: Some(ReadType::NamedTable(NamedTable {
                unparsed_identifier: format!(
                    "{}.{}",
                    quote(database),
                    quote(table)
                ),
                options: HashMap::new(),
            })),
            is_streaming: false,
        })),
    }
}

/// Quotes an identifier with back-ticks, as Spark SQL does.
fn quote(identifier: &str) -> String {
    format!("`{}`", identifier.replace('`', "``"))
}

/// Converts a gRPC failure into a [`SparkError`], carrying Spark's error
/// class if the server sent one.
fn to_error(status: &Status) -> SparkError {
    let mut error_class = "CONNECTION".to_string();
    let message = if status.message().is_empty() {
        status.to_string()
    } else {
        status.message().to_string()
    };
    if let Ok(rpc) = RpcStatus::decode(status.details()) {
        for any in &rpc.details {
            if any.type_url.ends_with("/google.rpc.ErrorInfo")
                && let Ok(info) = ErrorInfo::decode(any.value.as_slice())
            {
                error_class = info
                    .metadata
                    .get("errorClass")
                    .cloned()
                    .unwrap_or(info.reason);
            }
        }
    }
    SparkError::new(error_class, message)
}

/// Returns a random session id, a version 4 UUID, which is what Spark
/// requires a session id to be.
fn session_id() -> String {
    let mut bits = 0u128;
    for i in 0..2 {
        let mut hasher = RandomState::new().build_hasher();
        hasher.write_u128(
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_or(0, |d| d.as_nanos()),
        );
        hasher.write_usize(i);
        bits = (bits << 64) | hasher.finish() as u128;
    }
    // Version 4, variant 1.
    bits = (bits & !(0xf << 76)) | (0x4 << 76);
    bits = (bits & !(0x3 << 62)) | (0x2 << 62);
    let hex = format!("{:032x}", bits);
    format!(
        "{}-{}-{}-{}-{}",
        &hex[0..8],
        &hex[8..12],
        &hex[12..16],
        &hex[16..20],
        &hex[20..32]
    )
}

// End client.rs
