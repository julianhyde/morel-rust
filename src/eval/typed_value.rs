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

//! Values that know their own, progressively widening, type.
//!
//! The Rust analog of morel-java's `TypedValue`. A value of this kind
//! is a record whose fields are learned as a program names them: the
//! file system that `file` reads ([`crate::eval::file::File`]), and the
//! catalog of a Spark connection ([`crate::eval::spark`]). At run time
//! such a value is a [`Val::Progressive`]; during type resolution the
//! resolver keeps the value beside the type variable it typed, so that
//! naming a field it does not yet know can widen it.

use crate::compile::types::{Label, Type};
use crate::eval::val::Val;
use crate::shell::kernel::MorelError;
use std::fmt::Debug;
use std::rc::Rc;

/// A field that is itself a typed value, and whether learning its type
/// widened the type of the value it is a field of.
pub type Child = (Rc<dyn TypedValue>, bool);

/// A value that knows its own (potentially progressive) type.
///
/// Every operation that may have to ask an outside source -- a
/// directory, a server -- can fail, and the failure is the Morel
/// exception the source raises; the resolver reports it as it reports
/// any uncaught exception, whether it happened while typing a
/// statement or while evaluating it.
pub trait TypedValue: Debug {
    /// Returns the value's current type, learning what it must first:
    /// the entries of a directory, the databases of a catalog. The type
    /// may widen over the life of the value as fields are discovered.
    fn current_type(&self) -> Result<Rc<Type>, MorelError>;

    /// Tries to widen the type to include `field_name`, a field that
    /// the current type lacks. Returns whether the type widened, in
    /// which case the caller deduces the statement again.
    fn discover_field(&self, field_name: &str) -> Result<bool, MorelError>;

    /// Returns the field named `field_name`, if it is itself a typed
    /// value, having learned its type; and whether learning it widened
    /// this value's type, in which case the caller deduces the
    /// statement again. A field that holds an ordinary value, or no
    /// field at all, gives `None`.
    fn child(&self, field_name: &str) -> Result<Option<Child>, MorelError>;

    /// Returns the value of the field named `field_name`, as a program
    /// reads it: a nested typed value stays one, and a relation is its
    /// rows. `None` if there is no such field.
    fn field_value(&self, field_name: &str) -> Result<Option<Val>, MorelError>;

    /// Returns the fields known so far, for printing, without asking any
    /// source for more. A relation is given as a typed value, so that it
    /// prints as `<relation>` rather than as its rows.
    fn known_fields(&self) -> Vec<(Label, Val)>;

    /// Returns the text that the value prints as when no type guides
    /// the printer.
    fn describe(&self) -> String;
}

// End typed_value.rs
