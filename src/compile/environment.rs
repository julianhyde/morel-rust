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

use std::collections::{HashMap, HashSet};
use std::fmt;

/// Environment for validation/compilation.
///
/// Every environment is immutable; when you call `bind`, a new
/// environment is created that inherits from the previous environment. The new
/// environment may obscure bindings in the old environment, but neither the new
/// nor the old will ever change.
pub trait Environment {
    /// Visits every variable binding in this environment.
    ///
    /// Bindings that are obscured by more recent bindings of the same name are
    /// visited, but after the more obscuring bindings.
    fn visit<F>(&self, consumer: F)
    where
        F: FnMut(&Binding);

    /// Returns the top binding of `name`.
    ///
    /// If the top binding is overloaded, there may be other bindings. But at
    /// least it gives you a `NamedPat` with which to call `collect`.
    fn get_top(&self, name: &str) -> Option<&Binding>;

    /// Returns the binding of `name` if bound, None if not.
    fn get_opt(&self, name: &str) -> Option<&Binding>;

    /// Returns the binding of `id` if bound, None if not.
    fn get_opt_by_id(&self, id: &NamedPat) -> Option<&Binding>;

    /// Alternative version of `get_opt_by_id`.
    fn get_opt2(&self, id: &NamedPat) -> Option<&Binding>;

    /// Calls a consumer for all bindings of `id`.
    fn collect<F>(&self, id: &NamedPat, consumer: F)
    where
        F: FnMut(&Binding);

    /// Creates an environment that is the same as this, plus one more variable.
    fn bind(&self, id: IdPat, value: Value) -> Box<dyn Environment>;

    /// Creates an environment that is the same as this, plus the given bindings.
    fn bind_all(&self, bindings: &[Binding]) -> Box<dyn Environment>;

    /// Returns whether a given name is overloaded in this environment.
    fn has_overloaded(&self, name: &str) -> bool;

    /// Returns the overloads for a given ID.
    fn get_overloads(&self, id: &IdPat) -> Vec<IdPat>;

    /// Returns a map of the values and bindings.
    fn get_value_map(&self, skip_overloads: bool) -> HashMap<String, Binding>;
}

/// A binding in the environment.
#[derive(Debug, Clone, PartialEq)]
pub struct Binding {
    pub id: NamedPat,
    pub kind: BindingKind,
    pub value: Value,
    pub overload_id: Option<NamedPat>,
}

impl Binding {
    pub fn new(id: NamedPat, kind: BindingKind, value: Value) -> Self {
        Self {
            id,
            kind,
            value,
            overload_id: None,
        }
    }

    pub fn with_overload(id: NamedPat, kind: BindingKind, value: Value, overload_id: NamedPat) -> Self {
        Self {
            id,
            kind,
            value,
            overload_id: Some(overload_id),
        }
    }

    pub fn is_inst(&self) -> bool {
        matches!(self.kind, BindingKind::Inst)
    }

    pub fn with_flattened_name(&self) -> Self {
        let mut binding = self.clone();
        binding.id = self.id.flatten();
        binding
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BindingKind {
    Val,
    Inst,
    Over,
}

/// A named pattern in the AST.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NamedPat {
    pub name: String,
    pub ordinal: u32,
}

impl NamedPat {
    pub fn new(name: String, ordinal: u32) -> Self {
        Self { name, ordinal }
    }

    pub fn flatten(&self) -> Self {
        Self::new(self.name.clone(), 0)
    }
}

/// An identifier pattern.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IdPat {
    pub name: String,
    pub ordinal: u32,
}

impl IdPat {
    pub fn new(name: String, ordinal: u32) -> Self {
        Self { name, ordinal }
    }
}

/// A value in the environment.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Unit,
    Typed(TypedValue),
    Other(String), // For other value types
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypedValue {
    pub type_key: String, // Simplified type representation
}

/// Empty environment implementation.
pub struct EmptyEnvironment;

impl Environment for EmptyEnvironment {
    fn visit<F>(&self, _consumer: F)
    where
        F: FnMut(&Binding),
    {
        // Empty environment has no bindings to visit
    }

    fn get_top(&self, _name: &str) -> Option<&Binding> {
        None
    }

    fn get_opt(&self, _name: &str) -> Option<&Binding> {
        None
    }

    fn get_opt_by_id(&self, _id: &NamedPat) -> Option<&Binding> {
        None
    }

    fn get_opt2(&self, _id: &NamedPat) -> Option<&Binding> {
        None
    }

    fn collect<F>(&self, _id: &NamedPat, _consumer: F)
    where
        F: FnMut(&Binding),
    {
        // Empty environment has no bindings to collect
    }

    fn bind(&self, id: IdPat, value: Value) -> Box<dyn Environment> {
        let named_pat = NamedPat::new(id.name, id.ordinal);
        let binding = Binding::new(named_pat, BindingKind::Val, value);
        Box::new(SubEnvironment::new(Box::new(EmptyEnvironment), binding))
    }

    fn bind_all(&self, bindings: &[Binding]) -> Box<dyn Environment> {
        let mut env: Box<dyn Environment> = Box::new(EmptyEnvironment);
        for binding in bindings.iter().rev() {
            env = Box::new(SubEnvironment::new(env, binding.clone()));
        }
        env
    }

    fn has_overloaded(&self, _name: &str) -> bool {
        false
    }

    fn get_overloads(&self, _id: &IdPat) -> Vec<IdPat> {
        Vec::new()
    }

    fn get_value_map(&self, _skip_overloads: bool) -> HashMap<String, Binding> {
        HashMap::new()
    }
}

/// Sub-environment that extends a parent environment with one additional binding.
pub struct SubEnvironment {
    parent: Box<dyn Environment>,
    binding: Binding,
}

impl SubEnvironment {
    pub fn new(parent: Box<dyn Environment>, binding: Binding) -> Self {
        Self { parent, binding }
    }
}

impl Environment for SubEnvironment {
    fn visit<F>(&self, mut consumer: F)
    where
        F: FnMut(&Binding),
    {
        consumer(&self.binding);
        self.parent.visit(consumer);
    }

    fn get_top(&self, name: &str) -> Option<&Binding> {
        if self.binding.id.name == name {
            Some(&self.binding)
        } else {
            self.parent.get_top(name)
        }
    }

    fn get_opt(&self, name: &str) -> Option<&Binding> {
        let mut found_bindings = Vec::new();
        self.visit(|binding| {
            if binding.id.name == name {
                found_bindings.push(binding);
            }
            if let Some(ref overload_id) = binding.overload_id {
                if overload_id.name == name {
                    found_bindings.push(binding);
                }
            }
        });
        found_bindings.first().copied()
    }

    fn get_opt_by_id(&self, id: &NamedPat) -> Option<&Binding> {
        if &self.binding.id == id {
            Some(&self.binding)
        } else {
            self.parent.get_opt_by_id(id)
        }
    }

    fn get_opt2(&self, id: &NamedPat) -> Option<&Binding> {
        self.get_opt_by_id(id)
    }

    fn collect<F>(&self, id: &NamedPat, mut consumer: F)
    where
        F: FnMut(&Binding),
    {
        if &self.binding.id == id {
            consumer(&self.binding);
        }
        self.parent.collect(id, consumer);
    }

    fn bind(&self, id: IdPat, value: Value) -> Box<dyn Environment> {
        let named_pat = NamedPat::new(id.name, id.ordinal);
        let binding = Binding::new(named_pat, BindingKind::Val, value);
        Box::new(SubEnvironment::new(Box::new(EmptyEnvironment), binding))
    }

    fn bind_all(&self, bindings: &[Binding]) -> Box<dyn Environment> {
        let mut env: Box<dyn Environment> = Box::new(SubEnvironment::new(
            self.parent.bind_all(&[]),
            self.binding.clone(),
        ));
        for binding in bindings.iter().rev() {
            env = Box::new(SubEnvironment::new(env, binding.clone()));
        }
        env
    }

    fn has_overloaded(&self, name: &str) -> bool {
        let mut bindings = Vec::new();
        self.visit(|binding| {
            if let Some(ref overload_id) = binding.overload_id {
                if overload_id.name == name {
                    bindings.push(binding);
                }
            }
        });
        !bindings.is_empty() && bindings.first().map_or(false, |b| b.is_inst())
    }

    fn get_overloads(&self, id: &IdPat) -> Vec<IdPat> {
        let mut overloads = Vec::new();
        self.visit(|binding| {
            if let Some(ref overload_id) = binding.overload_id {
                if overload_id.name == id.name && overload_id.ordinal == id.ordinal {
                    overloads.push(IdPat::new(binding.id.name.clone(), 0)); // Assuming ordinal 0 for IdPat
                }
            }
        });
        overloads
    }

    fn get_value_map(&self, skip_overloads: bool) -> HashMap<String, Binding> {
        let mut value_map = HashMap::new();
        self.visit(|binding| {
            if skip_overloads && binding.kind == BindingKind::Inst {
                return;
            }
            value_map.entry(binding.id.name.clone()).or_insert_with(|| binding.clone());
        });
        value_map
    }
}

/// Creates an empty environment.
pub fn empty() -> Box<dyn Environment> {
    Box::new(EmptyEnvironment)
}