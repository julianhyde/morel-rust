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

use crate::compile::unifier::Term;
use std::collections::{BTreeMap, HashMap};
use std::fmt::{Display, Formatter};

/// Represents a resolved type in the system.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Primitive(PrimitiveType),
    Function(Box<Type>, Box<Type>),

    /// `Record(progressive, arg_name_types)` represents the type
    /// `{name0: arg0, ... nameN: argN}`. If `progressive`, the
    /// arguments may grow over time.
    Record(bool, BTreeMap<String, Type>),

    /// `List(element_type)` represents the type `element_type list`.
    List(Box<Type>),

    /// `Tuple(args)` represents the type `arg0 * ... * argN`.
    Tuple(Vec<Type>),
    Variable(TypeVariable),
    Named(String),

    /// `Alias(name, type_, args)` represents the declaration
    /// `type name = args type_`; for example,
    /// `type int_pair_list = (int * int) list`.
    Alias(String, Box<Type>, Vec<Type>),
    Data(String, Vec<Type>),

    /// `Forall(type_, parameter_count)` represents the type
    /// `forall tyVars ... type_`, where there are parameter_count
    /// type variables `'a`, `'b`, etc.
    Forall(Box<Type>, usize),

    /// `Multi(types)` represents an overloaded type `type0 or ... typeN`.
    Multi(Vec<Type>),
}

impl Type {
    fn describe(
        &self,
        f: &mut Formatter<'_>,
        left: u8,
        right: u8,
    ) -> std::fmt::Result {
        const TUPLE_LEFT: u8 = 14;
        const TUPLE_RIGHT: u8 = 15;
        const APPLY_LEFT: u8 = 16;
        const APPLY_RIGHT: u8 = 17;

        match self {
            Type::Primitive(p) => f.write_str(p.to_str()),
            Type::Function(arg, ret) => {
                write!(f, "({} -> {})", arg, ret)
            }
            Type::Record(progressive, fields) => {
                f.write_str("{")?;
                for (i, (name, field_type)) in fields.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}: {}", name, field_type)?;
                }
                if *progressive {
                    if fields.is_empty() {
                        write!(f, "...")?;
                    } else {
                        write!(f, ", ...")?;
                    }
                }
                f.write_str("}")
            }
            Type::List(elem_type) => {
                if left > APPLY_RIGHT || right > APPLY_RIGHT {
                    write!(f, "(")?;
                    self.describe(f, 0, 0)?;
                    return write!(f, ")");
                }
                elem_type.describe(f, left, APPLY_RIGHT)?;
                write!(f, " list")
            }
            Type::Tuple(types) => {
                if left > 0 || right > 0 {
                    write!(f, "(")?;
                    self.describe(f, 0, 0)?;
                    return write!(f, ")");
                }
                for (i, type_) in types.iter().enumerate() {
                    if i == 0 {
                        type_.describe(f, left, TUPLE_RIGHT)?;
                    } else if i == types.len() - 1 {
                        f.write_str(" * ")?;
                        type_.describe(f, TUPLE_LEFT, right)?;
                    } else {
                        f.write_str(" * ")?;
                        type_.describe(f, TUPLE_LEFT, TUPLE_LEFT)?;
                    }
                }
                Ok(())
            }
            Type::Variable(var) => f.write_str(var.name().as_str()),
            Type::Named(name) => f.write_str(name),
            Type::Alias(name, _, _) => f.write_str(name),
            _ => todo!(),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.describe(f, 0, 0)
    }
}

/// Primitive types in the ML-like language.
#[derive(Debug, Clone, PartialEq)]
pub enum PrimitiveType {
    Unit,
    Bool,
    Int,
    Real,
    String,
    Char,
}

impl PrimitiveType {
    pub fn to_str(&self) -> &'static str {
        match &self {
            PrimitiveType::Unit => "unit",
            PrimitiveType::Bool => "bool",
            PrimitiveType::Int => "int",
            PrimitiveType::Real => "real",
            PrimitiveType::String => "string",
            PrimitiveType::Char => "char",
        }
    }
}

/// Type variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeVariable {
    pub id: usize,
}

impl TypeVariable {
    /// Creates a type variable with a given ordinal.
    pub(crate) fn new(id: usize) -> Self {
        TypeVariable { id }
    }

    /// Returns the name of this type variable: "'a" for 0, "'b" for 1,
    /// "'z" for 25, "'ba" for 26, "'bb" for 27, etc.
    pub fn name(&self) -> String {
        let mut s = String::new();
        let mut i = self.id;
        loop {
            let c = (b'a' + (i % 26) as u8) as char;
            s.push(c);
            i /= 26;
            if i == 0 {
                break;
            }
        }
        s.push('\'');
        s.chars().rev().collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::compile::types::TypeVariable;

    #[test]
    fn test_type_variable() {
        let a = TypeVariable::new(0);
        let b = TypeVariable::new(1);
        assert_ne!(a, b);

        assert_eq!(a.name(), "'a");
        assert_eq!(b.name(), "'b");
        assert_eq!(TypeVariable::new(25).name(), "'z");
        assert_eq!(TypeVariable::new(26).name(), "'ba");
        assert_eq!(TypeVariable::new(27).name(), "'bb");
    }

    #[test]
    fn test_are_contiguous_integers() {
        use crate::compile::types::are_contiguous_integers;

        fn check(strings: &[&str]) -> bool {
            let owned: Vec<String> =
                strings.iter().map(|s| s.to_string()).collect();
            let refs: Vec<&String> = owned.iter().collect();
            are_contiguous_integers(&refs)
        }

        assert!(check(&[])); // Empty collection
        assert!(check(&["1"])); // Single element
        assert!(check(&["1", "2", "3"])); // Contiguous integers
        assert!(!check(&["1", "3", "4"])); // Missing "2"
        assert!(!check(&["0", "1", "2"])); // Wrong start
        assert!(!check(&["a", "b"])); // Non-numeric
    }
}

/// Returns whether the collection is `["1", "2", ... n]`.
///
/// See also: [ordinal_names].
pub(crate) fn are_contiguous_integers<I, S>(strings: I) -> bool
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    for (i, string) in strings.into_iter().enumerate() {
        let expected = (i + 1).to_string();
        if string.as_ref() != expected {
            return false;
        }
    }
    true
}

/// Returns a list of strings ["1", ..., n].
pub(crate) fn ordinal_names(n: usize) -> Vec<String> {
    let mut v: Vec<String> = Vec::new();
    for i in 0..n {
        v.push((i + 1).to_string());
    }
    v
}

/// Substitution mapping type variables to unifier variables.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum Subst {
    Empty,
    Cons {
        parent: Box<Subst>,
        type_var: TypeVariable,
        variable: Term,
    },
}

impl Subst {
    /// Creates a new substitution by adding a (type_var, variable) mapping.
    pub fn plus(&self, type_var: &TypeVariable, variable: Term) -> Self {
        Subst::Cons {
            parent: Box::new(self.clone()),
            type_var: type_var.clone(),
            variable,
        }
    }

    /// Gets the variable associated with a type variable.
    pub fn get(&self, type_var: &TypeVariable) -> Option<Term> {
        let mut current = self;
        loop {
            match current {
                Subst::Empty => return None,
                Subst::Cons {
                    parent,
                    type_var: current_type_var,
                    variable,
                } => {
                    if current_type_var == type_var {
                        return Some(variable.clone());
                    }
                    current = parent;
                }
            }
        }
    }
}

impl std::fmt::Display for Subst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut map = HashMap::new(); // TODO: deterministic order
        let mut current = self;

        loop {
            match current {
                Subst::Empty => break,
                Subst::Cons {
                    parent,
                    type_var,
                    variable,
                } => {
                    map.entry(type_var.clone()).or_insert(variable.clone());
                    current = parent;
                }
            }
        }

        write!(f, "{:?}", map)
    }
}
