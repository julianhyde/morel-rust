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

//! How each Morel operator reaches Spark: the table that
//! `functions.sml` holds as data, read for the translator's use.
//!
//! Port of morel-java's `SparkFunctionTable`. The table is data, in
//! Morel, so that every port shares one copy: this file is morel-java's
//! `functions.sml`, copied. It is read rather than evaluated: every
//! entry is a record of string literals, so the parse tree is the
//! value.

use crate::compile::library::BuiltInFunction;
use crate::syntax::ast::{ExprKind, LiteralKind, StatementKind};
use crate::syntax::parser;
use std::collections::HashMap;
use std::sync::OnceLock;

/// The table, as the file holds it.
const SOURCE: &str = include_str!("functions.sml");

/// How an operator reaches Spark.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Kind {
    /// An aggregate function, applied over a group.
    Aggregate,
    /// Spark has the operator, under the name the entry gives.
    Direct,
    /// The entry gives an expression template, with `{0}` for the
    /// first argument.
    Rewritten,
    /// The operator becomes a subquery.
    Subquery,
    /// Spark cannot do it, so a query that uses it cannot be prepared.
    Unsupported,
}

impl Kind {
    fn parse(s: &str) -> Kind {
        match s {
            "aggregate" => Kind::Aggregate,
            "direct" => Kind::Direct,
            "rewritten" => Kind::Rewritten,
            "subquery" => Kind::Subquery,
            "unsupported" => Kind::Unsupported,
            _ => panic!("functions.sml: unknown kind {}", s),
        }
    }

    /// The kind as morel-java's enum constant names it, `SUBQUERY`.
    pub fn upper(&self) -> &'static str {
        match self {
            Kind::Aggregate => "AGGREGATE",
            Kind::Direct => "DIRECT",
            Kind::Rewritten => "REWRITTEN",
            Kind::Subquery => "SUBQUERY",
            Kind::Unsupported => "UNSUPPORTED",
        }
    }

    /// The kind in lower case, as a message names it.
    pub fn lower(&self) -> String {
        self.upper().to_lowercase()
    }
}

/// One row of the table.
#[derive(Clone, Debug)]
pub struct Entry {
    /// The Morel operator, as the table names it, such as `"op +"`.
    pub morel: String,
    /// How it reaches Spark.
    pub kind: Kind,
    /// Spark's name for it, or the template that replaces it.
    pub spark: String,
}

/// The table.
pub struct FunctionTable {
    entries: HashMap<String, Entry>,
}

impl FunctionTable {
    /// Returns the table, reading it on first use.
    pub fn instance() -> &'static FunctionTable {
        static INSTANCE: OnceLock<FunctionTable> = OnceLock::new();
        INSTANCE.get_or_init(FunctionTable::load)
    }

    fn load() -> FunctionTable {
        let statement = parser::parse_statement(SOURCE)
            .unwrap_or_else(|e| panic!("functions.sml: {}", e));
        let StatementKind::Expr(ExprKind::List(rows)) = statement.kind else {
            panic!("functions.sml: expected a list");
        };
        let mut entries = HashMap::new();
        for row in rows {
            let ExprKind::Record(_, fields, _) = &row.kind else {
                panic!("functions.sml: expected a record");
            };
            let mut values = HashMap::new();
            for field in fields {
                let name = field
                    .label
                    .as_ref()
                    .map(|l| l.name.clone())
                    .expect("functions.sml: field has no label");
                let ExprKind::Literal(literal) = &field.expr.kind else {
                    panic!("functions.sml: expected a string literal");
                };
                let LiteralKind::String(raw) = &literal.kind else {
                    panic!("functions.sml: expected a string literal");
                };
                let value = parser::unquote_string(raw)
                    .unwrap_or_else(|e| panic!("functions.sml: {}", e));
                values.insert(name, value);
            }
            let field = |name: &str| {
                values.get(name).cloned().unwrap_or_else(|| {
                    panic!("functions.sml: entry has no '{}' field", name)
                })
            };
            let entry = Entry {
                morel: field("morel"),
                kind: Kind::parse(&field("kind")),
                spark: field("spark"),
            };
            let key = entry.morel.clone();
            if entries.insert(key.clone(), entry).is_some() {
                panic!("functions.sml: duplicate entry {}", key);
            }
        }
        FunctionTable { entries }
    }

    /// Returns how a built-in reaches Spark, or `None` if the table
    /// does not mention it.
    ///
    /// A row naming the built-in itself wins -- `String.size`, or
    /// `Real./`, which stays distinct from `op div`. Otherwise an
    /// `op X` row covers every type instance of the operator, because
    /// the tree carries the instance that overload resolution chose,
    /// `Int.+` rather than the `+` the program wrote. An internal
    /// operator, such as the `sum$int` that `sum` resolves to, the table
    /// names for the structure it belongs to, `$.sum:int`.
    pub fn get(&self, f: BuiltInFunction) -> Option<&Entry> {
        let name = f.name();
        if let Some(e) = self.entries.get(&f.full_name()) {
            return Some(e);
        }
        if f.parent().is_none()
            && let Some((generic, instance)) = name.split_once('$')
            && !generic.is_empty()
        {
            let key = format!("$.{}:{}", generic, instance);
            if let Some(e) = self.entries.get(&key) {
                return Some(e);
            }
        }
        self.entries.get(&format!("op {}", name))
    }

    /// Returns the built-ins whose names the table does not resolve.
    /// Every name the file writes must be a built-in, so the list is
    /// empty unless the file and the built-ins have drifted apart.
    #[cfg(test)]
    fn unresolved(&self) -> Vec<String> {
        use strum::IntoEnumIterator;
        let mut found: Vec<&str> = Vec::new();
        for f in BuiltInFunction::iter() {
            if let Some(e) = self.get(f) {
                found.push(&e.morel);
            }
        }
        let mut missing: Vec<String> = self
            .entries
            .keys()
            .filter(|k| !found.contains(&k.as_str()))
            .cloned()
            .collect();
        missing.sort();
        missing
    }
}

/// Returns the name of a built-in as morel-java's enum constant writes
/// it, `STRING_SIZE` for `StringSize`, as some messages name it.
pub fn constant_name(f: BuiltInFunction) -> String {
    let debug = format!("{:?}", f);
    let mut s = String::new();
    for (i, c) in debug.chars().enumerate() {
        if c.is_ascii_uppercase() && i > 0 {
            s.push('_');
        }
        s.push(c.to_ascii_uppercase());
    }
    s
}

/// Expands a template, calling `arg` for the text of each argument it
/// uses, in the order it meets them: `{0}` stands for the first
/// argument, and `{{` for a literal brace. An argument the template
/// does not use is never rendered.
pub fn expand<E>(
    template: &str,
    mut arg: impl FnMut(usize) -> Result<String, E>,
) -> Result<String, E> {
    let mut b = String::new();
    let chars: Vec<char> = template.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c != '{' {
            b.push(c);
        } else if chars.get(i + 1) == Some(&'{') {
            b.push('{');
            i += 1;
        } else {
            let close = (i..chars.len())
                .find(|&j| chars[j] == '}')
                .unwrap_or_else(|| {
                    panic!("unclosed placeholder in template [{}]", template)
                });
            let ordinal: String = chars[i + 1..close].iter().collect();
            let ordinal = ordinal.parse::<usize>().unwrap_or_else(|_| {
                panic!(
                    "placeholder [{}] in template [{}] is not an argument \
                     number",
                    ordinal, template
                )
            });
            b.push_str(&arg(ordinal)?);
            i = close;
        }
        i += 1;
    }
    Ok(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_every_name_resolves() {
        // morel-java resolves the `andalso` and `orelse` syntax to
        // internal operators, which the table names `$.andalso` and
        // `$.orelse`; this port resolves them to `Bool.andalso` and
        // `Bool.orelse`, which the table also names, so those two rows
        // have no built-in here.
        let table = FunctionTable::instance();
        assert_eq!(table.unresolved(), vec!["$.andalso", "$.orelse"]);
    }

    #[test]
    fn test_lookup() {
        let table = FunctionTable::instance();
        let spark = |f| table.get(f).map(|e| e.spark.clone());
        assert_eq!(spark(BuiltInFunction::StringSize).unwrap(), "length");
        assert_eq!(spark(BuiltInFunction::IntPlus).unwrap(), "+");
        assert_eq!(spark(BuiltInFunction::RealDivide).unwrap(), "/");
        assert_eq!(spark(BuiltInFunction::RelationalSumInt).unwrap(), "sum");
        assert_eq!(constant_name(BuiltInFunction::StringSize), "STRING_SIZE");
    }

    #[test]
    fn test_expand() {
        let e = expand("f({1}, {0}) {{x}", |i| {
            Ok::<_, ()>(["a", "b"][i].to_string())
        });
        assert_eq!(e.unwrap(), "f(b, a) {x}");
    }
}

// End function_table.rs
