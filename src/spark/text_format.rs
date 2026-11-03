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

//! A plan in protobuf's text format, as morel-java prints it.
//!
//! morel-java prints a plan with protobuf-java's `TextFormat` printer,
//! and the text is part of the contract between the ports, so this
//! printer writes what that one writes, byte for byte: fields in the
//! order of their numbers, a field with explicit presence whenever it
//! is set and any other only when it is not its default, two spaces of
//! indent per level, enums by name, and strings with every byte that
//! is not printable ASCII escaped in octal.
//!
//! It is written by hand, for the messages the translator builds,
//! rather than by reflection over every message, because those are all
//! a plan holds. One difference from protobuf's text is morel-java's
//! own: a `LocalRelation` shows the number of rows it carries, `data:
//! [2 rows]`, rather than the Arrow bytes that carry them, which are
//! neither readable nor stable.

use crate::spark::proto::expression::literal::LiteralType;
use crate::spark::proto::expression::{
    self as expr, ExprType, Literal, SortOrder,
};
use crate::spark::proto::plan::OpType;
use crate::spark::proto::read::ReadType;
use crate::spark::proto::relation::RelType;
use crate::spark::proto::{
    DataType, Expression, Plan, Relation, RelationCommon, aggregate, data_type,
    join, set_operation, subquery_expression,
};
use std::fmt::Write;

/// Prints a plan; `row_counts` are the number of rows of each local
/// relation, in the order the text meets them.
pub fn plan_text(plan: &Plan, row_counts: &[usize]) -> String {
    let mut p = Printer {
        b: String::new(),
        indent: 0,
        row_counts,
        next_count: 0,
    };
    match &plan.op_type {
        Some(OpType::Root(root)) => p.message("root", |p| p.relation(root)),
        Some(OpType::Command(_)) | None => {}
    }
    // The printer ends each field with a newline; a plan's text is a
    // tree, not a line.
    if p.b.ends_with('\n') {
        p.b.pop();
    }
    p.b
}

struct Printer<'a> {
    b: String,
    indent: usize,
    row_counts: &'a [usize],
    next_count: usize,
}

impl Printer<'_> {
    fn pad(&mut self) {
        for _ in 0..self.indent {
            self.b.push_str("  ");
        }
    }

    fn message(&mut self, name: &str, body: impl FnOnce(&mut Self)) {
        self.pad();
        self.b.push_str(name);
        self.b.push_str(" {\n");
        self.indent += 1;
        body(self);
        self.indent -= 1;
        self.pad();
        self.b.push_str("}\n");
    }

    fn scalar(&mut self, name: &str, value: &str) {
        self.pad();
        let _ = writeln!(self.b, "{}: {}", name, value);
    }

    fn string(&mut self, name: &str, value: &str) {
        let quoted = quote(value);
        self.scalar(name, &quoted);
    }

    /// A string without explicit presence: printed unless empty.
    fn string_nonempty(&mut self, name: &str, value: &str) {
        if !value.is_empty() {
            self.string(name, value);
        }
    }

    fn bool(&mut self, name: &str, value: bool) {
        self.scalar(name, if value { "true" } else { "false" });
    }

    fn opt_bool(&mut self, name: &str, value: Option<bool>) {
        if let Some(v) = value {
            self.bool(name, v);
        }
    }

    fn int(&mut self, name: &str, value: i64) {
        self.scalar(name, &value.to_string());
    }

    fn enum_(&mut self, name: &str, value: i32, label: Option<&str>) {
        if value != 0 {
            match label {
                Some(l) => self.scalar(name, l),
                None => self.int(name, value as i64),
            }
        }
    }

    fn opt_relation(&mut self, name: &str, r: &Option<Box<Relation>>) {
        if let Some(r) = r {
            self.message(name, |p| p.relation(r));
        }
    }

    fn opt_expression(&mut self, name: &str, e: &Option<Expression>) {
        if let Some(e) = e {
            self.message(name, |p| p.expression(e));
        }
    }

    fn opt_box_expression(&mut self, name: &str, e: &Option<Box<Expression>>) {
        if let Some(e) = e {
            self.message(name, |p| p.expression(e));
        }
    }

    fn expressions(&mut self, name: &str, es: &[Expression]) {
        for e in es {
            self.message(name, |p| p.expression(e));
        }
    }

    fn common(&mut self, c: &RelationCommon) {
        #[allow(deprecated)]
        self.string_nonempty("source_info", &c.source_info);
        if let Some(id) = c.plan_id {
            self.int("plan_id", id);
        }
    }

    fn relation(&mut self, r: &Relation) {
        if let Some(c) = &r.common {
            self.message("common", |p| p.common(c));
        }
        let Some(rel_type) = &r.rel_type else {
            return;
        };
        match rel_type {
            RelType::Read(read) => self.message("read", |p| {
                if let Some(ReadType::NamedTable(t)) = &read.read_type {
                    p.message("named_table", |p| {
                        p.string_nonempty(
                            "unparsed_identifier",
                            &t.unparsed_identifier,
                        );
                    });
                }
                if read.is_streaming {
                    p.bool("is_streaming", true);
                }
            }),
            RelType::Project(project) => self.message("project", |p| {
                p.opt_relation("input", &project.input);
                p.expressions("expressions", &project.expressions);
            }),
            RelType::Filter(filter) => self.message("filter", |p| {
                p.opt_relation("input", &filter.input);
                p.opt_expression("condition", &filter.condition);
            }),
            RelType::Join(j) => self.message("join", |p| {
                p.opt_relation("left", &j.left);
                p.opt_relation("right", &j.right);
                p.opt_expression("join_condition", &j.join_condition);
                let label = join::JoinType::try_from(j.join_type)
                    .ok()
                    .map(|t| t.as_str_name());
                p.enum_("join_type", j.join_type, label);
            }),
            RelType::SetOp(s) => self.message("set_op", |p| {
                p.opt_relation("left_input", &s.left_input);
                p.opt_relation("right_input", &s.right_input);
                let label = set_operation::SetOpType::try_from(s.set_op_type)
                    .ok()
                    .map(|t| t.as_str_name());
                p.enum_("set_op_type", s.set_op_type, label);
                p.opt_bool("is_all", s.is_all);
                p.opt_bool("by_name", s.by_name);
                p.opt_bool("allow_missing_columns", s.allow_missing_columns);
            }),
            RelType::Sort(s) => self.message("sort", |p| {
                p.opt_relation("input", &s.input);
                for o in &s.order {
                    p.message("order", |p| p.sort_order(o));
                }
                p.opt_bool("is_global", s.is_global);
            }),
            RelType::Limit(l) => self.message("limit", |p| {
                p.opt_relation("input", &l.input);
                if l.limit != 0 {
                    p.int("limit", l.limit as i64);
                }
            }),
            RelType::Offset(o) => self.message("offset", |p| {
                p.opt_relation("input", &o.input);
                if o.offset != 0 {
                    p.int("offset", o.offset as i64);
                }
            }),
            RelType::Aggregate(a) => self.message("aggregate", |p| {
                p.opt_relation("input", &a.input);
                let label = aggregate::GroupType::try_from(a.group_type)
                    .ok()
                    .map(|t| t.as_str_name());
                p.enum_("group_type", a.group_type, label);
                p.expressions("grouping_expressions", &a.grouping_expressions);
                p.expressions(
                    "aggregate_expressions",
                    &a.aggregate_expressions,
                );
            }),
            RelType::LocalRelation(l) => self.message("local_relation", |p| {
                if l.data.is_some() {
                    let rows = p.row_counts.get(p.next_count).copied();
                    p.next_count += 1;
                    let rows = rows.unwrap_or(0);
                    let text = format!(
                        "[{} {}]",
                        rows,
                        if rows == 1 { "row" } else { "rows" }
                    );
                    p.scalar("data", &text);
                }
                if let Some(schema) = &l.schema {
                    p.string("schema", schema);
                }
            }),
            RelType::Deduplicate(d) => self.message("deduplicate", |p| {
                p.opt_relation("input", &d.input);
                for c in &d.column_names {
                    p.string("column_names", c);
                }
                p.opt_bool("all_columns_as_keys", d.all_columns_as_keys);
                p.opt_bool("within_watermark", d.within_watermark);
            }),
            RelType::SubqueryAlias(s) => self.message("subquery_alias", |p| {
                p.opt_relation("input", &s.input);
                p.string_nonempty("alias", &s.alias);
                for q in &s.qualifier {
                    p.string("qualifier", q);
                }
            }),
            RelType::WithRelations(w) => self.message("with_relations", |p| {
                p.opt_relation("root", &w.root);
                for r in &w.references {
                    p.message("references", |p| p.relation(r));
                }
            }),
            // The translator builds nothing else.
            _ => {}
        }
    }

    fn sort_order(&mut self, o: &SortOrder) {
        self.opt_box_expression("child", &o.child);
        let label = expr::sort_order::SortDirection::try_from(o.direction)
            .ok()
            .map(|t| t.as_str_name());
        self.enum_("direction", o.direction, label);
        let label = expr::sort_order::NullOrdering::try_from(o.null_ordering)
            .ok()
            .map(|t| t.as_str_name());
        self.enum_("null_ordering", o.null_ordering, label);
    }

    fn expression(&mut self, e: &Expression) {
        let Some(t) = &e.expr_type else {
            return;
        };
        match t {
            ExprType::Literal(l) => self.message("literal", |p| p.literal(l)),
            ExprType::UnresolvedAttribute(a) => {
                self.message("unresolved_attribute", |p| {
                    p.string_nonempty(
                        "unparsed_identifier",
                        &a.unparsed_identifier,
                    );
                    if let Some(id) = a.plan_id {
                        p.int("plan_id", id);
                    }
                    p.opt_bool("is_metadata_column", a.is_metadata_column);
                })
            }
            ExprType::UnresolvedFunction(f) => {
                self.message("unresolved_function", |p| {
                    p.string_nonempty("function_name", &f.function_name);
                    p.expressions("arguments", &f.arguments);
                    if f.is_distinct {
                        p.bool("is_distinct", true);
                    }
                    if f.is_user_defined_function {
                        p.bool("is_user_defined_function", true);
                    }
                    p.opt_bool("is_internal", f.is_internal);
                })
            }
            ExprType::ExpressionString(s) => {
                self.message("expression_string", |p| {
                    p.string_nonempty("expression", &s.expression);
                })
            }
            ExprType::Alias(a) => self.message("alias", |p| {
                p.opt_box_expression("expr", &a.expr);
                for n in &a.name {
                    p.string("name", n);
                }
                if let Some(m) = &a.metadata {
                    p.string("metadata", m);
                }
            }),
            ExprType::SortOrder(o) => {
                self.message("sort_order", |p| p.sort_order(o))
            }
            ExprType::SubqueryExpression(s) => {
                self.message("subquery_expression", |p| {
                    if s.plan_id != 0 {
                        p.int("plan_id", s.plan_id);
                    }
                    let label = subquery_expression::SubqueryType::try_from(
                        s.subquery_type,
                    )
                    .ok()
                    .map(|t| t.as_str_name());
                    p.enum_("subquery_type", s.subquery_type, label);
                })
            }
            // The translator builds nothing else.
            _ => {}
        }
    }

    fn literal(&mut self, l: &Literal) {
        let Some(t) = &l.literal_type else {
            return;
        };
        match t {
            LiteralType::Null(d) => self.message("null", |p| p.data_type(d)),
            LiteralType::Boolean(b) => self.bool("boolean", *b),
            LiteralType::Integer(i) => self.int("integer", *i as i64),
            LiteralType::Long(i) => self.int("long", *i),
            LiteralType::Double(d) => self.scalar("double", &java_double(*d)),
            LiteralType::Float(f) => self.scalar("float", &java_float(*f)),
            LiteralType::Decimal(d) => self.message("decimal", |p| {
                p.string_nonempty("value", &d.value);
                if let Some(precision) = d.precision {
                    p.int("precision", precision as i64);
                }
                if let Some(scale) = d.scale {
                    p.int("scale", scale as i64);
                }
            }),
            LiteralType::String(s) => self.string("string", s),
            // The translator builds nothing else.
            _ => {}
        }
    }

    fn data_type(&mut self, d: &DataType) {
        if let Some(data_type::Kind::Null(n)) = &d.kind {
            self.message("null", |p| {
                if n.type_variation_reference != 0 {
                    p.int(
                        "type_variation_reference",
                        n.type_variation_reference as i64,
                    );
                }
            });
        }
    }
}

/// Quotes a string as protobuf's text format does: in double quotes,
/// with the C escapes, and every byte of its UTF-8 that is not
/// printable ASCII in octal.
fn quote(s: &str) -> String {
    let mut b = String::from("\"");
    for &c in s.as_bytes() {
        match c {
            0x07 => b.push_str("\\a"),
            0x08 => b.push_str("\\b"),
            0x0c => b.push_str("\\f"),
            b'\n' => b.push_str("\\n"),
            b'\r' => b.push_str("\\r"),
            b'\t' => b.push_str("\\t"),
            0x0b => b.push_str("\\v"),
            b'\\' => b.push_str("\\\\"),
            b'\'' => b.push_str("\\'"),
            b'"' => b.push_str("\\\""),
            0x20..=0x7e => b.push(c as char),
            _ => {
                let _ = write!(b, "\\{:03o}", c);
            }
        }
    }
    b.push('"');
    b
}

/// Formats a `double` as Java's `Double.toString` does.
pub fn java_double(d: f64) -> String {
    if d.is_nan() {
        return "NaN".to_string();
    }
    if d.is_infinite() {
        return if d > 0.0 { "Infinity" } else { "-Infinity" }.to_string();
    }
    java_format(&format!("{:e}", d))
}

/// Formats a `float` as Java's `Float.toString` does.
pub fn java_float(f: f32) -> String {
    if f.is_nan() {
        return "NaN".to_string();
    }
    if f.is_infinite() {
        return if f > 0.0 { "Infinity" } else { "-Infinity" }.to_string();
    }
    java_format(&format!("{:e}", f))
}

/// Writes a number, given as the shortest digits that identify it in
/// scientific notation, `-1.25e-3`, in Java's style: plain if its
/// magnitude is at least 10^-3 and less than 10^7, with at least one
/// digit after the point; otherwise `d.dddE-n`.
fn java_format(sci: &str) -> String {
    let (mantissa, exp) = sci.split_once('e').expect("scientific");
    let exp: i32 = exp.parse().expect("exponent");
    let (neg, mantissa) = match mantissa.strip_prefix('-') {
        Some(m) => (true, m),
        None => (false, mantissa),
    };
    let digits: String = mantissa.chars().filter(|c| *c != '.').collect();
    let mut b = String::new();
    if neg {
        b.push('-');
    }
    if digits.chars().all(|c| c == '0') {
        b.push_str("0.0");
        return b;
    }
    if (-3..7).contains(&exp) {
        if exp < 0 {
            b.push_str("0.");
            for _ in 0..(-exp - 1) {
                b.push('0');
            }
            b.push_str(&digits);
        } else {
            let point = exp as usize + 1;
            if digits.len() <= point {
                b.push_str(&digits);
                for _ in digits.len()..point {
                    b.push('0');
                }
                b.push_str(".0");
            } else {
                b.push_str(&digits[..point]);
                b.push('.');
                b.push_str(&digits[point..]);
            }
        }
    } else {
        b.push_str(&digits[..1]);
        b.push('.');
        if digits.len() > 1 {
            b.push_str(&digits[1..]);
        } else {
            b.push('0');
        }
        let _ = write!(b, "E{}", exp);
    }
    b
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_java_double() {
        assert_eq!(java_double(2.0), "2.0");
        assert_eq!(java_double(1.5), "1.5");
        assert_eq!(java_double(-0.25), "-0.25");
        assert_eq!(java_double(0.001), "0.001");
        assert_eq!(java_double(0.0001), "1.0E-4");
        assert_eq!(java_double(1.0e7), "1.0E7");
        assert_eq!(java_double(1234567.0), "1234567.0");
        assert_eq!(java_double(1.1f32 as f64), "1.100000023841858");
        assert_eq!(java_float(1.1), "1.1");
        assert_eq!(java_float(2.5e10), "2.5E10");
        assert_eq!(java_double(0.0), "0.0");
    }

    #[test]
    fn test_quote() {
        assert_eq!(quote("a'b\"c\\"), "\"a\\'b\\\"c\\\\\"");
        assert_eq!(quote("é"), "\"\\303\\251\"");
    }
}

// End text_format.rs
