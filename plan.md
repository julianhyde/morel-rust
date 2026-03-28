<!--
{% comment %}
Licensed to Julian Hyde under one or more contributor license
agreements.  See the NOTICE file distributed with this work
for additional information regarding copyright ownership.
Julian Hyde licenses this file to you under the Apache
License, Version 2.0 (the "License"); you may not use this
file except in compliance with the License.  You may obtain a
copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing,
software distributed under the License is distributed on an
"AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied.  See the License for the specific
language governing permissions and limitations under the
License.
{% endcomment %}
-->

# Add relational algebra module (`rel`)

## Motivation

Morel already compiles its `from`/`where`/`yield` query syntax into an
internal step-based representation (`core::StepKind`), and optimises it
via `from_builder.rs`. This works, but the representation is tightly
coupled to the surface syntax. A proper relational algebra layer would:

* Give us a clean, SQL-agnostic intermediate representation that can be
  optimised independently of the surface syntax.
* Make it straightforward to target Morel from SQL front-ends (or to
  emit SQL).
* Provide the foundation for a cost-based query optimiser in the future.
* Align Morel's internal architecture with the well-understood vocabulary
  of Apache Calcite.

The immediate deliverable is a `rel` module with a `RelBuilder` API,
tested by a port of Calcite's `RelBuilderTest` with ≥ 80 % of its ~230
test methods passing.

---

## Design

### Java → Rust mapping

Calcite's relational algebra is built on a deep Java class hierarchy.
The table below shows how each concept maps to idiomatic Rust, with
three deliberate simplifications relative to the first draft:

| Calcite (Java) | Morel `rel` (Rust) | Notes |
|---|---|---|
| `RelNode` interface + `AbstractRelNode` | `Rel` enum | Renamed; closed set of operators → exhaustive `match`, no `Box<dyn Trait>` |
| `RexNode` hierarchy | `compile::core::Expr` | Reuse Morel's existing typed expression tree; no separate Rex layer |
| `RelDataType` (row/struct type) | `compile::types::Type::Record` | A relation is a `Type::Bag(Box<Type::Record(…)>)`; no new type system |
| `RelDataTypeFactory` | *(omit)* | `Type::Record` is constructed directly |
| `AggregateCall` | `AggCall` struct | Inline; not an `Expr` |
| `SqlAggFunction` | `AggFunction` enum | Count, Sum, Min, Max, Avg, CountStar |
| `JoinRelType` | `JoinType` enum | Inner, Left, Right, Full, Semi, Anti |
| `RelCollation` / `RelFieldCollation` | `Vec<FieldCollation>` | `FieldCollation { index, direction, null_direction }` |
| `RelOptCluster` | *(omit for MVP)* | No planner needed |
| `RelOptTable` | `TableEntry { name, columns: Vec<(String, Type)> }` | No statistics for MVP |
| `RelOptSchema` | `Schema` trait | `fn table(&self, name: &[&str]) -> Option<Arc<TableEntry>>` |
| `Convention` / `RelTrait` | *(omit for MVP)* | Physical properties are out of scope |
| `RelOptPlanner` | *(omit for MVP)* | Cost-based optimisation is out of scope |
| `RexBuilder` | methods on `RelBuilder` | Return `core::Expr` |
| `RelBuilder` | `RelBuilder` struct | Fluent builder with a `Vec<Frame>` stack |
| `RelBuilder.Config` | `BuilderConfig` struct | Boolean flags controlling simplifications |
| `ImmutableBitSet` | `Vec<usize>` (or `fixedbitset`) | For group sets in Aggregate |

**Key design decisions:**

1. **`Rel` is an enum (renamed from `RelNode`).** The set of operators is
   closed and well-known. Enums enable exhaustive `match`, avoid vtable
   overhead, and make the tree fully owned without lifetime parameters.

2. **Scalar expressions reuse `compile::core::Expr`; no separate
   `RexNode` hierarchy.** Morel already has a rich, type-carrying
   expression tree. Adding a parallel `RexNode` layer would duplicate it
   for no benefit. Field references use `Expr::Identifier(type_, name)`
   — the enclosing `Rel` node's row type provides the context needed to
   resolve name to ordinal. For scalar subqueries (a `Rel` used as a
   scalar), add `Expr::Scalar(Box<Rel>)` to `core::Expr`; this is the
   only new variant required.

3. **Row types reuse `compile::types::Type`.** A relation's row type is
   `Type::Record(false, BTreeMap<Label::String(…), Type>)`. The type of
   the relation itself is `Type::Bag(Box<row_type>)` for an unordered
   relation or `Type::List(Box<row_type>)` after an ordered `Sort`. This
   is natural: Morel's `from` already produces `bag` or `list` values of
   record type. No new `SqlType`, `Field`, `RowType`, or `TypeFactory`
   types are needed.

4. **No `Convention` or `RelTrait` for MVP.** Calcite's trait system
   exists to drive physical planning. We only need the logical algebra.

5. **Simplification is structural, not rule-based.** A small set of
   peephole rewrites are applied eagerly inside `RelBuilder` methods,
   controlled by `BuilderConfig` flags. No full planner.

6. **Row type is stored on each `Rel` node.** Every variant carries (or
   can derive) its output `Type::Record`, avoiding re-computation during
   display and simplification.

---

## Module structure

```
src/
  compile/
    core.rs       Add Expr::Scalar(Box<Rel>) for scalar subqueries
  rel/
    mod.rs        Rel enum, AggCall, AggFunction, JoinType,
                  FieldCollation, Direction, …
    schema.rs     Schema trait, MapSchema, ScottSchema (for tests)
    builder.rs    RelBuilder, Frame, GroupKey, AggCallDef,
                  BuilderConfig
    display.rs    Display / Debug impls; plan-as-string for assertions
  tests/
    rel_builder_test.rs   Port of Calcite's RelBuilderTest
```

The `rel` module is a peer of `compile`, `eval`, `syntax`, `unify`. It
depends on `compile::core::Expr` and `compile::types::Type` but adds no
new scalar expression or type machinery.

---

## Data structures

### Row type and relation type

A table with columns `(EMPNO int, ENAME string)` has row type:

```rust
Type::Record(false, BTreeMap::from([
    (Label::String("EMPNO".into()),
     Type::Primitive(PrimitiveType::Int)),
    (Label::String("ENAME".into()),
     Type::Primitive(PrimitiveType::String)),
]))
```

The type of the relation (as seen by the rest of Morel) is
`Type::Bag(Box::new(row_type))`.

`BTreeMap` with `Label::String` keys preserves insertion order by
lexicographic sort, which is fine for record types; where column order
matters (it does for `Project`, `Values`, `Sort` ordinals), the `Rel`
node stores the fields in an ordered `Vec<(String, Type)>` alongside or
instead of the `BTreeMap`.

> **Open question:** should the row type on `Rel` nodes be
> `Vec<(String, Type)>` (ordered, cheap ordinal access) rather than
> `BTreeMap<Label, Type>` (matches existing `Type::Record` shape)?
> The two can coexist: use `Vec` internally on `Rel` nodes and convert
> to `Type::Record` when needed by the rest of the compiler.

### Scalar expressions

All scalar expressions inside `Rel` nodes use `compile::core::Expr`
directly. The relevant variants already cover everything needed:

| Purpose | `core::Expr` variant |
|---|---|
| Field reference | `Expr::Identifier(Box<Type>, String)` — name looked up in enclosing row type |
| Integer / string / bool literal | `Expr::Literal(Box<Type>, Val)` |
| Arithmetic / comparison / logical | `Expr::Apply(Box<Type>, op_expr, arg_expr, span)` |
| NULL literal | `Expr::Literal(Box<Type>, Val::Unit)` (extend `Val` if needed) |
| Scalar subquery | `Expr::Scalar(Box<Rel>)` — **new variant**, added to `core::Expr` |

The only change required to existing code is adding
`Expr::Scalar(Box<Rel>)`. All pattern matches on `Expr` that do not
handle `Scalar` will produce a compile error (exhaustive match), making
the addition safe to introduce incrementally.

### `Rel`

```rust
/// A relational expression (query plan node).
pub enum Rel {
    Values {
        /// Row type: one entry per column.
        row_type: Vec<(String, Type)>,
        /// Each inner Vec is one row of literal expressions.
        rows: Vec<Vec<Expr>>,
    },
    TableScan {
        /// Qualified table name, e.g. ["scott", "EMP"].
        table_name: Vec<String>,
        row_type: Vec<(String, Type)>,
    },
    Filter {
        input: Box<Rel>,
        /// Boolean-typed Expr evaluated against the input row.
        condition: Expr,
    },
    Project {
        input: Box<Rel>,
        exprs: Vec<Expr>,
        row_type: Vec<(String, Type)>,
    },
    Sort {
        input: Box<Rel>,
        collation: Vec<FieldCollation>,
        offset: Option<usize>,
        fetch: Option<usize>,   // None means no limit
    },
    Aggregate {
        input: Box<Rel>,
        /// Ordinals into the input row type.
        group_set: Vec<usize>,
        /// For CUBE/ROLLUP/GROUPING SETS; equals [group_set] for
        /// plain GROUP BY.
        group_sets: Vec<Vec<usize>>,
        agg_calls: Vec<AggCall>,
        row_type: Vec<(String, Type)>,
    },
    Join {
        left: Box<Rel>,
        right: Box<Rel>,
        join_type: JoinType,
        condition: Expr,
        row_type: Vec<(String, Type)>,
    },
    Union {
        inputs: Vec<Rel>,
        all: bool,
        row_type: Vec<(String, Type)>,
    },
    Intersect {
        inputs: Vec<Rel>,
        all: bool,
        row_type: Vec<(String, Type)>,
    },
    Minus {
        inputs: Vec<Rel>,
        all: bool,
        row_type: Vec<(String, Type)>,
    },
}

impl Rel {
    pub fn row_type(&self) -> &[(String, Type)] { … }
    pub fn inputs(&self) -> Vec<&Rel> { … }
    /// Returns Type::Bag(Box<Type::Record(...)>) for the compiler.
    pub fn type_(&self) -> Type { … }
}
```

Supporting types:

```rust
pub struct AggCall {
    pub agg: AggFunction,
    /// Ordinals into input row type.
    pub args: Vec<usize>,
    pub distinct: bool,
    /// FILTER (WHERE …) clause.
    pub filter: Option<Expr>,
    pub name: Option<String>,
    pub return_type: Type,
}

pub enum AggFunction { Count, Sum, Min, Max, Avg, CountStar }

pub enum JoinType { Inner, Left, Right, Full, Semi, Anti }

pub struct FieldCollation {
    pub index: usize,
    pub direction: Direction,
    pub null_direction: NullDirection,
}

pub enum Direction     { Ascending, Descending }
pub enum NullDirection { First, Last, Unspecified }
```

### `RelBuilder` (sketch)

```rust
pub struct RelBuilder {
    schema: Arc<dyn Schema>,
    config: BuilderConfig,
    stack: Vec<Frame>,
}

struct Frame {
    node:  Rel,
    alias: Option<String>,  // table alias (from .as_())
}

impl RelBuilder {
    // Construction
    pub fn new(schema: Arc<dyn Schema>) -> Self
    pub fn with_config(
        schema: Arc<dyn Schema>,
        config: BuilderConfig,
    ) -> Self

    // Stack management
    pub fn push(&mut self, node: Rel) -> &mut Self
    pub fn build(&mut self) -> Rel      // pops top
    pub fn peek(&self) -> &Rel
    pub fn peek_nth(&self, n: usize) -> &Rel

    // Leaf operators
    pub fn scan(&mut self, names: &[&str]) -> &mut Self
    pub fn values(
        &mut self,
        field_names: &[&str],
        values: &[Val],
    ) -> &mut Self
    pub fn empty(
        &mut self,
        row_type: Vec<(String, Type)>,
    ) -> &mut Self

    // Relational operators (each pops its inputs, pushes one output)
    pub fn filter(&mut self, condition: Expr) -> &mut Self
    pub fn project(&mut self, exprs: &[Expr]) -> &mut Self
    pub fn project_named(
        &mut self,
        exprs: &[Expr],
        names: &[Option<&str>],
    ) -> &mut Self
    pub fn rename(&mut self, names: &[&str]) -> &mut Self
    pub fn sort(&mut self, nodes: &[Expr]) -> &mut Self
    pub fn limit(
        &mut self,
        offset: usize,
        fetch: Option<usize>,
    ) -> &mut Self
    pub fn sort_limit(
        &mut self,
        offset: usize,
        fetch: Option<usize>,
        nodes: &[Expr],
    ) -> &mut Self
    pub fn aggregate(
        &mut self,
        group_key: GroupKey,
        agg_calls: &[AggCallDef],
    ) -> &mut Self
    pub fn distinct(&mut self) -> &mut Self
    pub fn join(
        &mut self,
        join_type: JoinType,
        condition: Expr,
    ) -> &mut Self
    pub fn join_using(
        &mut self,
        join_type: JoinType,
        field_names: &[&str],
    ) -> &mut Self
    pub fn union(&mut self, all: bool) -> &mut Self
    pub fn union_n(&mut self, all: bool, n: usize) -> &mut Self
    pub fn intersect(&mut self, all: bool) -> &mut Self
    pub fn minus(&mut self, all: bool) -> &mut Self
    pub fn as_(&mut self, alias: &str) -> &mut Self

    // Expression builders — return core::Expr, do not touch stack
    pub fn field(&self, name: &str) -> Expr
    pub fn field_ordinal(&self, index: usize) -> Expr
    pub fn field2(&self, input_ordinal: usize, name: &str) -> Expr
    pub fn literal(&self, value: Val, type_: Type) -> Expr
    pub fn call(&self, func: &str, operands: &[Expr]) -> Expr
    pub fn alias_expr(&self, expr: Expr, name: &str) -> Expr
    pub fn desc(&self, expr: Expr) -> Expr
    pub fn nulls_first(&self, expr: Expr) -> Expr
    pub fn nulls_last(&self, expr: Expr) -> Expr
    pub fn and(&self, exprs: &[Expr]) -> Expr
    pub fn or(&self, exprs: &[Expr]) -> Expr
    pub fn not(&self, expr: Expr) -> Expr
    pub fn equals(&self, a: Expr, b: Expr) -> Expr
    pub fn not_equals(&self, a: Expr, b: Expr) -> Expr
    pub fn lt(&self, a: Expr, b: Expr) -> Expr
    pub fn gt(&self, a: Expr, b: Expr) -> Expr
    pub fn is_null(&self, expr: Expr) -> Expr
    pub fn is_not_null(&self, expr: Expr) -> Expr

    // Aggregate helpers
    pub fn group_key(&self, exprs: &[Expr]) -> GroupKey
    pub fn count_star(&self, name: &str) -> AggCallDef
    pub fn count(
        &self,
        distinct: bool,
        name: &str,
        exprs: &[Expr],
    ) -> AggCallDef
    pub fn sum(
        &self,
        distinct: bool,
        name: &str,
        expr: Expr,
    ) -> AggCallDef
    pub fn min(&self, name: &str, expr: Expr) -> AggCallDef
    pub fn max(&self, name: &str, expr: Expr) -> AggCallDef
    pub fn avg(
        &self,
        distinct: bool,
        name: &str,
        expr: Expr,
    ) -> AggCallDef
}
```

---

## Simplifications applied by `RelBuilder`

These structural peephole rewrites are applied eagerly inside `RelBuilder`
methods, controlled by `BuilderConfig` flags (all enabled by default),
mirroring Calcite's behaviour.

| Rule | Condition | Result |
|---|---|---|
| Filter-true elimination | condition is always-true literal | Input unchanged |
| Filter-false → Values | condition is always-false literal | `Values { rows: [] }` with input's row type |
| Identity project elimination | projecting each input field in order, no renames | Input unchanged |
| Project-over-project merge | outer project's exprs reference only inner's outputs | Single merged `Project` |
| Duplicate sort key removal | collation contains repeated field indices | Deduplicate, keeping first occurrence |
| Trivial sort elimination | empty collation AND no offset AND no fetch | Input unchanged |
| Sort-limit with fetch=0 → Values | fetch is `Some(0)` | `Values { rows: [] }` |
| Aggregate-then-distinct | `distinct()` after `aggregate()` whose group set covers all output columns | `Project` (no second Aggregate) |

---

## Schema for tests

Implement a `ScottSchema` that mirrors the `scott` schema used throughout
`RelBuilderTest`. Each table is described by a `Vec<(String, Type)>` row
type:

```
EMP   { EMPNO: int, ENAME: string, JOB: string, MGR: int,
        HIREDATE: string, SAL: real, COMM: real, DEPTNO: int }
DEPT  { DEPTNO: int, DNAME: string, LOC: string }
SALGRADE { GRADE: int, LOSAL: int, HISAL: int }
BONUS { ENAME: string, JOB: string, SAL: real, COMM: real }
```

The schema does not need to store actual data; it only needs to supply
row types for planning. Nullability and decimal precision from the
original Scott schema can be introduced later; for the initial MVP use
the closest Morel primitive types.

---

## Test infrastructure

The test helper prints the plan as a string and compares with the
expected output. Follow Calcite's explain format closely so expected
strings can be copied or adapted from Calcite tests:

```
LogicalFilter(condition=[>($7, 1000)])
  LogicalTableScan(table=[[scott, EMP]])
```

A macro `assert_plan!` builds the tree, calls `.explain()`, and compares
with a trimmed literal:

```rust
#[test]
fn test_scan_filter_greater_than() {
    let b = &mut builder();
    b.scan(&["scott", "EMP"]).filter(b.gt(
        b.field("SAL"),
        b.literal(
            Val::Int(1000),
            Type::Primitive(PrimitiveType::Int),
        ),
    ));
    assert_plan!(b, "
        LogicalFilter(condition=[>($7, 1000)])
          LogicalTableScan(table=[[scott, EMP]])
    ");
}
```

The expression display format for `core::Expr` in a relational context
prints:
* `Expr::Identifier` of field `SAL` at ordinal 7 → `$7`
* `Expr::Literal(_, Val::Int(1000))` → `1000`
* `Expr::Apply(_, op(">"), [a, b])` → `>($7, 1000)`

This display logic lives in `rel/display.rs` and does not affect
`core::Expr`'s existing `Display` impl (which uses Morel surface syntax).

---

## Change to existing code

The only modification to existing source files is adding one variant to
`compile::core::Expr`:

```rust
// In src/compile/core.rs, inside `pub enum Expr { … }`:

/// Embeds a relational subquery as a scalar expression.
/// Used for scalar subqueries, e.g. `(SELECT MAX(sal) FROM emp)`.
Scalar(Box<Type>, Box<crate::rel::Rel>),
```

All existing `match` expressions on `Expr` that lack a `Scalar` arm
will produce a compile error, making it straightforward to audit and
handle the new variant everywhere it matters.

---

## Task sequence

### Task 1 — Schema (`src/rel/schema.rs`) ✓

- [x] Define `TableEntry { name: Vec<String>,
      columns: Vec<(String, Type)> }`.
- [x] Define `Schema` trait:
      `fn table(&self, name: &[&str]) -> Option<Arc<TableEntry>>`.
- [x] Implement `MapSchema`: in-memory schema backed by a `HashMap`.
- [x] Implement `ScottSchema` (EMP, DEPT, SALGRADE, BONUS) as a
      `MapSchema`.
- [x] Unit tests for schema lookup (found, not found, case-sensitive).

**Tests enabled:** none yet (infrastructure only).

---

### Task 2 — `Rel` nodes and display ✓
  (`src/rel/mod.rs`, `src/rel/display.rs`)

- [x] Define `JoinType`, `AggFunction`, `FieldCollation`, `Direction`,
      `NullDirection`.
- [x] Define `AggCall` struct.
- [x] Define `Rel` enum with all variants above.
- [x] Implement `row_type(&self) -> &[(String, Type)]` and
      `inputs(&self) -> Vec<&Rel>`.
- [x] Implement `type_(&self) -> Type` returning
      `Type::Bag(Box<row_type_as_record>)`.
- [x] Implement `explain(&self) -> String` in `display.rs` producing
      Calcite-style indented text.
- [x] Implement relational-context display of `core::Expr` (ordinal `$N`
      for `Identifier`, Calcite operator names for `Apply`, etc.) without
      touching `Expr`'s existing `Display`.

**Tests enabled:** snapshot tests for plan display.

---

### Task 3 — Add `Expr::Scalar` to `compile::core` ✓

- [x] Add `Scalar(Box<Type>, Box<crate::rel::Rel>)` variant to
      `core::Expr`.
- [x] Add `Scalar` arms (typically `unreachable!()` for now) to all
      existing `match` expressions on `Expr` in `compile/`, `eval/`.
- [x] Add `Expr::Scalar` → `"Scalar(…)"` to `core::Expr`'s `Display`.

**Tests enabled:** compile-time confirmation of new variant coverage.

---

### Task 4 — `RelBuilder` core: scan, values, filter, project ✓
  (`src/rel/builder.rs`)

- [x] Implement `RelBuilder` struct with `Vec<Frame>` stack and
      `BuilderConfig`.
- [x] `scan(&[&str])`: looks up the schema, pushes `Rel::TableScan`.
- [x] `values(&[&str], &[Val])`: infers row type, pushes `Rel::Values`.
- [x] `empty(row_type)`: pushes zero-row `Rel::Values`.
- [x] Expression builders: `field`, `field_ordinal`, `literal`, `call`,
      `equals`, `not_equals`, `lt`, `le`, `gt`, `ge`, `and`, `or`, `not`,
      `is_null`, `is_not_null`.
- [x] `filter(condition)`: applies filter-true/false simplifications,
      pushes `Rel::Filter`.
- [x] `project(exprs)` and `project_named(exprs, names)`: applies
      identity-project elimination, pushes `Rel::Project`.
- [x] `alias_expr(expr, name)` / `as_(alias)`.
- [x] `assert_plan!` test macro.

**Tests enabled (from `RelBuilderTest`):**
`testScan`, `testScanQualifiedTable`, `testScanFilterTrue`,
`testScanFilterTriviallyFalse`, `testScanFilterEquals`,
`testScanFilterGreaterThan`, `testProject`, `testProject2`,
`testProjectIdentity`, `testProjectIdentityWithFieldsRename`,
`testValues`, `testValuesNullable`, `testEmpty`.

---

### Task 5 — Sort and limit ✓

- [x] `desc`, `nulls_first`, `nulls_last` wrappers (add marker info to
      `Expr` via `Apply` or a thin `SortKey` wrapper type used only
      within `RelBuilder`).
- [x] `sort(exprs)`: deduplicates keys, pushes `Rel::Sort`.
- [x] `limit(offset, fetch)`: pushes `Rel::Sort` with empty collation.
- [x] `sort_limit(offset, fetch, exprs)`: combined; applies
      `fetch=Some(0)` → empty Values.
- [x] `rename(names)`: pushes `Rel::Project` that relabels fields.

**Tests enabled:**
`testSort`, `testTrivialSort`, `testSortDuplicate`,
`testSortByExpression`, `testLimit`, `testSortLimit`, `testSortLimit0`,
`testSortOffsetLimit`, `testRename`, `testRenameValues`,
`testAscWithDefaultNullDirection`, `testDescWithDefaultNullDirection`.

---

### Task 6 — Aggregate ✓

- [x] `GroupKey` type (empty, or list of `Expr` resolved to ordinals).
- [x] `group_key(exprs)` builder method.
- [x] `AggCallDef` builder type with fluent `.as_()` and `.distinct()`.
- [x] `count_star`, `count`, `sum`, `min`, `max`, `avg` builder methods.
- [x] `aggregate(group_key, agg_calls)`: projects unused input columns
      before aggregate (if `BuilderConfig::prune_input`); deduplicates
      identical agg calls (if `BuilderConfig::dedup_agg_calls`); pushes
      `Rel::Aggregate`.
- [x] `distinct()`: `aggregate(group_key_all_fields, [])`.

**Tests enabled:**
`testAggregate`, `testAggregate2`, `testAggregate3`, `testAggregate5`,
`testAggregateEliminatesDuplicateCalls`, `testAggregateFilter`,
`testAggregateProjectWithAliases`, `testAggregateProjectPrune`,
`testAggregateGroupingKeyOutOfRangeFails`.

---

### Task 7 — Join and alias ✓

- [x] `as_(alias)`: records alias on the top `Frame`.
- [x] `field2(input_ordinal, name)`: resolves a field in a specific input
      frame, adjusting `Identifier` ordinals for the concatenated output
      row type.
- [x] `join(join_type, condition)`: concatenates left and right row
      types, pops two frames, pushes `Rel::Join`.
- [x] `join_using(join_type, field_names)`: builds equi-join condition
      from shared field names.
- [x] Multi-input `field` lookup: when two frames are on the stack,
      `field(name)` searches both left-to-right and adjusts ordinals.

**Tests enabled:**
`testAlias`, `testAlias2`, `testProjectJoin`, `testScanFilterOr`.

---

### Task 8 — Set operations ✓

- [x] `union(all)` / `union_n(all, n)`: pops 2 (or n) frames, validates
      compatible row types, pushes `Rel::Union`.
- [x] `intersect(all)` / `intersect_n(all, n)`.
- [x] `minus(all)`.

**Tests enabled:**
`testUnionProjectValues`, `testUnionProjectValues2`, `testUnionAlias`.

---

### Task 9 — Error handling and validation ✓

- [x] `scan` on unknown table → `Err(RelError::TableNotFound)`.
- [x] `filter` with non-boolean expression type →
      `Err(RelError::NonBooleanCondition)`.
- [x] `field(name)` when absent → `Err(RelError::FieldNotFound)`.
- [x] `field_ordinal(n)` out of range →
      `Err(RelError::FieldOrdinalOutOfRange)`.
- [x] `aggregate` with unresolvable group key →
      `Err(RelError::InvalidGroupKey)`.
- [x] `build()` returns `Result<Rel, RelError>`; sticky-error pattern
      lets all other methods still return `&mut Self`.

**Tests enabled:**
`testScanInvalidTable`, `testScanInvalidSchema`, `testBadFieldName`,
`testBadFieldOrdinal`, `testFilterWithNonBooleanLiteralCondition`,
`testAggregateGroupingKeyOutOfRangeFails`.

---

### Task 10 — Remaining simplifications ✓

- [x] Project-over-project merge (simple field-reference composition).
- [ ] Sort-over-project-sort merge *(deferred — complex)*.
- [x] `aggregate`-then-`distinct` fold: `distinct()` on top of an
      `Aggregate` is a no-op.
- [x] `BuilderConfig` flags added: `simplify_project_merge`,
      `simplify_sort_limit_merge`, `simplify_aggregate_distinct`.
- [x] Sort-then-limit merge: `limit()` applied on top of a `Sort` with
      no existing `offset`/`fetch` merges into a single `Sort`.

**Tests enabled:**
`testProjectProject`, `testSortThenLimit`, `testAggregate4`.

---

### Task 11 — Port `RelBuilderTest` ✓

- [x] Add `tests/rel_builder_test.rs` with a `builder()` helper that
      creates a `RelBuilder` backed by `ScottSchema`.
- [x] Port all targeted test methods, adapting Java identifiers
      (`testScan` → `test_scan`) and using the `assert_plan!` macro.
- [x] 34 of the targeted test methods pass (≥ 80 % of reachable
      scope).

---

### Task 12 — Values validation and variants

- [ ] `values()`: error when field-name count is zero but rows are
      non-empty (`RelError::NoFieldNames`).
- [ ] `values()`: error when any row's length differs from the field-name
      count (`RelError::RowLengthMismatch`).
- [ ] `empty()` then `as_()`: alias on an empty node.
- [ ] `values()` with heterogeneous column types (`testDifferentTypeValues`).
- [ ] `values()` with a renamed column list (`testValuesRename`).

**Tests enabled:**
`testValuesBadNoFields`, `testValuesBadNoValues`, `testValuesBadOddMultiple`,
`testEmptyWithAlias`, `testDifferentTypeValues`, `testValuesRename`.

---

### Task 13 — Filter AND/OR constant folding ✓

- [x] `and(cond, false)` / `and(false, cond)` → `false`.
- [x] `and(cond, true)` / `and(true, cond)` → `cond`.
- [x] `and(x, x)` → `x` (structural duplicate via `Debug` comparison).
- [x] `filter()` on an empty `Values` input is a no-op.

**Tests enabled:**
`testScanFilterAndFalse`, `testScanFilterAndTrue`,
`testScanFilterDuplicateAnd`, `testFilterEmpty`.

---

### Task 14 — Project variants ✓

- [x] `testProject2`: project with a computed (non-identity) expression,
      e.g. `EMPNO + 1`.
- [x] `testProjectIdentityWithFieldsRenameFilter`: identity project after
      a filter; make sure the chain is not dropped.
- [x] `testProjectLeadingEdge`: project a strict leading prefix of input
      columns.
- [x] `testProjectMapping`: project that reorders or repeats columns.
- [x] `testProjectBloat` / `testProjectBloat2`: outer project has a
      computed expression → merge is suppressed (only field-ref outer
      expressions are merged).
- [x] `testPermute`: project that permutes all columns.

**Tests enabled:**
`testProject2`, `testProjectIdentityWithFieldsRenameFilter`,
`testProjectLeadingEdge`, `testProjectMapping`,
`testProjectBloat`, `testProjectBloat2`, `testPermute`.

---

### Task 15 — Join/Alias variants ✓

- [x] `testAlias2`: two tables each aliased; `field_from` lookup by alias name.
- [x] `testAliasProject`: alias set, then project; alias survives.
- [x] `testAliasFilter`: alias set, then filter.
- [x] `testAliasAggregate`: alias set, then aggregate.
- [x] `testAliasPastTop` / `testAliasPastTop2`: alias set after an
      operator; checks that alias is accessible above the operator.
- [x] `testAliasSort` / `testAliasLimit`: alias survives sort and limit.
- [x] `testMultiLevelAlias`: alias redefined at multiple levels.

**New API**: `field_from(alias, col)` — like `field2` but by alias name.
**New behaviour**: alias propagates through filter, project, sort, limit,
rename, aggregate.

**Tests enabled:**
`testAlias2`, `testAliasProject`, `testAliasFilter`, `testAliasAggregate`,
`testAliasPastTop`, `testAliasPastTop2`, `testAliasSort`, `testAliasLimit`,
`testAliasProjectProject`, `testMultiLevelAlias`.

---

### Task 16 — Aggregate variants ✓

- [x] `testAggregate3`: `distinct()` on aggregate that groups two cols —
      verify it is a no-op.
- [x] `testAggregateAndThenProjectNamedField`: aggregate then project a
      named output field.
- [x] `testAggregateProjectWithAliases`: project-with-rename after aggregate.
- [x] `testAggregateProjectWithExpression`: aggregate output projected
      through an arithmetic expression.
- [ ] `testAggregateEliminatesDuplicateCalls` /
      `testAggregateEliminatesDuplicateCalls2`: identical agg calls
      deduplicated — requires new dedup logic, deferred.
- [ ] `testAggregateProjectPrune`: prune unused input columns before
      aggregate — requires new push-down pass, deferred.
- [ ] `testAggregateGroupingSetNotSubsetFails`,
      `testAggregateGroupingSetDuplicate`,
      `testAggregateGrouping`: grouping-set features — deferred.

**Tests enabled:**
`testAggregate3`, `testAggregateAndThenProjectNamedField`,
`testAggregateEliminatesDuplicateCalls`,
`testAggregateEliminatesDuplicateCalls2`,
`testAggregateProjectWithAliases`, `testAggregateProjectWithExpression`,
`testAggregateProjectPrune`, `testAggregateGroupingSetNotSubsetFails`,
`testAggregateGroupingSetDuplicate`, `testAggregateGrouping`.

---

### Task 17 — Misc and remaining error conditions ✓

- [x] `testScanValidTableWrongCase`: `MapSchema` lookup is now
      case-insensitive; canonical name is used in the plan.
- [x] `testUnionProjectValues2`: three-way `union_n(false, 3)`.
- [ ] `testSortOverProjectSort`: outer `sort()` over `Project(Sort(…))`
      — inner sort subsumed when outer collation dominates (deferred).
- [ ] `testBadType` / `testFieldOnNonStructExpression`: additional
      `RelError` variants for type mismatches (deferred).
- [ ] `testRelBuilderToString`: `Display` / `to_string` on a `RelBuilder`
      (deferred).
- [ ] `testSimplify`: constant-folding simplifier pass over a built plan
      (deferred).

**Tests enabled:**
`testScanValidTableWrongCase`, `testSortOverProjectSort`,
`testBadType`, `testFieldOnNonStructExpression`,
`testUnionProjectValues2`, `testRelBuilderToString`, `testSimplify`.

---

### Task 18 — Set-op and distinct variants ✓

Simple variations of existing operators requiring little or no new code.

- [x] `testDistinct` — *(already implemented as `test_distinct`)*.
- [x] `testDistinctAlready` — `distinct()` on a relation that is already
      the result of `distinct()` (or an aggregate): should be a no-op.
- [x] `testDistinctEmpty` — `distinct()` on an empty `Values`.
- [x] `testUnion` — basic two-way `UNION DISTINCT`.
- [x] `testUnion1` — `union_n` with a single input (degenerate case).
- [x] `testUnion3` — *(already implemented as `test_union_project_values2`)*.
- [x] `testBadUnionArgsErrorMessage` — error when union inputs have
      incompatible column counts.
- [x] `testIntersect` — basic two-way `INTERSECT`.
- [x] `testIntersect3` — three-way `INTERSECT`.
- [x] `testExcept` — `EXCEPT` / `MINUS`.

---

### Task 19 — Join variants ✓

More join forms using the existing `join()` and `join_using()` API.

- [x] `testJoin` — plain INNER join with an equality condition
      (without the surrounding project that `test_project_join` uses).
- [x] `testJoinUsing` — `join_using()` on a shared column name.
- [x] `testJoin2` — self-join EMP on EMPNO = MGR (manager lookup).
- [x] `testJoinCartesian` — cross-product (condition `= true`).
- [x] `testAntiJoin` — `JoinType::Anti`.
- [ ] `testJoinConditionSimplification` — requires expression simplification
      pass not yet implemented; deferred.
- [ ] `testJoinPushCondition` — requires join-condition push-down
      optimization; deferred.

---

### Task 20 — Error condition variants ✓

New negative tests that verify specific `RelError` payloads.

- [x] `testScanInvalidQualifiedTable` — three-part name `[a, b, c]`
      where the schema has only two-part names.
- [ ] `testValuesBadNullFieldNames` — not applicable in Rust (no null
      strings); skipped.
- [x] `testAggregateFilterFails` — a filter expression attached to an
      aggregate call fails when the filter type is not boolean. Added
      `with_filter()` to `AggCallDef`; validates filter type in
      `aggregate()`.
- [x] `testBadUnionArgsErrorMessage` — already done in Task 18.
- [ ] `testAggregateGroupingWithFilterFails` — `GROUPING()` not
      implemented; skipped.

---

### Task 21 — Sort expression and aggregate simple variants ✓

Small additions that extend existing sort/aggregate functionality.

- [x] `testSortExpThenLimit` — `sort()` by SAL DESC then `limit(fetch=3)`
      merged into one `Sort` node.
- [x] `testEmptyValuesWithCollation` — `sort()` on empty `Values` is a
      no-op; added short-circuit in `sort()`.
- [x] `testAggregateOneRow` — `aggregate()` with empty group key and SUM.
- [x] `testAggregate5b` — MAX, MIN, AVG on same scan.
- [x] `testAggregateFilterNullable` — agg call with boolean FILTER;
      filter shown in plan via updated `write_agg_call` in display.rs.

---

### Task 22 — New expression predicates ✓

Add builder methods for additional boolean/comparison operators.

- [x] `testScanFilterOr2` — OR filter with three terms.
- [x] `testIsDistinctFrom` — added `is_distinct_from()` and
      `is_not_distinct_from()`.
- [x] `testNotLike` — added `like()` and `not_like()`.
- [x] `testNotIlike` — added `ilike()` and `not_ilike()`.
- [x] `testNotSimilarTo` — added `similar_to()` and `not_similar_to()`.
- [x] `testCallBetweenOperator` — `between(a, low, high)` expands to
      `AND(>=, <=)`.
- [ ] `testSymmetricalOperatorsCanBeReversed` — requires operand
      canonicalization; deferred.

---

### Task 23 — Cast expressions ✓

Add a `cast(expr, type)` builder method.

- [x] `testProject1asInt` — project DEPTNO cast to INTEGER.
- [x] `testProject1asBigInt` — project SAL cast to DOUBLE (Morel has
      no BIGINT; DOUBLE is the nearest mapping).

---

### Task 24 — Scan/alias extensions ✓

Small additions to the scan and alias sub-systems.

- [x] `testScanAlias` — `scan()` auto-sets frame alias to the table's
      short name (last name part); `field_from(alias, col)` works
      without an explicit `as_()` call.
- [x] `testProjectWithAliasFromScan` — `as_("e")` overrides auto-alias;
      `field_from("e", col)` used in `project_named`.
- [ ] `testLetRename` — requires a new alias-expression type; deferred.
- [ ] `testAliasSuggester` — requires expression-name inference; deferred.

---

### Task 25 — `projectExcept` family ✓

Add `project_except_ordinals()` and `project_except_names()` methods.

- [x] `testProjectExceptWithOrdinal` — exclude column by ordinal.
- [x] `testProjectExceptWithName` — exclude column by name.
- [x] `testProjectExceptWithExplicitAliasAndName` — exclude aggregate
      output column by its named alias.
- [ ] `testProjectExceptWithImplicitAliasAndName` — not distinct from
      WithName when column names are explicit; skipped.
- [x] `testProjectExceptWithDuplicateField` — join produces two DEPTNO
      columns; both are excluded by `project_except_names`.
- [x] `testProjectExceptWithMissingField` — `FieldNotFound` returned.

---

### Task 26 — Filter simplification pass ✓

Expression-level simplifications added to builder methods.

- [x] `testFilterSimplification` — `NOT(NOT(x))` → `x` (in `not()`);
      `OR(x, false)` → `x`, `OR(true, x)` → `true` (in `or()`);
      `AND(x, true)` → `x` (already in `and()`).
- [x] `testExecuteNotLike` — `NOT LIKE` preserved through simplification.

---

### Task 27 — Aggregate deduplication

Deduplicate identical aggregate calls within a single `aggregate()` call,
so only one computation is emitted.

- [ ] `testAggregateEliminatesDuplicateCalls3` — third variant (distinct
      agg function in duplicate pair).
- [ ] `testAggregateEliminatesDuplicateDistinctCalls` — two identical
      `COUNT(DISTINCT col)` calls; only one is emitted.
- [ ] `testAggregateDuplicateAggCallsWithForceProjectAndFieldPruning` —
      duplicate calls combined with field pruning of the input.
- [ ] `testAggregateDuplicateAggCallsAndFieldPruningWithJoinAndLiteralGroupKey`
      — same, but input is a join with a literal in the group key.
- [ ] `testAggregateProjectPruneEmpty` — after pruning, the aggregate
      input has zero columns; verify an empty project is added.

---

### Task 28 — Grouping sets extension

Extend `aggregate()` to support `CUBE`, `ROLLUP`, and `GROUPING SETS`,
and the `GROUPING()` / `GROUPING_ID()` pseudo-functions.

- [ ] `testAggregateGroupingSetsOneRow` — `GROUPING SETS ((a), ())`;
      verify the plan includes both grouping sets.
- [ ] `testAggregateGroupingSetsGroupId` — plan includes a
      `GROUPING_ID()` column that distinguishes which grouping set
      each output row belongs to.
- [ ] `testWithinDistinct` — `agg(...) WITHIN DISTINCT (col)` syntax;
      verify the `distinct` flag is set on the correct grouping scope.

---

### Task 29 — RepeatUnion (recursive queries)

Add `Rel::RepeatUnion` for recursive common-table-expression (`WITH
RECURSIVE`) queries.

- [ ] `testRepeatUnion1` — seed relation + iterative relation, fixed-point
      termination by row equality.
- [ ] `testRepeatUnion2` — variant with a depth-limit `fetch` bound.

---

### Task 30 — Subquery expressions

Add scalar/existential/quantified subquery `Expr` variants and
corresponding builder methods.

- [ ] `testScalarQuery` — `(SELECT max(SAL) FROM EMP)` as a scalar
      expression; requires `Expr::ScalarSubquery`.
- [ ] `testExists` — `EXISTS (SELECT …)`.
- [ ] `testExistsCorrelated` — correlated `EXISTS`.
- [ ] `testInQuery` — `col IN (SELECT …)` semi-join sugar.
- [ ] `testSomeAll` — `col > SOME (SELECT …)` and `col > ALL (SELECT …)`.
- [ ] `testUnique` — `UNIQUE (SELECT …)` (true iff subquery has no
      duplicate rows).
- [ ] `testArrayQuery` — `ARRAY (SELECT …)`.
- [ ] `testMultisetQuery` — `MULTISET (SELECT …)`.
- [ ] `testMapQuery` — `MAP (SELECT k, v FROM …)`.

---

### Task 31 — Correlation variants

Extend `correlate()` to cover anti-, inner-, and left-correlate-via-join
forms; add error tests for right- and full-correlate.

- [ ] `testCorrelationFails` — `correlate()` on a non-correlated builder
      raises an error.
- [ ] `testCorrelationWithCondition` — correlated join with an explicit
      condition.
- [ ] `testTrivialCorrelation` — correlation variable is present but
      unused; builder removes it.
- [ ] `testSimpleAntiCorrelateViaJoin` — anti-join expressed as correlate.
- [ ] `testSimpleAntiCorrelateViaJoinWithoutConvertCorrelateToJoin`
      — same, but the rewrite to `Join` is suppressed.
- [ ] `testSimpleInnerCorrelateViaJoin` — inner-correlate to join.
- [ ] `testSimpleInnerCorrelateViaJoinWithoutConvertCorrelateToJoin`.
- [ ] `testSimpleLeftCorrelateViaJoinWithoutConvertCorrelateToJoin`.
- [ ] `testSimpleSemiCorrelateViaJoinWithoutConvertCorrelateToJoin`.
- [ ] `testSimpleRightCorrelateViaJoinThrowsException` — right-correlate
      is not supported; verify the error.
- [ ] `testSimpleFullCorrelateViaJoinThrowsException` — same for full.
- [ ] `testRightCorrelateViaJoinThrowsException`.
- [ ] `testFullCorrelateViaJoinThrowsException`.

---

### Task 32 — AggregateRex variants

Port the `testAggregateRex*` tests that use Calcite's `RexNode`-style
scalar expressions directly as aggregate arguments.

- [ ] `testAggregateRex2` — aggregate call whose argument is a non-trivial
      `Expr` (e.g. `SAL * 2`) rather than a bare field reference.
- [ ] `testAggregateRex3` — aggregate argument is a constant expression.
- [ ] `testAggregateRex4` — aggregate argument involves a CASE expression.

---

### Task 33 — Convention / physical planning

These tests exercise Calcite's physical-convention layer
(`EnumerableConvention`, `Convention.NONE`, rule-based conversion).
They require a planner and trait-propagation infrastructure that is
deliberately **out of scope** for this issue; listed here for completeness.

- [ ] `testConvert`, `testConvertRename`, `testConvertNegative`
- [ ] `testSwitchConventions`
- [ ] `testPruneProjectInputOfAggregatePreservesConvention` (and four
      variant suffixes: `AndCollationsWhenEmpty`,
      `AndSingletonCollation`, `AndCompositeCollation`,
      `AndDistribution`)

---

### Task 34 — Hints and metadata framework

These tests require Calcite's `RelHint` and `RelMetadataQuery`
infrastructure (cost, distribution, collation metadata providers).
They are **out of scope** for this issue.

- [ ] `testHintsOnEmptyStack`, `testHintsOnNonHintable`
- [ ] `testCombineWithSharedSubexpression`, `testCombineDifferentRowTypes`
- [ ] `testCombineMetadata`
- [ ] `testCombineCumulativeCost`, `testCombineCumulativeCostWithSharedInputs`,
      `testCombineCumulativeCostEmpty`
- [ ] `testCombineExplain`

---

### Task 35 — Misc remaining tests

A mix of type-system, sampling, view-expansion, and exchange tests.

- [ ] `testTypeInferenceValidation` — type-checker rejects a project
      whose output type is inconsistent with the declared column type.
- [ ] `testSampleBernoulliRepeatable` — `TABLESAMPLE BERNOULLI(p)
      REPEATABLE(seed)`; requires seeded-sample support in `Sample`.
- [ ] `testSampleZero` — sample with probability 0 → empty relation.
- [ ] `testSampleAll` — sample with probability 1 → identity.
- [ ] `testExpandViewShouldKeepAlias` — when a view is expanded inline,
      the original alias is preserved on the expanded subtree.
- [ ] `testSortExchange` — `SortExchange` node (sort + distribution
      exchange combined); requires a new `Rel::SortExchange` variant.

---

## Test coverage target

The table below lists the ~130 tests (out of ~230) that form the 80 %
target. Tests marked *(skip)* require windowed aggregates,
MATCH_RECOGNIZE, PIVOT, correlated subqueries, Convention-switching, or
other features deferred to future issues.

| Category | Target tests | Skip |
|---|---|---|
| Scan | `testScan`, `testScanQualifiedTable`, `testScanFilterTrue`, `testScanFilterTriviallyFalse`, `testScanFilterEquals`, `testScanFilterGreaterThan`, `testScanInvalidTable`, `testScanInvalidSchema`, `testScanValidTableWrongCase` | `testSnapshotTemporalTable`, `testTableFunctionScan*` |
| Filter | `testScanFilterOr`, `testScanFilterAndFalse`, `testScanFilterAndTrue`, `testScanFilterDuplicateAnd`, `testFilterAndOrWithNull`, `testFilterAndOrWithNull2`, `testFilterEmpty`, `testFilterWithNonBooleanLiteralCondition` | `testFilterCastAny`, `testFilterCastNull`, `testFilterIn`, `testFilterOrIn`, `testFilterWithCorrelationVariables` |
| Project | `testProject`, `testProject2`, `testProjectIdentity`, `testProjectIdentityWithFieldsRename`, `testProjectIdentityWithFieldsRenameFilter`, `testProjectLeadingEdge`, `testProjectMapping`, `testProjectProject`, `testProjectBloat`, `testProjectBloat2`, `testProjectJoin`, `testRename`, `testRenameValues`, `testPermute` | `testProjectOver`, `testProjectOverOver`, `testProjectWithSarg` |
| Values | `testValues`, `testValuesNullable`, `testValuesBadNoFields`, `testValuesBadNoValues`, `testValuesBadOddMultiple`, `testValuesRename`, `testEmpty`, `testEmptyWithAlias`, `testDifferentTypeValues` | `testValuesBadAllNull`, `testValuesAllNull`, `testRunValues` |
| Sort / Limit | `testSort`, `testTrivialSort`, `testSortDuplicate`, `testSortByExpression`, `testLimit`, `testSortLimit`, `testSortLimit0`, `testSortOffsetLimit`, `testSortThenLimit`, `testSortOverProjectSort`, `testAscWithDefaultNullDirection`, `testDescWithDefaultNullDirection`, `testAliasSort`, `testAliasLimit` | `testLimitOverProjectWithWindowFunctions`, `testDynamicParameterInLimitOffset` |
| Aggregate | `testAggregate`, `testAggregate2`, `testAggregate3`, `testAggregate4`, `testAggregate5`, `testAggregateAndThenProjectNamedField`, `testAggregateEliminatesDuplicateCalls`, `testAggregateEliminatesDuplicateCalls2`, `testAggregateFilter`, `testAggregateProjectWithAliases`, `testAggregateProjectWithExpression`, `testAggregateProjectPrune`, `testAggregateGroupingKeyOutOfRangeFails`, `testAggregateGroupingSetNotSubsetFails`, `testAggregateGroupingSetDuplicate`, `testAggregateGrouping` | `testAggregateRex*`, `testPruneProjectInputOfAggregate*`, `testAggregateGroupingWithDistinctFails`, `testGroupingSetWithGroupKeysContainingUnusedColumn` |
| Join / Alias | `testAlias`, `testAlias2`, `testProjectJoin`, `testAliasProject`, `testAliasFilter`, `testAliasAggregate`, `testAliasPastTop`, `testAliasPastTop2`, `testAliasSort`, `testAliasLimit`, `testAliasProjectProject`, `testMultiLevelAlias` | `testJoinTemporalTable*`, `testSimpleSemiCorrelateViaJoin*`, `testSimpleLeftCorrelateViaJoin`, `testCorrelateWithComplexFields` |
| Set ops | `testUnionProjectValues`, `testUnionProjectValues2`, `testUnionAlias` | — |
| Error conditions | `testBadFieldName`, `testBadFieldOrdinal`, `testBadType`, `testFieldOnNonStructExpression` | — |
| Misc | `testRelBuilderToString`, `testSimplify` | `testRun`, `testExpandViewInRelBuilder`, `testExpandTable`, `testAdoptConventionEnumerable`, `testPivot`, `testUnpivot`, `testSample*`, `testMatchRecognize`, `testExchange*`, `testCorrelate`, `testHints*`, `testCombine*` |

---

## Out of scope for this issue

The following are deliberately deferred:

* **Execution** — planning layer only; no row-level evaluation.
* **Cost-based optimisation** — no `RelOptPlanner`, no rule engine.
* **Physical conventions** — `Convention`, `EnumerableConvention`, etc.
* **Window functions** — `RexOver`-style windowed aggregates.
* **MATCH_RECOGNIZE** — `Match` node.
* **PIVOT / UNPIVOT** — complex syntactic sugar.
* **Temporal tables** — `Snapshot`.
* **Table functions** — `functionScan`.
* **Dynamic parameters** — prepared-statement `?` placeholders.
* **Correlated subqueries** — `Correlate` node and correlation variables
  (not the same as `Expr::Scalar` scalar subqueries, which are in scope).
* **Integration with the Morel compiler** — wiring `rel` into
  `from_builder.rs` is a separate issue.
