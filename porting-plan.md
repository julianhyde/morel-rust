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

# Morel Rust porting plan

This document tracks which features from morel-java (morel.0) have been ported
to morel-rust (morel-rust.0), and the plan for porting remaining features.

The goal is for each Java commit or issue to correspond to roughly one Rust
commit, with tests ported alongside the feature.

## High-water marks

These are the repository HEAD commits at the time this plan was last updated.
When you update the plan, record the new HEADs here so future readers know
which commits the "Done" table covers and which Java features had landed.

| Repo | Branch | Commit | Date |
|------|--------|--------|------|
| morel-rust (morel-rust.0) | `main` | `e20ae30` | 2026-03-26 |
| morel-java (morel.0) | `main` | `9ee0581b` | 2026-03-25 |

The morel-java `main` HEAD (`9ee0581b`) corresponds to the release after
**0.8.0** (2025-11-23). The most recent release included in the plan is 0.8.0;
any Java commits after `9ee0581b` are not yet reflected here.

Branch `0008-query` has been merged into `main` via cherry-pick (commits
`3d0acec`–`334a656`). Items A0a and A0b below are now done.

## How to read this table

* **Seq** — Suggested sequence for TODO items. Blank = already done.
* **Java issue** — GitHub issue number in morel-java.
* **Description** — What the feature does.
* **Rust ref** — For done items: short commit hash or Rust PR#. For
  in-progress items: branch name. For TODO items: blank.
* **Notes** — Architectural notes, dependencies, or test script to port.

## Keeping this plan up to date

When you add a feature to morel-rust:

1. Move its row from the **TODO** table to the **Done** table.
2. Fill in the **Rust ref** column with the short commit hash or PR number.
3. Update the **High-water marks** table with the new morel-rust HEAD.

When new features land in morel-java:

1. Check `git log <old-java-hwm>..HEAD` in morel.0 for new issues.
2. Add rows to the appropriate TODO phase.
3. Update the morel-java high-water mark.

## Architectural differences (Rust vs Java)

Before diving into the table, these are the key structural differences between
the two implementations that affect the porting strategy:

| Concern | Java | Rust | Impact |
|---------|------|------|--------|
| Evaluation model | `EvalEnv` chain → `Stack` (#349) | `Frame`-based slots | Query steps that reference row position (ordinal, current) need frame support |
| Query execution | Calcite `RowSink` pipeline | `QueryStep` enum (JoinIn/Where/Yield only so far) | Most query steps need compiler + eval work |
| Operator overloading | Type constraint solver (#237) | Parsed (`over`, `inst`), not yet resolved | Large piece of work before `over`-based aggregation works end-to-end |
| Type aliases | Fully implemented (#285) | Parsed (`DeclKind::Type`), not yet evaluated | Needed before many test scripts pass |
| Predicate inversion | Full solver, unbounded variables (#202, #217) | Not started | Requires a new analysis pass |
| Datalog | Separate module (#323) | Not started | Largest remaining feature |
| Foreign / JDBC | Full Calcite integration | Not started | Low priority; Rust targets in-memory data |
| Test scripts | `.smli` with embedded expected output | `.smli` with same format | Port tests alongside each feature |

---

## TODO: Planned tasks

### Phase A0 — Merge / land 0008-query branch work

These items exist on branch `0008-query` but have not yet been merged to
`main`. Merge or cherry-pick them first; then the Phase A items follow.

| Seq | Java issue | Description | Rust ref | Notes |
|-----|------------|-------------|----------|-------|
| ~~A0a~~ | #273, #288 | Type inference for query steps: `group`, `compute`, `elements`, `exists`, `forall`, `distinct`, `order`, `skip`, `take` | `334a656` | Cherry-picked to main; fixup `915856d` |
| ~~A0b~~ | — | Warning infrastructure | `d0d9eb4` | Cherry-picked to main |

### Phase A — Complete query execution (current branch: 0008-query)

The parser and type-resolver handle most query steps; the compiler and
evaluator currently only handle `JoinIn`, `Where`, and `Yield`. This phase
finishes the rest.

| Seq | Java issue | Description | Notes |
|-----|------------|-------------|-------|
| ~~A1~~ | #288, #304 | `group`/`compute`/`elements` execution | `over` syntax requires C1 (operator overloading). |
| A2 | (0.4+) | `distinct`, `order`, `skip`, `take` execution | Type inference already done. |
| A3 | #253 | Set operators (`union`, `intersect`, `except`) as pipeline steps | Parsed. Port tests from `relational.smli`. |
| A4 | #265, #276, #277 | `current` keyword, `ordinal` expression, `unorder` step | Parsed and type-inferred. Needs frame/row-index support. |
| A5 | #321 | `intersect`/`except` should count occurrences and preserve order | Bug fix on top of A3. |
| A6 | #287 | Degenerate joins (singleton scan with `=`) | Requires resolver fix. |
| A7 | #171 | `through` clause in queries (already have `into`) | Parsed. Needs compiler/eval. |

### Phase B — Core language features

| Seq | Java issue | Description | Notes |
|-----|------------|-------------|-------|
| B1 | #230 | Multi-arm `fn` expressions (`fn p1 => e1 \| p2 => e2`) | AST already has `Fn(Vec<Match>)`. Needs compiler/eval path. |
| B2 | #285 | Type aliases (`type t = ...`) | Parsed (`DeclKind::Type`). Needs resolver and evaluator. Port `type-alias.smli`. |
| B3 | #249 | `with` operator for records (`{r with f = v}`) | `Record(Some(base), fields)` in AST. Needs compiler/eval. |
| B4 | #291 | `typeof` operator | Not yet in AST; add parse + type-inference + eval. |
| B5 | #306 | Nested block comments (`(* (* ... *) *)`) | Parser-only change. |
| B6 | #289 | Quoted type names (backtick-quoted identifiers in types) | Parser + type system. |
| B7 | #247 | Expressions with type annotations should translate correctly | Bug fix in resolver. |
| B8 | #343 | Shared type-variable scope within declarations | Type-resolver change; affects polymorphic signatures. |

### Phase C — Operator overloading

Operator overloading (`over`/`inst`) is the largest unimplemented language
feature. It requires a type-constraint solver that allows the same operator
symbol to resolve to different implementations based on type.

| Seq | Java issue | Description | Notes |
|-----|------------|-------------|-------|
| C1 | — | **Research**: study Java's `TypeUnifier` constraint solver (#237) and design Rust equivalent | Read `TypeResolver.java` and `Unifier.java` in morel-java. |
| C2 | #237 | Operator overloading (`over` / `inst` keywords) | Depends on C1. The AST already has `DeclKind::Over` and `ExprKind::Aggregate`. |
| C3 | #282 | `Descending` datatype and `Relational.compare` for type-based orderings | Depends on C2 (uses overloaded compare). Port `overload.smli`. |
| C4 | #271 | Aggregate functions adapt to collection type (list vs bag) | Depends on C2. |

### Phase D — Shell, tooling, and syntax sugar

| Seq | Java issue | Description | Notes |
|-----|------------|-------------|-------|
| D1 | #297 | Source position in parse exceptions | Parser plumbing; improves error messages. |
| D2 | #259 | Tabular output mode in the shell | Shell-only; format query results as a table. |
| D3 | #332 | Tuple field access via dot syntax (`tuple.1`) | Parser + resolver + eval change. |
| D4 | #346 | Postfix method-call syntax (`x.f arg`, `x.f(a,b).g(c)`) | Parser + resolver. Port `postfix.smli`. |
| D5 | #151 | Tail-call optimization via trampolining | Needs eval refactor. Port `tail-recursion.smli`. Depends on G1/G2. |

### Phase E — New standard-library structures

| Seq | Java issue | Description | Notes |
|-----|------------|-------------|-------|
| E1 | #324 | `variant` datatype and `Variant` structure | Port `variant.smli`. |
| E2 | #278 | `Date` structure | No external dependency needed; use chrono crate. |
| E3 | #351, #352 | `Time` structure; `now` and `timeZone` properties | Depends on E2. |

### Phase F — Advanced query: predicate inversion and unbounded variables

This is a significant analysis/compilation feature. Java added it in stages
across several releases (#202, #217, #341, #347).

| Seq | Java issue | Description | Notes |
|-----|------------|-------------|-------|
| F1 | — | **Research**: study predicate inversion in Java (class `PredicateInverter`) and design Rust equivalent | Read `PredicateInverter.java` and `such-that.smli`. |
| F2 | #202 | Unbounded variables in `from`/`join` (no `in` clause) | Depends on F1. Port `such-that.smli`. |
| F3 | #217 | Invert predicates to resolve unbounded variables | Depends on F2. |
| F4 | #341 | Invert `case` expressions with multiple arms | Depends on F3. |
| F5 | #347 | Predicate inversion should filter by outer-scope variables | Depends on F4. |

### Phase G — Evaluation model and Datalog

| Seq | Java issue | Description | Notes |
|-----|------------|-------------|-------|
| G1 | — | **Research**: compare Java's `Stack`-based eval (#349) with Rust's `Frame`-based eval; decide whether to migrate | Java migrated from `EvalEnv` chain to `Stack` for performance and ordinal support. |
| G2 | #349 | Migrate evaluation to stack-based model (if G1 recommends it) | Would replace `Frame` + `EvalEnv`. Enables `ordinal` to work correctly. |
| G3 | — | **Research**: Datalog architecture in Java and how it interacts with the type system | Read `datalog/` in morel-java; review `datalog.smli`. |
| G4 | #323 | Datalog | Largest new feature. Depends on G3. Port `datalog.smli`. |

---

## Done: Features already ported

| Java issue | Description | Rust ref | Notes |
|------------|-------------|----------|-------|
| — | Parser (full grammar) | `1ae5030` | Pest PEG parser |
| — | Command-line shell (REPL) | PR #2 | |
| — | Type unification | PR #6 | |
| — | Type resolution | PR #7 | |
| — | Evaluate simple expressions | PR #12 | |
| — | Morel in the browser via WebAssembly | PR #13 | |
| #14 (rust) | Type inference for query expressions (basic) | `ac33adc` | |
| #15 (rust) | Execute query expressions (basic scan/where/yield) | `1b562d9` | |
| #241 | `exists`, `forall`, `implies` quantification | `fc2f2be` | Short-circuit eval in PR #25 |
| #171 | `into` clause in queries | `fc2f2be` | `through` still TODO (A7) |
| — | `General` structure | `e3f3c00` | |
| — | `Int` structure | `2e520ba` | Java #228 |
| — | `Bool` structure | `b5ec264` | |
| — | `String` structure | `8fba653` | Java #279 |
| — | `Char` structure | `bf29c07` | Java #264 |
| — | `Real` structure | `d37c6e3` | |
| — | `Math` structure | `78aee5c` | |
| — | `Option` structure | `f5a0dd2` | |
| — | `Order` enum | `93d43bb` | |
| — | `List` structure | `8010a70` | |
| #235 | `Bag` structure and `bag` type | `1a49331` | |
| #295 | `ListPair` structure | `53b815c` | |
| #302 | `Either` structure | `0c816f4` | |
| #301 | `Fn` structure | `fde8eb4` | |
| — | `Vector` structure and `vector` type | `17a42dd` | |
| — | Exceptions | `ea86d11` | |
| — | Closures | `8ea5aed` | |
| — | Pattern matching of `Option` (`SOME`/`NONE`) | `0e4b4f6` | |
| — | Recursive functions | `c1fd023` | |
| — | Record type inference | `1a59ca3` | |
| #311 | `op` keyword (operator sections) | `80efa02` | |
| #315 | Parse `signature` | `fa5936f` | |
| — | Standard-library signatures | `8f6657f` | |
| #310 | Validation mode (`:t` syntax) | `cf7ebcf` | |
| #300 | `-c` / `--command` flag (run `.smli` scripts) | PR #23 | Java uses `--run`; similar intent |
| #319 | `productName`, `productVersion`, `banner` properties | `d99f5d1` | |
| — | `Sys` structure (`plan`, `unset`, `clearEnv`, `showAll`) | `a2cab34` | Java #251, #260 |
| #24 (rust) | `Relational` structure | `d7e601a` | |
| #18 (rust) | Tune `Unifier` (persistent data structures) | `86006ae` | |
| #273, #288 | Type inference for query steps (`group`, `compute`, `elements`, `exists`, `forall`, `distinct`, `order`, `skip`, `take`) | `334a656` | Commits `3d0acec`–`334a656`; fixup `915856d` |
| — | Warning infrastructure | `d0d9eb4` | |
| #288, #304 | `group`/`compute`/`elements` execution | `e20ae30` | `over` syntax needs C1 first |

---

## Test scripts: Java vs Rust

| Script | Java | Rust | Status |
|--------|------|------|--------|
| `bag.smli` | ✓ | ✓ | Partial (query execution incomplete) |
| `blog.smli` | ✓ | ✓ | Partial |
| `built-in.smli` | ✓ | ✓ | Mostly complete |
| `closure.smli` | ✓ | ✓ | Complete |
| `datalog.smli` | ✓ | stub | TODO (G4) |
| `datatype.smli` | ✓ | ✓ | Complete |
| `file.smli` | ✓ | stub | Not planned (no file I/O yet) |
| `fixed-point.smli` | ✓ | ✓ | Complete |
| `foreign.smli` | ✓ | stub | Not planned (no JDBC) |
| `hybrid.smli` | ✓ | stub | Not planned (no Calcite) |
| `idempotent.smli` | ✓ | ✓ | Partial |
| `logic.smli` | ✓ | ✓ | Partial |
| `match.smli` | ✓ | ✓ | Complete |
| `misc.smli` | ✓ | ✓ | Partial |
| `optimize.smli` | ✓ | — | TODO (after query execution) |
| `overload.smli` | ✓ | stub | TODO (C2, C3) |
| `postfix.smli` | ✓ | — | TODO (D4) |
| `pretty.smli` | ✓ | ✓ | Partial |
| `regex-example.smli` | ✓ | ✓ | Partial |
| `relational.smli` | ✓ | ✓ | Partial (needs A1–A7) |
| `scott.smli` | ✓ | stub | Needs query execution + scott DB |
| `signature.smli` | ✓ | ✓ | Complete |
| `simple.smli` | ✓ | ✓ | Complete |
| `such-that.smli` | ✓ | stub | TODO (F2) |
| `tail-recursion.smli` | ✓ | — | TODO (D5) |
| `type-alias.smli` | ✓ | stub | TODO (B2) |
| `type-inference.smli` | ✓ | ✓ | Partial |
| `type.smli` | ✓ | ✓ | Partial |
| `variant.smli` | ✓ | — | TODO (E1) |
| `wordle.smli` | ✓ | ✓ | Complete |
