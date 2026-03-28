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

## High-water mark

The morel-java commit surveyed when the TODO tables were last updated.
Features in morel-java after this commit may not yet have TODO rows.

| Repo | Branch | Commit | Date |
|------|--------|--------|------|
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
* **Notes** — Architectural notes, dependencies, test script to port, or
  Java commit reference.

## Commit message convention

The commit message (one-line summary and description) should generally be
based on, or even a copy of, the corresponding morel-java commit message,
adapted as follows:

* Replace a `[MOREL-NNN]` prefix or `(#NNN)` suffix with
  `(hydromatic/morel#NNN)`.
* Remove any `Fixes #NNN` line.
* Keep the `Propagate:` trailer (see below).

For example, a Java commit message:

```
[MOREL-230] Allow lambda (`fn`) to have multiple branches, similar to `case`

Fixes #230
```

becomes the Rust commit message:

```
Allow lambda (`fn`) to have multiple branches, similar to `case`
  (hydromatic/morel#230)

Propagate: hydromatic/morel#230 commit 3c73f2fe
```

## `Propagate:` commit trailer

Every morel-rust commit that ports a feature from morel-java should include
a `Propagate:` trailer in its commit message. The format is:

```
Propagate: hydromatic/morel#NNN commit XXXXXXXX
```

where `NNN` is the GitHub issue number in morel-java and `XXXXXXXX` is the
short hash of the morel-java commit that implemented the feature. The trailer
may be repeated when one Rust commit covers multiple Java issues or commits.

**Why**: the trailer records the cross-repo provenance in the git history
itself, so this plan does not need to store the morel-rust commit hash.
That eliminates the "two-commit dance" (one to implement, one to record the
hash in the plan). To find which Rust commit ported a given Java feature:

```
git log --grep "Propagate: hydromatic/morel#NNN"
```

Entries in the Done table that pre-date this convention (before 2026-03-27)
carry a legacy `(rust: HASH)` note instead.

## Keeping this plan up to date

When you add a feature to morel-rust, do it all in **one commit**:

1. Implement the feature and port the tests.
2. Move the feature's row from the **TODO** table to the **Done** table.
3. Add a `Propagate:` trailer to the commit message (see above).

No second commit is needed to record the Rust commit hash — the `Propagate:`
trailer in the commit message IS the record.

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
| ~~A2~~ | (0.4+) | `distinct`, `order`, `skip`, `take` execution | Already done (in evaluate-mode tests since before A1). |
| ~~A3~~ | #253 | Set operators (`union`, `intersect`, `except`) as pipeline steps | Already done (in evaluate-mode tests since before A1). |
| A4 | #265, #276, #277 | `current` keyword, `ordinal` expression, `unorder` step | Parsed and type-inferred. Needs frame/row-index support. |
| ~~A5~~ | #321 | `intersect`/`except` should count occurrences and preserve order | Already done alongside A3. |
| A6 | #287 | Degenerate joins (singleton scan with `=`) | Requires resolver fix. |
| A7 | #171 | `through` clause in queries (already have `into`) | Parsed. Needs compiler/eval. |

### Phase B — Core language features

| Seq | Java issue | Description | Notes |
|-----|------------|-------------|-------|
| ~~B1~~ | #230 | Multi-arm `fn` expressions (`fn p1 => e1 \| p2 => e2`) | Parser, compiler, and eval all supported `Fn(Vec<Match>)`. Tests in match.smli. |
| B2 | #285 | Type aliases (`type t = ...`) | Parsed (`DeclKind::Type`). Needs resolver and evaluator. Port `type-alias.smli`. |
| ~~B3~~ | #249 | `with` operator for records (`{r with f = v}`) | Evaluate mode. Resolver + type_resolver fix. |
| ~~B4~~ | #291 | `typeof` operator | TypeKind::Expression was parsed; added TypeToTermConverter handler. |
| ~~B5~~ | #306 | Nested block comments (`(* (* ... *) *)`) | Already supported by pest grammar. Fixed grammar bug: `(*)` inside a block comment is now a line comment, matching SML/NJ and morel-java. |
| ~~B6~~ | #289 | Quoted type names (backtick-quoted identifiers in types) | Already works; tested in simple.smli lines 364-369. |
| ~~B7~~ | #247 | Expressions with type annotations should translate correctly | Already works; ExprKind::Annotated passes through in resolver. |
| ~~B8~~ | #343 | Shared type-variable scope within declarations | Done. |

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
| ~~D2~~ | #259 | Tabular output mode in the shell | `output` property: `classic` (default) or `tabular`. |
| ~~D3~~ | #332 | Tuple field access via dot syntax (`tuple.1`) | Parser already handled it; fix was one line in `Code::new_nth` to use `field_types()` instead of `expect_record()`. |
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

Entries marked `(rust: HASH)` pre-date the `Propagate:` trailer convention;
for later entries use `git log --grep "Propagate: hydromatic/morel#NNN"`.

| Java issue | Description | Notes |
|------------|-------------|-------|
| — | Parser (full grammar) | Pest PEG parser (rust: `1ae5030`) |
| — | Command-line shell (REPL) | rust: PR #2 |
| — | Type unification | rust: PR #6 |
| — | Type resolution | rust: PR #7 |
| — | Evaluate simple expressions | rust: PR #12 |
| — | Morel in the browser via WebAssembly | rust: PR #13 |
| #14 (rust) | Type inference for query expressions (basic) | rust: `ac33adc` |
| #15 (rust) | Execute query expressions (basic scan/where/yield) | rust: `1b562d9` |
| #241 | `exists`, `forall`, `implies` quantification | Short-circuit eval in PR #25 (rust: `fc2f2be`) |
| #171 | `into` clause in queries | `through` still TODO (A7) (rust: `fc2f2be`) |
| — | `General` structure | rust: `e3f3c00` |
| — | `Int` structure | Java #228 (rust: `2e520ba`) |
| — | `Bool` structure | rust: `b5ec264` |
| — | `String` structure | Java #279 (rust: `8fba653`) |
| — | `Char` structure | Java #264 (rust: `bf29c07`) |
| — | `Real` structure | rust: `d37c6e3` |
| — | `Math` structure | rust: `78aee5c` |
| — | `Option` structure | rust: `f5a0dd2` |
| — | `Order` enum | rust: `93d43bb` |
| — | `List` structure | rust: `8010a70` |
| #235 | `Bag` structure and `bag` type | rust: `1a49331` |
| #295 | `ListPair` structure | rust: `53b815c` |
| #302 | `Either` structure | rust: `0c816f4` |
| #301 | `Fn` structure | rust: `fde8eb4` |
| — | `Vector` structure and `vector` type | rust: `17a42dd` |
| — | Exceptions | rust: `ea86d11` |
| — | Closures | rust: `8ea5aed` |
| — | Pattern matching of `Option` (`SOME`/`NONE`) | rust: `0e4b4f6` |
| — | Recursive functions | rust: `c1fd023` |
| — | Record type inference | rust: `1a59ca3` |
| #311 | `op` keyword (operator sections) | rust: `80efa02` |
| #315 | Parse `signature` | rust: `fa5936f` |
| — | Standard-library signatures | rust: `8f6657f` |
| #310 | Validation mode (`:t` syntax) | rust: `cf7ebcf` |
| #300 | `-c` / `--command` flag (run `.smli` scripts) | Java uses `--run`; similar intent (rust: PR #23) |
| #319 | `productName`, `productVersion`, `banner` properties | rust: `d99f5d1` |
| — | `Sys` structure (`plan`, `unset`, `clearEnv`, `showAll`) | Java #251, #260 (rust: `a2cab34`) |
| #24 (rust) | `Relational` structure | rust: `d7e601a` |
| #18 (rust) | Tune `Unifier` (persistent data structures) | rust: `86006ae` |
| #273, #288 | Type inference for query steps (`group`, `compute`, `elements`, `exists`, `forall`, `distinct`, `order`, `skip`, `take`) | Commits `3d0acec`–`334a656`; fixup `915856d` |
| — | Warning infrastructure | rust: `d0d9eb4` |
| (0.4+) | `distinct`, `order`, `skip`, `take` execution | In evaluate-mode tests since before A1 (rust: `e20ae30`) |
| #253 | Set operators (`union`, `intersect`, `except`) as pipeline steps | In evaluate-mode tests since before A1 (rust: `e20ae30`) |
| #288, #304 | `group`/`compute`/`elements` execution | `over` syntax needs C1 first (rust: `e20ae30`) |
| #249 | `with` operator for records (`{r with f = v}`) | Resolver + type_resolver fix (rust: `e7ae0f4`) |
| #291 | `typeof` operator | TypeKind::Expression handler in TypeToTermConverter (rust: `cdd547f`) |
| #306 | Nested block comments | Already in pest grammar; added test (rust: `2b23914`) |
| #343 | Shared type-variable scope within declarations | `decl_type_vars` in TypeResolver; `mustBeList` workaround removed from test scripts (rust: `b9b057e`) |

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
