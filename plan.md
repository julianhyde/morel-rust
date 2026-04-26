# Predicate Inversion in morel-rust

Port plan for the morel-java "such-that" / unbounded-variable feature.

## Goal

After all phases land, `from`-expressions that contain unbounded
variables must compile and evaluate. Concrete acceptance: every
test case added to morel-java's `.smli` files in commits

  * `eff94a5d` — Implement queries with unbounded variables (#217)
  * `d0249a04` — Invert `case` expressions with multiple arms (#341)
  * `27f98a5c` — Refactor predicate inversion logic
  * `3ec81171` — Predicate inversion should filter by outer-scope variables (#347)

passes in morel-rust **without modifying the queries or expected
output** (subject to the carve-out in [Out of scope](#out-of-scope)).

After every commit on this branch, `fullMake --no-clean` must pass.

## Out of scope (deferred)

- `62581437` (Datalog) and `5aa84eef` (graph examples) — done later.
- `Sys.planEx` — a handful of tests in `optimize.smli` and
  `such-that.smli` print the optimized core plan. morel-rust has only a
  partial `Sys.plan` and no `planEx`. We defer those plan-introspection
  tests; the semantic tests of the same files must still pass.
- `Sys.set("output", "tabular")` mode in eff94a5d (cosmetic; tests can
  be guarded with the existing `output=classic` default until tabular
  output lands).

If a test depends on either of these, we either copy it without the
`Sys.planEx ...;` lines, or we hold the test out and track it in a
follow-up issue. Critically, **no test query is rewritten**.

## Algorithm overview

The morel-java pipeline is a two-phase visitor over a `Core.From`:

```
                     ┌────────────────────┐
   AST ──resolver──> │  Core.From         │
                     │  (unbounded vars   │ ──phase 1──> generator cache
                     │   appear as Scan   │              (multimap pat→Generator)
                     │   over an Extent   │
                     │   marker, or as a  │ ──phase 2──> Core.From with
                     │   pattern with no  │              synthesised Scans,
                     │   source)          │              simplified Wheres
                     └────────────────────┘
```

**Phase 1 — derive generators** (`Expander.expandFrom` →
`Generators.maybeGenerator`)

1. Walk the steps left-to-right. For each `Where`, decompose the
   condition into a conjunction of conjuncts.
2. For every free pattern in the conjuncts, run a *classify-then-
   synthesise* loop:
   - Classify each conjunct as `elem`, `point`, `range`,
     `stringPrefix`, `case`, `function`, `exists`, etc.
   - Synthesise the strongest (lowest-cardinality) generator and add
     it to a per-pattern multimap (the **cache**).
3. The cache is monotonic: refinements append; `bestGenerator(pat)`
   returns the last entry.
4. Each generator carries:
   - `pat` — pattern bound by the resulting scan,
   - `exp` — Core expression to scan,
   - `cardinality` ∈ {SINGLE, FINITE, INFINITE},
   - `freePats` — patterns the generator depends on (drives ordering),
   - `provenance` — minimal set of original `Where` conjuncts that this
     generator fully encodes,
   - `sealed` — whether the provenance is trustworthy (leaf
     generators are sealed; composite ones like `ExistsJoinGenerator`
     are not).

**Phase 2 — rewrite the from** (`Expander.expandFrom2`)

1. Topologically order patterns by `freePats` dependency (`PatternState`
   tracks `IN_PROGRESS` for cycle detection, `DONE` once a scan is
   emitted).
2. For each unbounded pattern `p`, emit a `Scan(p, generator.exp)`
   step. If `p` was already bound in an outer scope (i.e. *not in*
   `allScanPats`), treat it as already-bound and emit a join condition
   `p' = p` rather than re-binding.
3. For each original `Where` step, decompose its conjunction, drop
   conjuncts that appear in any sealed generator's provenance, then
   apply each generator's `simplify()` to the remainder.
4. Rebuild the `From` with the new step sequence.

**Outer-scope filtering** (3ec81171): `addGeneratorScan` treats `p` as
already-bound when `patternState[p] == DONE` *or* `p` is absent from
`allScanPats`. The latter is the bug fix for nested `from` expressions
that read a variable from an enclosing scope.

**Case inversion** (d0249a04): `maybeCase` decomposes a multi-arm case:
- arms returning `true` with literal pattern `lit` contribute `subject = lit`,
- arms returning a condition `c` with id pattern `n` contribute `c[subject/n]`,
- arms returning `false` with literal pattern contribute exclusion
  constraints `subject <> lit` AND-ed onto subsequent arms.
The OR of these becomes the synthesised constraint, fed back into
`maybeGenerator`.

## morel-rust starting point

What's already in place (from
[the inventory](#appendix-a-rust-inventory)):

- `compile/core.rs` — Core IR with `Expr::From(_, Vec<Step>)` and
  `StepKind::{Scan, Where, Yield, Order, …}`.
- `compile/from_builder.rs` — accumulates steps and runs a small set
  of simplifications (e.g. removing `where true`). Has a TODO for
  nested-from inlining.
- `compile/resolver.rs::resolve_query()` — orchestrates AST→Core for
  queries; populates a `FromBuilder`; calls `build_simplify()` at end.
- `compile/var_collector.rs` — collects defined/referenced vars; not
  designed for predicate analysis.
- `syntax/ast.rs` — has `StepKind::ScanExtent(Box<Pat>)` for `from p`
  syntax (no `in`); the type resolver currently **panics** on it
  (verified: `target/release/main` panics at `type_resolver.rs:2338`
  on `from i where i > 0 andalso i < 10;`).

What's missing (must build): `Expander`, `Generator`, `Generators`,
`Simplifier`, `Replacer`, dedicated `FreeFinder`, plus the
`ScanExtent`-handling path in the resolver/type resolver.

## Phases

Each phase is one PR-sized commit; `fullMake --no-clean` must pass at
the end of each.

### Phase 0 — Scaffolding

**Files:** `src/compile/free_finder.rs` (new),
`src/compile/replacer.rs` (new), additions to `compile/core.rs`,
`compile/type_resolver.rs::deduce_scan_step_type`.

1. Add `FreeFinder`: walks a Core expression in an environment and
   returns the set of free `NamedPat`s. Mirrors morel-java's
   `FreeFinder` + the bits of `EnvShuttle` we need.
2. Add `Replacer`: substitutes `NamedPat → Core::Expr`. Used by
   case inversion and by the function-inlining generator.
3. Wire `StepKind::ScanExtent(p)` end-to-end: type resolver allows it
   (records type of `p` from context), resolver lowers it to a Core
   step that the Expander will recognise. Recommended Core
   representation: a `Scan(p, Expr::Extent(t))` where `Extent(t)` is a
   new placeholder Core expression that fails to evaluate but carries
   the type. (Equivalent to morel-java's `Extents.singleton(t)` —
   denotes "all values of type `t`".)
4. **Acceptance**: existing tests still pass; `fullMake --no-clean`
   green. No semantic change yet — `from i where i > 0` still errors,
   just more cleanly (e.g. "unbounded variable `i`" instead of an
   `Option::unwrap()` panic).

### Phase 1 — Leaf generators (elem, point, range)

**Files:** `src/compile/expander.rs` (new),
`src/compile/generator.rs` (new), `src/compile/generators.rs` (new),
hook into `resolver::resolve_query()`.

1. Define `Generator` struct (`pat`, `exp`, `cardinality`,
   `free_pats`, `provenance`, `sealed`, `unique`).
2. Implement `Generators::maybe_generator` with three leaf strategies:
   - **PointGenerator**: `x = c` ⇒ `[c]`.
   - **CollectionGenerator**: `x elem coll` ⇒ `coll`.
   - **RangeGenerator**: `x ≥ a` ∧ `x ≤ b` (and `<`/`>` mixed) on
     `int` ⇒ `List.tabulate(b-a+1, fn k => a + k)` etc.
3. Implement `Expander::expand_from`:
   - Phase 1: walk steps; for each `Where`, split into conjuncts;
     accumulate per-pattern generators in a `Cache` (multimap).
   - Phase 2: rebuild `From`; emit a `Scan(p, gen.exp)` for each
     unbounded `p` (use `bestGenerator`); rewrite `Where` by
     dropping conjuncts in any sealed generator's `provenance`.
4. Plug in `resolver::resolve_query()`: after `FromBuilder` finishes
   collecting steps and before `build_simplify()`, run the Expander
   on the resulting `From`. Skip if there are no unbounded patterns.
5. **Acceptance**: leaf-generator subset of `eff94a5d`'s
   `such-that.smli` passes (≈30 tests covering `=`, `<`, `>`, `<=`,
   `>=`, `andalso`, `orelse`, `mod`, `elem` for tuples and records,
   `from x, y where (x, y) elem [...]`).

### Phase 2 — String prefix generator

**Files:** add to `compile/generators.rs`.

1. Implement **StringPrefixGenerator** for `String.isPrefix p s`:
   inverts to `List.tabulate(String.size s + 1, fn i =>
   String.substring(s, 0, i))`.
2. Verify built-ins exist (they do: `String.isPrefix`,
   `String.substring`, `String.size`, `List.tabulate`).
3. **Acceptance**: ~6 prefix-related tests in `eff94a5d`'s
   `such-that.smli` pass.

### Phase 3 — Function inlining + `exists`

**Files:** add `maybe_function`, `maybe_exists` to `generators.rs`;
`Replacer` already exists from Phase 0.

1. **maybe_function**: when a conjunct is `f arg1 … argN` and `f`'s body
   is available as Core, inline the body with parameters substituted,
   then recurse `maybe_generator` on the inlined Core. Cycle guard:
   refuse to inline a function already on the inlining stack
   (recursion stays unsupported until later, which is fine — the
   commits we're porting introduce recursive `reachable` only in
   3ec81171, which is gated on this).
2. **maybe_exists**: `exists … where …` ⇒ a join generator over a
   nested `from`. Mark unsealed.
3. **Acceptance**: function-defined predicate tests
   (`fun isNum n = n elem nums`, etc.) and `exists`/`forall` tests
   from `eff94a5d` pass.

### Phase 4 — Case (single arm)

**Files:** `generators.rs::maybe_case`.

1. Handle case expressions whose arms are: literal-pattern → `true`,
   id-pattern → condition. Single-arm case is the common pattern after
   `fn` desugaring (`fn x => body` becomes `case _arg of x => body`).
2. **Acceptance**: case-inversion tests from `eff94a5d` pass (the ones
   that don't need multi-arm). About 4–5 tests.

### Phase 5 — Case (multi-arm + constructors)

**Files:** extend `generators.rs::maybe_case`; uses `Replacer`.

1. Multi-arm decomposition: build the OR of arm constraints,
   apply exclusion constraints from prior false-arms.
2. Constructor patterns (`INL n`, `INR (b, i)`, user datatypes): each
   arm contributes a subset constraint; the result is an OR over arms.
3. **Acceptance**: all of `d0249a04`'s `such-that.smli` additions pass,
   including the bar-patron `happy` query that was previously gated.

### Phase 6 — Provenance refactor (27f98a5c)

This commit reshapes the algorithm without adding new tests; we apply it
in one commit so the cache and conjunct-elimination logic match the
final morel-java shape before we tackle 3ec81171.

**Files:** `generator.rs`, `expander.rs`.

1. Add `provenance: Vec<Conjunct>` and `sealed: bool` to `Generator`.
   Leaf generators set `sealed = true` and populate `provenance` with
   the conjuncts they fully encode.
2. Make `Cache` strictly monotonic: never remove a generator on
   refinement; `best_generator` returns the most-recently-inserted entry.
3. In `expand_from2`, rewrite each `Where` by dropping conjuncts that
   appear in any sealed generator's provenance.
4. **Acceptance**: existing tests still pass; the 30 new lines of
   `such-that.smli` from 27f98a5c (which check that redundant `op elem`
   conjuncts are removed from plans) pass *if* `Sys.planEx` is available;
   otherwise treat semantically. No regressions.

### Phase 7 — Outer-scope filtering (3ec81171)

**Files:** `expander.rs::add_generator_scan`, `from_builder.rs::scan`.

1. In `add_generator_scan`, treat `p` as already-bound when
   `pattern_state[p] == Done` *or* `p ∉ all_scan_pats`. Emit a join
   condition `p' = p` instead of a fresh scan in the second case.
2. Mirror the morel-java fix in `FromBuilder::scan`: when inlining a
   subquery whose last step is `yield id(X)` and `X` matches the outer
   scan pattern but `add_all` introduced multiple bindings, emit
   `yield id(X)` (scalar) rather than `{X = id(X)}` (record). This is
   the "ClassCastException at runtime" fix.
3. **Acceptance**: `blog.smli` `reachable` / `cousin` queries
   (24-line addition) produce the correct counts per `source`.

### Phase 8 — Cleanup and full sweep

1. Run the entire `tests/script/*.smli` suite; address any fallout.
2. Remove temporary scaffolding flags / dead code.
3. Update `tests/smile.rs` to register any newly-added test files.
4. Re-port any test cases initially deferred for `Sys.planEx`
   reasons, with the `planEx` lines stripped (tracked separately).

## Risks and open questions

- **`Sys.planEx`**: morel-rust currently has no plan-string surface.
  Several morel-java tests (especially in 27f98a5c and parts of
  eff94a5d) verify the *plan* not the *result*. We can either add a
  minimal `Sys.planEx` (it would help future debugging) or hold those
  tests until after Phase 8. Decision to be made when we land Phase 6.
- **Tabular output mode** (`Sys.set("output","tabular")` at the top of
  `eff94a5d`'s `such-that.smli`): pretty-printer feature, orthogonal
  to predicate inversion. We can either: (a) write the test file with
  tabular off (re-encoding the expected output to classic style) or
  (b) port tabular output as a separate side commit. Simpler is (a) —
  but per the goal we shouldn't modify expected output. So this likely
  needs a small commit before Phase 1 to add tabular output. Track as
  Phase 0.5 if tests need it.
- **Recursion**: `maybe_function` (Phase 3) does not yet handle
  recursive functions; the only test that needs recursion is the
  `reachable` example in `3ec81171`, which we tackle in Phase 7. We may
  need a small extension to `maybe_function` (semi-naïve evaluation,
  or just the morel-java `Relational.iterate` path) — assess in Phase
  3 and split into 7a if non-trivial.
- **Where to insert the Expander pass**: current plan is "after
  `FromBuilder` finishes, before `build_simplify`". Alternative is a
  post-resolver core pass over the whole tree. Inserting inside
  `resolve_query` is more local but only handles top-level `From`s.
  morel-java uses `SuchThatShuttle` which walks the *entire* program
  to find Froms inside let-bindings. We probably want the same — an
  outer post-resolver shuttle. Decide in Phase 1.
- **`var_collector` interaction**: predicate inversion may rename
  patterns; `var_collector` runs later for frame allocation. Confirm
  no fixed-point assumptions are broken.

## Appendix A: rust inventory (one-line summary)

| morel-java | morel-rust | state |
| --- | --- | --- |
| `SuchThatShuttle` | (none) | build new |
| `Expander` | (none) | build new |
| `Generator` (interface) | (none) | build new |
| `Generators` (factory) | (none) | build new |
| `Simplifier` | (none) | build new |
| `Replacer` | (none) | build new |
| `FreeFinder` | (none — `var_collector` is for frames) | build new |
| `CoreBuilder` | `compile/core.rs` constructors | reuse, may extend |
| `Core.From / FromStep / Scan` | `Expr::From` + `StepKind::{Scan,…}` | exists |
| `EnvShuttle` / `EnvVisitor` | `inliner::Transformer` (loose) | reuse pattern |
| `FromBuilder` | `compile/from_builder.rs` | exists; small extensions |
| `Extent` / `Extents` | (none) | build minimal `Expr::Extent(t)` |
| `ScanExtent` parsing | `syntax/ast.rs::StepKind::ScanExtent` | parses, no resolver wiring |

## Appendix B: acceptance test inventory

| Commit | Files touched | New lines | Coverage |
| --- | --- | --- | --- |
| `eff94a5d` | such-that.smli, blog.smli, scott.smli, optimize.smli, built-in.smli | ~990 | ranges, equality, elem on tuples/records, isPrefix, case (single arm), exists/forall, function predicates, group/order/take on unbounded sources |
| `d0249a04` | such-that.smli | +52 | multi-arm case; INL/INR constructor inversion; combined arms |
| `27f98a5c` | such-that.smli | +30 | plan-quality assertions (provenance elimination, no-distinct) |
| `3ec81171` | blog.smli | +24 | recursive `reachable`, outer-scope filtering, scalar-yield fix |

The detailed test-by-test inventory lives in the agent reports
captured during planning; we'll re-derive it as each phase comes up.
