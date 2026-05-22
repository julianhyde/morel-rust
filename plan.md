# Plan: tune `built-in.smli` and the unifier (issue #34)

Working document for hydromatic/morel-rust#34. Captures the prior
analysis posted on the issue, current measurements, hypotheses about
remaining bottlenecks, and the benchmarks that would validate (or
falsify) each one.

## Status

* Issue: <https://github.com/hydromatic/morel-rust/issues/34>
* Original analysis: posted as a comment on the issue (Mar 2026).
* Since then, `built-in.smli` was split into one file per structure
  (commit `0fec908`), so the original 26 s wall-clock test no longer
  exists in that form — its work has been parallelised across files.
* The underlying performance characteristics (and the per-statement
  fixed cost) remain unchanged, which is what this document focuses on.

## Progress log

| Date | Change | bench-built-in (release) | 10 000×`1+2;` |
|---|---|---:|---:|
| 2026-05-21 | baseline | 29.0 s | 2.95 s |
| 2026-05-21 | H1a (cache base Env) | 26.4 s | 0.45 s |
| 2026-05-21 | H3a (im → std HashMap) | 15.8 s | 0.45 s |
| 2026-05-21 | New-1 (one resolver pass) | 15.3 s | 0.45 s |
| 2026-05-21 | chained-scopes Env | 14.5 s | 0.40 s |

Note: New-1 also moved size-200 (1000 × n-200) from 37.7 s to
31.6 s (~16 %). The bench-built-in win is small because
type-checking dominates there; size-K wins because the resolver
is a larger fraction of per-stmt work for big, simply-typed
expressions.

H1a — `Session::base_env()` lazily builds the inliner `Env` populated
with all built-ins once per session, then layers per-statement
session bindings on top via `Env::child` (HAMT path-copy on top of
the cached structural-sharing parent). Removes ~460 `Type::clone`s
+ a HAMT rebuild from every statement. Lands `1+2;` throughput at
~45 µs/stmt (was ~295 µs/stmt). Bench-built-in moves only 9 %
because most of its statements are large enough that per-node
unifier work (H3) dominates.

H3a — `Work.result`, `Substitution.substitutions`, and the `active`
working set in `act` switched from `im::HashMap` / `im::HashSet` to
`std::HashMap` / `std::HashSet`. The unifier uses these as mutable
accumulators, not as persistent maps. Bench-built-in dropped 40 %
on release (26.4 → 15.8 s) and 9 % on debug (208 → 189 s). The
size scan and small-stmt workloads are unmoved because their
per-statement substitution maps are too small for HAMT vs flat
hashmap constant factors to matter. We captured ~90 % of the
unifier-HAMT headroom the original flamegraph identified
(~41 % of pre-H1a runtime in HAMT iteration + teardown).

New-1 — Eliminate the duplicate resolver pass. Previously
`evaluate_node` called both `resolver::resolve_pre_expander` and
`resolver::resolve_with_session_fns_rec`, each doing a full
AST→Core walk. Now `resolve_with_session_fns_rec` does the
resolver pass once and eagerly extracts the pre-expander
`fn p => body` bindings (a top-level-only walk, cheap) before
moving the decl into the expander. The shell commits those
extracted bindings into `rec_fn_bindings` after the statement
succeeds. Bench-built-in: 15.8 → 15.3 s (~3 %). size-200: 37.7 → 31.6 s
(~16 %). The win is bigger on size-200 because the resolver is a
larger fraction of per-statement work for big, simply-typed
expressions; bench-built-in's per-statement budget is dominated
by type-checking, not AST → Core conversion. Initial measurement
only sampled bench-built-in and undersold the change.

Chained-scopes Env — Replaced `im::HashMap` (HAMT) in
`inliner::Env` with a chain of `Rc<EnvFrame>`s where each frame
holds a small flat `HashMap`. `Env::clone` is still O(1) (Rc
bump), `Env::child` allocates one new frame instead of HAMT
path-copy, and lookups walk the chain (typical depth ≤ 15).
Crucially the `Env` API (`child`, `child_none`, `child_expr`,
`lookup`, `lookup_expr`) is unchanged, so no `&Env → &mut Env`
plumbing was needed.

Wall-clock impact (M-series macOS, release build):
  bench-relational (50×)  10.5 s → 8.1 s   (-23 %)
  bench-built-in          15.3 s → 14.5 s  (-5 %)
  10 000 × `1+2;`          0.45 s → 0.40 s (-11 %)
  size-200                 31.6 s → 32.1 s (noise)

The relational workload is where this hits hardest because
`from`-queries push a new scope at every step. The Mar-issue
flamegraph put HAMT iteration at 36 %; the post-H3a-flamegraph
showed `im::HashMap::update` + `im::HashMap::insert` +
`Env::child` + HAMT drops summing to ~50 % on bench-relational.
The dependency on the `im` crate has been removed entirely.

## Post-H1a+H3a flamegraphs (May 2026)

Captured with `cargo flamegraph --bin main -- …` on release with
`[profile.release] debug = "line-tables-only"`. SVGs in
`target/flame/` (gitignored).

The two workloads now have very different shapes — the original
"HAMT iteration is 36 %" hotspot is **gone in both**, and the
remaining costs are workload-specific.

### bench-built-in (15.8 s, many statements, complex types)

| % | Category | Top entries |
|---:|---|---|
| 13.9 | type resolver | `deduce_decl_type` |
| 13.6 | type resolver | `deduce_val_bind_type` |
| 13.2 | type resolver | `deduce_expr_type` |
| 12.1 | **source resolver, pass 1** | `resolve_with_session_fns_rec` |
| 11.2 | **source resolver, pass 2** | `resolve_pre_expander` |
| 8.4  | source resolver | `resolve_val_decl` |
| 6.6  | unifier | `unify_with_constraints` |
| 6.2  | unifier | `apply1` |
| 4.9  | inliner Env | `drop_in_place<Env>` (HAMT teardown) |
| 4.0  | inliner Env | `Env::child` |
| 3.4  | inliner Env | `im::HashMap::update` |
| 3.5  | type clone | `<Type as Clone>::clone` (deep tree) |
| 3.2  | parser | `parse_statement` |
| 2.9  | type resolver | `FunTypeEnv::get` (per-name lookups) |

Biggest finding: **the source resolver runs twice per statement**
(`resolve_pre_expander` + `resolve_with_session_fns_rec` =
~23 %). The pre-expander pass exists so phase 2 of recursive
predicate inversion (morel#217) can see the original conjuncts,
but every statement pays for it whether it uses recursion or not.

### size-200 (37 s, 1000 statements of depth-200 expression chains)

| % | Category | Top entries |
|---:|---|---|
| ~12 | type resolver | `deduce_expr_type`, `deduce_call2_type`, `deduce_apply_type` |
| ~13 | compiler | `compile_statement`, `compile_val_decl`, `compile_expr`, `compile_tail_expr` |
| ~13 | parser | `expr_additive`, `spanned`, `parse_statement`, precedence-level rules |
| ~10 | source resolver | `resolve_expr`, `call2` |
| ~6  | **AST clone/drop** | `Expr::clone`, `Expr::drop_in_place`, `ExprKind::clone` |
| 0.3 | **unifier** | virtually nothing |
| 0.1 | inliner | virtually nothing |
| 0.0 | im::HashMap | gone |

The O(n²) shape for size-K **is not in the unifier**. The most
suspect single chunk is the ~6 % spent in `Expr::clone` /
`Expr::drop_in_place` / `ExprKind::clone` — deep AST cloning at
each level of a traversal would produce exactly the observed
"per-node cost doubles when n doubles" curve.

### Implications for next steps

* **H3b / H3c (skip clone in `act`, reverse-index `act2`)** —
  diminished payoff. Unifier is now only 6–7 % of bench-built-in
  and ~0 % of size-200. Even a complete win on the remaining
  unifier hot spots would buy <10 % overall.
* **Eliminate the resolver double-pass** — well-defined target,
  ~11 % of bench-built-in. The pre-expander result might be
  derivable from `decl` without a separate AST walk, or could
  be lazily computed only for statements that actually use
  recursive predicate inversion.
* **Investigate AST clone-on-traverse** — could explain size-K's
  O(n²). Likely affects every workload to some degree.
* **H2 (Rc<Type>)** — modest payoff. Type clone is 3.5 % of
  bench-built-in, 0.4 % of size-200. Refactor is large.

## Overall-progress benchmark (May 2026)

`tests/script/bench-built-in-rust.smli` and
`tests/script/bench-built-in-java.smli` are concatenated builds of
the per-structure scripts in their respective repos, regenerated by
`etc/build-bench-built-in.py`. Both pass idempotent-mode validation
on their native platforms; cross-platform compatibility is **not**
attempted (see "Rust ↔ Java script divergence" below). Generator
behaviour:

* Strip license headers.
* Strip `set("mode","validate") … set("mode","evaluate")` blocks
  (only present in the rust scripts).
* Skip `datalog.smli` (rust-only, path-sensitive).
* Insert `Sys.clearEnv ()` between files so each section runs with
  a clean environment.
* Drop `Sys.plan ()` / `Sys.planEx ...;` calls because their output
  embeds a compiler-internal fresh-variable counter that drifts
  across duplicated copies of the same script (java only — rust's
  inliner is counter-stable).
* Repeat the per-file body 6× so the fastest platform (java)
  exceeds the 5 s benchmark floor.

### Numbers (M-series macOS, idempotent mode, 3 runs each)

| Platform | Wall time | vs java |
|---|---:|---:|
| rust release  | 29.0 s | 4.1× |
| rust debug    | 220 s  | 31×  |
| java          |  7.0 s | 1×   |

This is the headline number to drive down. The 6× duplicate factor
is baked into the generator (`DUPLICATIONS`) — leave it fixed so
runs are comparable over time.

### Rust ↔ Java script divergence (informational)

A single shared benchmark file is not viable today. Counts of
diverging lines when each platform runs the **other**'s smli file
(idempotent diff, May 2026):

| File | java→rust diff | rust→java diff | note |
|---|---:|---:|---|
| date           |   0 |  113 | rust adds postfix `.toString ()`-style methods |
| either         |   0 |    0 | identical |
| interact       |   0 |    0 | identical |
| list-pair      |   0 |    4 | trivial wording diffs |
| time           |   4 |   41 | rust off-by-one in span columns (`1.1-1.24` vs `1.1-1.23`) |
| int            |   6 |   27 | rust prints `Overflow [overflow]`; span columns off-by-one |
| fn             |  10 |   26 | `Fn.repeat ~5` raises eagerly on java, lazily on rust (rust morel#354) |
| bool           |  12 |   44 | rust's `Bool` adds `<>`, `=`, `andalso`, `if`, `implies`, `orelse` |
| range          |  16 |  n/a | rust-only file |
| variant        |  16 |  n/a | rust-only file |
| string         |  52 |   65 | postfix on primitives, slight format diffs |
| general        |  57 |   40 | mode-toggle blocks; differing Sys.plan |
| math           |  69 |   83 | postfix; real number formatting |
| vector         |  84 |   98 | postfix |
| bag            |  94 |  128 | postfix; unordered output handling |
| char           | 105 |  127 | postfix; new chars in rust |
| option         | 114 |   46 | postfix; differing inliner output |
| list           | 150 |  270 | postfix; richer feature set on both sides |
| relational     | 306 |  173 | unique-var counter, postfix, query plan diffs |
| sys            | 388 |  403 | newer Sys API on rust, full divergence |
| real           | 436 |  485 | rust's full IEEE-754 path; java is sparser |
| order          | n/a |  n/a | rust-only file |
| datalog        | n/a |  n/a | rust-only file |

Most divergences fall into one of:

* **Postfix method-call syntax** — `5.abs ()`, `(SOME 1).valOf ()`,
  etc. Java's scripts use the newer postfix form (morel#346 in
  java); rust's scripts still use the prefix form even though
  rust supports both.
* **`Sys.plan` output format** — rust's inliner emits a different
  IR than java's (`apply2(...)`, `fn(bind(0) => …)`, `get(0)`).
* **Bool structure surface** — rust exposes `andalso`, `orelse`,
  `implies`, `if`, `<>`, `=`; java does not yet.
* **Diagnostic strings** — rust includes the lowercase tag
  (`Overflow [overflow]`), and most position spans are off-by-one
  (`1.1-1.27` vs `1.1-1.26`).
* **`SMLNJ` vs `SML/NJ`** — cosmetic comment difference in many
  files.

Aligning the scripts so a single bench works on both platforms is
follow-up work; not blocking on it.

## Prior analysis (verbatim, from the GitHub issue)

> **Setup**: Release build with debug symbols; flamegraph via
> `cargo flamegraph --test smile -- built_in`. Result: **3.67 s**
> (release) vs 2 s Java. Debug mode is ~26 s due to unoptimised Rust.
>
> ### Where time is spent (flamegraph top-level)
>
> | % | Function |
> |---|---|
> | 57% | `TypeResolver::deduce_type` |
> | 49% | `Unifier::unify` |
> | 34%+15% | `Unifier::act` |
> | ~36% | `im::nodes::hamt::Iter::next` |
> | 10% | `library::populate_env` |
> | 6%  | `Type::clone` |
> | 5%  | `Arc::drop_slow` + `SparseChunk::drop` |
> | 5%  | `inliner::Env::multi` |
> | 5%  | `resolver::Resolver::resolve_decl` |
> | 5%  | `parse_statement` |
>
> ### Root causes
>
> 1. `im::HashMap` (HAMT) in `Work.result` / `Substitution.substitutions`.
> 2. `Substitution::from_result` clones the whole map inside the unify
>    loop on every variable resolution that has term-actions.
> 3. `act2` does an O(n) scan of all substitution entries on every
>    `act` call.
> 4. `populate_env` rebuilds the ~500-entry built-in map on every
>    statement.
>
> ### Suggested follow-ups (from the comment)
>
> 1. Replace `im::HashMap` / `im::HashSet` in `unifier.rs` with `std::`.
> 2. Cache `populate_env` output once per session.
> 3. Avoid cloning `work.result` into a `Substitution` on every `act`.
> 4. Add reverse index to avoid O(n) scan in `act2`.

## Current state of the code (May 2026)

Spot-check vs. the prior analysis:

| Item | Status |
|---|---|
| `Substitution.substitutions` type | still `im::HashMap<Var, Term>` (unifier.rs:412) |
| `Work.result` type | still `im::HashMap<Var, Term>` (unifier.rs:692) |
| `Substitution::from_result` clones map | still does (unifier.rs:1188 and 1323) |
| `act2` O(n) scan over substitution | still does (unifier.rs:1450–1473) |
| `populate_env` called per statement | still called twice from shell/main.rs (1022, 1096) |
| `Env::multi` HAMT build per statement | still done (inliner.rs:1095–1115) |
| `Type` is `#[derive(Clone)]`, `Box<Type>` children | still (types.rs:23) — every clone walks the tree |
| `Type` wrapped in `Rc`/`Arc` for sharing | not done |

So none of the four follow-up tasks from the prior comment have
landed yet. They remain the highest-leverage fixes.

## New measurements (May 2026, release build on macOS)

All numbers from `target/release/main < script.sml > /dev/null`,
real-time via `/usr/bin/time -p`. Each script is N copies of the same
statement.

### A. Throughput of small statements (eval mode)

| Script | N | Wall time | Per-statement |
|---|---:|---:|---:|
| `1 + 2;`           | 100   | 0.17 s | 1.7 ms (incl. startup ~50 ms) |
| `1 + 2;`           | 1 000  | 0.31 s | 310 µs |
| `1 + 2;`           | 10 000 | 2.95 s | 295 µs |
| `1;`               | 10 000 | 2.98 s | 298 µs |
| `v;` (after `val v = 1`) | 1 000 | 0.32 s | 320 µs |
| `val x_i = 1 + 2;` | 1 000  | 0.58 s | 580 µs |

Per-statement cost in eval mode flattens at ~290 µs. The literal
`1;` and the variable reference `v;` are essentially the same cost
as `1 + 2;`, so this is a fixed overhead, not anything intrinsic to
the expression.

Adding a `val` binding nearly doubles the cost (+270 µs) — this is
`Session::commit_bindings` rebuilding the type-env and cloning
`type_bindings`.

### B. Validate-only mode (parse + type-check, no inline/eval)

After `Sys.set ("mode", "validate");`:

| N | Wall time | Per-stmt (excl. startup) |
|---:|---:|---:|
| 10 000 | 0.44 s | ~40 µs |
| 50 000 | 0.42 s | (suspect; see note) |
| 100 000 | 0.83 s | ~8 µs incremental |

Validate mode is **6× faster** than eval mode for these tiny
statements, despite still parsing and type-checking. **The bulk of
the per-statement cost is in inlining + compile + eval, not in type
resolution.** That points squarely at `populate_env` + `Env::multi`
+ `commit_bindings`. (The 50 k anomaly likely reflects validate-mode
short-circuiting or buffered output; needs a closer look but doesn't
change the conclusion.)

### C. Per-expression node count (fixed N=1 000 statements)

Each statement is `1 + 1 + 1 + ... + 1` with the given number of
literals:

| Nodes | Wall time | Per-statement | Per-node (excl. 0.31 s fixed) |
|---:|---:|---:|---:|
| 1   | 0.31 s | 310 µs | — |
| 5   | 0.36 s | 360 µs | 12 µs |
| 25  | 1.05 s | 1.05 ms | 31 µs |
| 50  | 2.97 s | 2.97 ms | 53 µs |
| 75  | 5.80 s | 5.80 ms | 73 µs |
| 100 | 10.0 s | 10.0 ms | 97 µs |
| 200 | 37.1 s | 37.1 ms | 184 µs |

Per-node cost roughly **doubles every time N doubles** — strong
signature of **O(n²)** behaviour in the per-statement work, almost
certainly inside the unifier (the type-checker is the only stage
whose work grows with expression size faster than linearly).

## Hypotheses

Hypotheses below are ordered by likely payoff. The "expected impact"
column is informed by the measurements above and by the prior
flamegraph.

### H1. Per-statement env-build dominates small-expression cost

**Claim.** For statements with ≤10 AST nodes, ≥80 % of wall-clock
time is spent in `populate_env` + `Env::multi` + `commit_bindings`
(rebuilding the ~460-entry built-in environment as an `im::HashMap`).
This work is independent of statement size.

**Evidence so far.** Validate mode (skips inliner + compile + eval)
is 6× faster than eval mode for `1+2;`. `1;`, `1+2;`, and `v;` all
cost ~290 µs — the cost is per-statement, not per-AST-node.

**Sub-hypothesis 1a (cache it).** Building the BTreeMap of
~460 entries every statement, then cloning every value into an
`im::HashMap`, is unnecessary because the built-in env never changes
between user statements. Caching the resulting `Env` in the session
and forking it on demand should cut the fixed per-statement cost
sharply.

**Sub-hypothesis 1b (clone a populated unifier).** The same logic
applies to the type-resolver's unifier: `TypeResolver::new()` is
called fresh on every statement, but the only op-defs registered
eagerly are 8 built-in ops (`list`, `bag`, `tuple`, ...). However,
`FunTypeEnv::get` lazily calls `tr.type_to_term(t)` on each *used*
built-in name. So no eager pre-load happens for type-checking
itself. The unifier-clone idea would help only if we *also* pre-load
all built-in type schemes into the unifier — likely net-negative
since most statements use only a handful.

**Verdict on H1.** Sub-hypothesis 1a is high-value and well-supported.
Sub-hypothesis 1b is probably not worth pursuing — keep
`FunTypeEnv`'s lazy behaviour.

**Expected impact.** Reducing the ~290 µs fixed cost to ~50 µs
(parse + lazy type-check + small eval) would make 10 000 × `1+2;`
drop from ~3 s to well under 1 s.

---

### H2. `Type::clone` is a hot path because `Type` is a deep-Box tree

**Claim.** `populate_env` does ~460 `Type::clone` calls per statement,
and `Env::multi` clones each `(Type, Option<Val>)` again into the
HAMT. `Type` derives `Clone` and uses `Box<Type>` (and `Vec<Type>`,
`BTreeMap<Label, Type>`) for its children, so every clone walks the
whole subtree and allocates fresh `Box`es. The deeper / wider the
type (e.g. `Relational.scott` is a record with ~30 fields, each of
which is itself a function type), the more this hurts.

**Evidence so far.** Prior flamegraph showed 6 % in `Type::clone` +
5 % in `Arc::drop_slow`/`SparseChunk::drop` — both consistent with
"populate the HAMT with cloned Types, then drop it next statement".
With the env-build now identified as the dominant fixed cost (H1),
type cloning inside that step is the obvious mechanical contributor.

**Fix sketch.** Wrap `Type` in `Rc<Type>` (or, at minimum, change
`Box<Type>` children to `Rc<Type>`), so `clone` is a reference-count
bump. `Type` is immutable after construction, so `Rc` is correct;
`Arc` would be needed only for cross-thread sharing (not currently
required).

**Caveats.** `Type` implements `PartialEq` (by structural equality),
which is fine with `Rc`. Pattern-matching `match t { Type::Fn(a, b)
=> ... }` would change from `&Box<Type>` to `&Rc<Type>` — same
ergonomics. Existing code that holds owned `Type` values would need
review (the `Vec<Type>` and `BTreeMap<Label, Type>` would also become
`Vec<Rc<Type>>` etc., or remain `Vec<Type>` and pay one shallow
clone per entry — investigate which is the win).

**Expected impact.** If H2 is correct, every site that clones `Type`
becomes O(1) instead of O(tree-size). populate_env's ~460 clones
go from "walk ~30 fields each" to "bump 460 refcounts". Combined
with H1 this should be additive.

---

### H3. The unifier is O(n²) in expression size

**Claim.** For an expression of size n nodes, the unifier does work
that grows quadratically with n. This is what causes the 100-node
statement to cost 10 ms and the 200-node statement to cost 37 ms.

**Evidence so far.** Per-node time roughly doubles each time n
doubles (12 → 31 → 53 → 73 → 97 → 184 µs/node at n = 5, 25, 50,
75, 100, 200). After subtracting the ~310 µs fixed overhead, the
remaining cost fits `c · n²` with c ≈ 1 µs better than any
sub-quadratic curve.

**Likely cause(s)** (from reading `unifier.rs`):

1. **`Work::substitute_list` rewrites both queues on every var
   resolution.** `unifier.rs:773` does `mem::take` on
   `seq_seq_queue` and `var_any_queue`, walks every element, applies
   the new (var → term) substitution to it, and re-pushes. If the
   queue has k pending pairs and we resolve n variables, this is
   O(n · k) ≈ O(n²) substitution work.
2. **`act2` scans every entry of the substitution map.** `unifier.rs:
   1450–1473` iterates the whole `Substitution` looking for
   variables that ultimately point at the just-resolved `variable`.
   With n substitutions and n term_actions, this is O(n²) per
   unify. (This was already called out in the prior analysis.)
3. **`Substitution::from_result` clones the entire HAMT** (unifier.rs:
   1188 and 1323) on every variable resolution that has any
   term_actions registered. HAMT clone is O(log n) per node times
   n nodes = O(n log n), but in practice the constant factor is
   huge (~36 % in the prior flamegraph was HAMT iteration alone).

**Fix sketch.**

* **3a.** Replace `im::HashMap` with `std::HashMap` for `Work.result`
  and `Substitution.substitutions` (mutable accumulator, no shared
  history needed) — already in the prior follow-up list, not done.
* **3b.** Avoid cloning `work.result` into a `Substitution` on every
  `act` call. Pass `&work.result` directly, change `Substitution`
  to hold a borrow during the action callback.
* **3c.** Maintain a reverse index `HashMap<Var, Vec<Var>>` (var →
  list of vars whose substitution value is this var) so `act2`
  can find chained variables in O(1) instead of scanning.
* **3d.** Reconsider `substitute_list`. Lazy substitution
  (substitute when *reading* the pair, not on every insert) would
  reduce per-resolution cost from O(k) to O(1), shifting work to
  the final `Substitution::apply` step. This is what most
  textbook Robinson unifiers actually do.

**Expected impact.** 3a + 3b should give an immediate constant-factor
win (the prior analysis estimated ~36 % of unifier time goes into
HAMT iteration). 3c removes the O(n²) scan in `act2`. 3d is the
biggest architectural change and the most uncertain.

---

### H4. Expression-size scaling: fixed cost dominates until ~25 nodes

**Claim.** For statements with ≤10 nodes the cost is dominated by
H1 (env-build). Between 25 and 100 nodes the per-node O(n²) unifier
work (H3) takes over. By 200 nodes the unifier is >99 % of cost.

**Already measured.** See "C. Per-expression node count" above. The
crossover where per-node unifier work overtakes the ~310 µs fixed
cost is around n = 15–20 (where total cost is ~0.6 ms, half env,
half unifier).

**Implication for prioritisation.**

* Real-world morel programs in the test suite have median expression
  size in single digits (a typical `val` binds a small literal,
  application, or `from` query). So H1 dominates aggregate test
  time more than H3.
* But H3 has a much higher worst-case ceiling: a single 1 000-node
  expression (e.g. a long string-concat or chained `case`) takes
  ~1 s today and would take ~4 s with double the nodes. Bench
  scripts that exercise large expressions are the right tool for
  validating H3 fixes.

---

## Benchmarks (artifacts)

All benchmark scripts live in `/tmp/` for now. Each runs in eval
mode (default) unless otherwise noted.

### bench_small_N.sml — "many small expressions" (validates H1)

```sh
# Generator:
for n in 100 1000 10000; do
  python3 -c "open('/tmp/bench_small_$n.sml','w').write('1 + 2;\n' * $n)"
done

# Runner:
for n in 100 1000 10000; do
  /usr/bin/time -p target/release/main < /tmp/bench_small_$n.sml > /dev/null
done
```

**Today's numbers**: 0.17 s, 0.31 s, 2.95 s.
**After H1 fix (predicted)**: under 1 s at N=10 000 (≤100 µs/stmt).

### bench_size_K.sml — expression-size scan (validates H3)

```sh
# Generator (K = node count per statement):
for k in 1 5 25 50 75 100 200; do
  python3 -c "
size = $k; expr = ' '.join(['1'] + ['+ 1']*(size-1)) + ';'
open('/tmp/bench_size_%03d.sml' % size,'w').write((expr+'\n') * 1000)
  "
done

# Runner:
for k in 001 005 025 050 075 100 200; do
  /usr/bin/time -p target/release/main < /tmp/bench_size_$k.sml > /dev/null
done
```

**Today's numbers**: 0.31, 0.36, 1.05, 2.97, 5.80, 10.0, 37.1 s.
**After H3 fix (predicted)**: per-node cost stays flat (~30 µs)
across all sizes; N=200 drops from 37 s to under 6 s.

### bench_validate_N.sml — strip inliner/eval (already validates H1)

```sh
python3 -c "
open('/tmp/bench_validate.sml','w').write(
  'Sys.set (\"mode\", \"validate\");\n' + '1 + 2;\n' * 10000)
"
/usr/bin/time -p target/release/main < /tmp/bench_validate.sml > /dev/null
```

**Today's number**: 0.44 s (≈40 µs/stmt — sets a floor that H1+H2
fixes can approach). Note the validate-mode anomaly at N=50 000;
needs investigating but the 10 k figure is solid.

### bench_val_binding.sml — bindings cost (validates H1)

```sh
python3 -c "
open('/tmp/bench_val.sml','w').write(
  ''.join(f'val x{i} = 1 + 2;\n' for i in range(1000)))
"
/usr/bin/time -p target/release/main < /tmp/bench_val.sml > /dev/null
```

**Today's number**: 0.58 s (580 µs/stmt — the +270 µs delta over
`1+2;` is `commit_bindings` rebuilding the type-env).

### Bench TODOs (not yet implemented)

1. **Microbenchmark for `populate_env`.** Needs `populate_env` to
   become `pub` (currently `pub(crate)`), or live as an
   integration test inside the crate's `tests/` tree. Goal: time
   1 000 iterations and compare with/without H2's `Rc<Type>` change.
2. **Microbenchmark for `TypeResolver::deduce_type`** in isolation.
   Should plateau in cost as expression size grows linearly *after*
   H3 fixes; today it should reproduce the O(n²) growth.
3. **Microbenchmark for the unifier alone** on a synthetic input
   that mimics the type structure produced by an n-way `+` chain.
   Letting us tune H3 fixes without going through the whole shell.
4. **Apples-to-apples vs Java.** The original issue's 2 s vs 26 s
   measurement should be reproduced on current code (post `0fec908`
   split) so we have an external reference point.

## H2 (Rc-Type) phased plan

The original H2 hypothesis — wrap `Type` so clone is O(1) — was
investigated in May 2026 and confirmed (~5 % bench-built-in, ~13 %
bench-relational ceiling). A big-bang refactor was attempted and
aborted: the change cascades through `Expr`, `Pat`, `ValBind`,
LIBRARY statics, and every `Box::new(Type::…)` callsite (~150+
sites). The work is real but needs to be staged so every commit
compiles and passes `fullMake`.

### Phase 1 — Thread-local `LIBRARY` and `bool_type()` helper

Pre-work that *doesn't* change `Type`'s structure but removes the
`Sync` constraint that statics like `LIBRARY` impose. Independent
of all later phases.

* Convert `pub static LIBRARY: LazyLock<Lib>` in `eval/code.rs`
  into `thread_local! { pub static LIBRARY: Lib }`.
* Update the 10 `LIBRARY.foo` callsites to
  `LIBRARY.with(|lib| lib.foo …)`.
* Replace `static BOOL: Type` in `pretty.rs` with
  `fn bool_type() -> Type` and update its 10 callers.

No perf change. Risk: low. Estimated effort: ~30 minutes.

### Phase 2 — `Box<Type>` → `Rc<Type>` migration (no interning)

Sub-phased by `Type` variant so each sub-commit compiles and the
test suite passes. Order is "least-used variant first" so the
mechanical edits get smaller as we go and the high-touch ones
land with a tested skeleton in place.

| Sub | Variant change | Approximate constructor sites |
|---|---|---:|
| 2a | `Type::Forall(Rc<Type>, usize)` | ~5 |
| 2b | `Type::List(Rc<Type>)` + `Type::Bag(Rc<Type>)` | ~30 each |
| 2c | `Type::Fn(Rc<Type>, Rc<Type>)` (heaviest) | ~80 |
| 2d | `Type::Tuple` / `Named` / `Data` / `Multi` (all `Vec<Rc<Type>>`) | ~60 combined |
| 2e | `Type::Record(bool, BTreeMap<Label, Rc<Type>>)` | ~15 |
| 2f | `Type::Alias(String, Rc<Type>, Vec<Rc<Type>>)` | ~5 |
| 2g | `Expr`/`Pat`/`ValBind` type-annotation fields `Box<Type>` → `Rc<Type>` | ~150 |

Between 2a–2f, `Expr`/`Pat`/`ValBind` keep their `Box<Type>`
annotation fields. When a constructor needs to bridge — e.g. a
new `Rc<Type>` child being placed into a `Box<Type>` slot — wrap
with `Box::new((*rc).clone())`. Ugly but compiles, and goes away
in 2g.

Also fold in (probably during 2g or as its own micro-phase):
remove the `Send + Sync` bounds from `Comparator` and `Discrete`
traits (they were defensive, never required at runtime; will
become unsatisfiable once Type holds `Rc`).

Total Phase 2 effort estimate: 4–6 hours. Each sub-commit should
be followed by `cargo test --release` and ideally `fullMake`.

Expected perf impact after Phase 2 lands fully (no interning):
~50–70 % of the H2 ceiling, i.e. ~3 % bench-built-in and
~7–9 % bench-relational. The remaining "interning" benefit (cat
3 below) is largely memory and pointer-equality, not clone speed.

### Phase 3 — *Future / optional* — Hash + `intern()` + apply

Only if Phase 2's measured gain doesn't close the rust↔java gap
enough.

* Derive `Hash` + `Eq` on `PrimitiveType` and `Type`.
* Add a thread-local `POOL: HashSet<Rc<Type>>` and
  `intern(Type) -> Rc<Type>`.
* Use `intern()` at LIBRARY init so library types are canonical,
  then at `FunTypeEnv::get` so each name reference returns the
  pre-interned `Rc<Type>` rather than cloning the LIBRARY entry's
  subtree.
* Optionally: pointer-equality shortcuts in unifier hot paths.

Expected delta on top of Phase 2: small but non-zero (memory
locality, occasional pointer-equality wins).

## Suggested execution order

The four follow-ups from the prior comment, in dependency order:

1. **H1a (cache env)** — single biggest hit on the small-statement
   workload that dominates aggregate test time. Low risk: the
   cached `Env` is keyed by "is anything user-defined in scope?"
   and easy to invalidate. Touches shell/main.rs:1090–1107 and a
   new cache field on `Session` or `Shell`.
2. **H3a (im::HashMap → std::HashMap)** — mechanical change in
   `unifier.rs`. Removes the dominant unifier overhead at all
   sizes. Should be done before H3b/c/d so we benchmark the
   algorithm, not the HAMT constants.
3. **H3b + H3c (skip `from_result` clone; reverse index for `act2`)**
   — direct unifier algorithmic wins, both already designed in the
   prior comment.
4. **H2 (`Type` → `Rc<Type>`)** — biggest mechanical refactor; gives
   leverage for everything that clones `Type` (`Env`,
   `populate_env`, `inliner::Env::child*`, `commit_bindings`,
   `TypeMap::*`). Easier to land after H1a so we can measure its
   impact in isolation.
5. **H3d (lazy substitution in unifier)** — biggest design change;
   defer until 1–4 have landed and a flamegraph confirms
   `substitute_list` is the remaining hotspot.

Each step should be followed by a re-run of `bench_small_10000.sml`
and `bench_size_100.sml` to track progress; both numbers should
fall monotonically.

## Open questions

* Validate mode at N=50 000 reported wall time *below* N=10 000 —
  is validate mode short-circuiting subsequent statements after
  `Sys.set`? Worth a 10-minute investigation before relying on
  validate-mode floor numbers.
* `BuiltInFunction::iter()` walks ~445 variants on every call from
  `populate_env`; is the order stable enough to memoise the
  resulting `BTreeMap`? (For H1a, yes — but worth double-checking
  there's no per-session state baked into entries.)
* `commit_bindings` rebuilds `self.type_env` (a chain of
  `ResolvedTypeEnv` → `FunTypeEnv` → `EmptyTypeEnv`) whenever a
  binding is added. Each rebuild allocates fresh `Rc`s but the
  inner `FunTypeEnv` is identical — could be cached. ~270 µs/stmt
  saving on `val`-binding statements.
