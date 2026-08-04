# Issue #48 — Enable `Sys.plan ()` / `Sys.planEx ()` in tests, consistent with morel-java

Follow-on to `f8b21ff3` ("`Sys.plan` crashes on a `from` expression"),
which stopped the panic but left the plan *strings* diverging from
morel-java. The goal here is to make morel-rust's plan output match
morel-java's, and un-gate the `.smli` sections currently bracketed by
`set("mode", "validate")` because of the mismatch.

## Scope

- **`Sys.plan ()`** — renders the compiled runtime `Code` in the
  "describe" format (`apply(fnValue X, argCode Y)`, `from(sink ...)`,
  `constant(...)`, `tuple(...)`). This is where the work is.
- **`Sys.planEx s`** — a *different* mechanism: re-plan the Core AST to
  a phase and unparse it back to Morel source. Already implemented in
  rust (`code.rs:2774`, via `pre_inline_decl` / `post_inline_decl`);
  phase `< 0` → pre-inline, `>= 0` → post-inline, matching java's
  `"0"` / `"-1"`. Only needs verification, not new machinery.

Already passing: most `Sys.plan` sections (optimize.smli 43 calls,
built-in/list.smli 32, ...). Rust's describe format already matches
morel-java for scalar/functional code. **The work is the 19 gated
regions / 28 gated `Sys.plan` calls** below.

## morel-java reference (source of truth)

- Describe engine: `eval/DescriberImpl.java` — `start(name, detail)`
  prints `name` bare when it has no args, else `name(arg0, arg1, ...)`;
  each arg is `argName value` (name omitted when empty).
- **Operator label** (`Codes.BaseApplicable.name()`,
  `ApplicableImpl.name()`): `mlName.startsWith("op ")` → strip the
  `"op "` prefix (`+`, `elem`, `=`); else `structure + "." + mlName`
  (`Int.+`, `List.map`, `Bag.fromList`, `Relational.count`). Driven
  entirely by each `BuiltIn`'s `(structure, mlName)`.
- `constant` node prints the value only — **no span**
  (`start("constant", d -> d.arg("", value))`).
- Row-sink labels (`eval/RowSinks.java`): `from(sink ...)`,
  `join(pat, exp, [condition], sink)` (condition omitted via `argIf`
  when constant-`true`), `where(condition, sink)`,
  `group(key, agg..., sink)`, `order(code, sink)`,
  `yield(codes [...], sink)`, `collect(code)`, `skip`, `take`.
  Leaves: `get(name X)`, `stack(offset N, name X)`, `aggregate`.
- Hybrid-only (`Calcite.java`): `calcite(plan <RelNode text>)` and
  `globalMarshal(globals [...], body ...)`. **Rust has no Calcite
  backend → these are permanent divergences.**

## Divergence taxonomy (rust `Display for Code`, `src/eval/code.rs`)

| # | Cause | Location | Fix |
|---|---|---|---|
| A | `Native0` / `NativeCustom` print `{:?}` (raw variant, e.g. `Bag`) instead of the `.plan()` label (`Bag.fromList`) | `code.rs:1861`, `1887` | use `.plan()` |
| B | `NativeF1/F2/F3` inject `constant(<span>)` when a builtin carries an error span (`List.only [7]` → `..., constant(stdIn:1.1-1.14)`) | `code.rs:1894–1946` | drop the span arm; render as the no-span form |
| C | Label table doesn't match java: `List.elem` vs bare `elem`, and any builtin whose `mlName` is `"op ..."` | `code.rs:4686` (`operator_plan_name`), `4709` (`camel_to_dotted`) | derive the label from the builtin's strum `(p, name)` props + the `"op "`-strip rule; retire `camel_to_dotted` and `operator_plan_name` |
| D | Row-sink `from(...)` format approximated in `f8b21ff3` | `eval/row_sink.rs` `fmt_plan` | align labels/args with `RowSinks.describe` (condition via `argIf`, `group`/`order`/`yield` shapes) |
| E | Genuinely different compiled plan (Calcite/`globalMarshal` in hybrid mode; optimizer inlines differently) | — | document in `smli-divergence-backlog.md`, keep gated |

### On fix C (the central one)

Rust already carries `(p = structure, name = mlName)` in each builtin's
`#[strum(props(...))]`. The faithful port is to make `EagerFn::plan()`
read those props and apply the `"op "`-strip rule, retiring
`camel_to_dotted` (a mechanical guess) and folding `operator_plan_name`
into the data. This automatically fixes `elem`, `+` variants, `=`, etc.,
and removes a table that has to be hand-maintained. Verify the strum
`name`/`p` props exist for every native variant first; add where missing.

## Plan of work

1. **Fix A, B, C** in `code.rs` — unify every `fnValue` label path on a
   single `plan()` that mirrors java's `name()`, and stop emitting the
   span. Re-run the *already-enabled* `Sys.plan` sections (optimize,
   list, math, real, string, vector, option, sys) to confirm **no
   regressions** — these are the safety net.
2. **Fix D** — bring `row_sink.rs::fmt_plan` in line with
   `RowSinks.describe`: `join` condition suppressed when constant-true;
   `group(key ..., agg ..., sink ...)`; `order`, `yield`, `collect`,
   `skip`, `take`; `get(name X)` / `stack(offset N, name X)` leaves.
3. **Un-gate region by region** (list below): delete the
   `set("mode","validate")` / `set("mode","evaluate")` pair, run the
   script, and either (a) it matches → keep enabled, or (b) it's a
   type-E divergence → re-gate and record in the backlog with the reason.
4. **Backlog** — update `smli-divergence-backlog.md` for every region
   that stays gated (Calcite/hybrid, or a separate open bug).
5. **Gate & verify** — `etc/check-convergence.py HEAD --java-repo
   ~/dev/morel.1` must not increase net divergence; `/usr/local/bin/
   fullMake --no-clean` green.

## The 19 gated regions

Likely closed by the A–D fixes (mechanical label / span / row-sink):

- `built-in/relational.smli` 46–60 — `Relational.count (bag ...)`; `Bag` → `Bag.fromList` (fix A).
- `built-in/relational.smli` 193–217 — `elem`; `List.elem` → `elem` (fix C).
- `built-in/relational.smli` 116–123, 234–258 — `Relational.iterate` / row-sink; fixes C+D (verify).
- `built-in/bag.smli` 145–149 — label (fix A/C).
- `built-in/list.smli` 162–166 — `List.only`; drop span arg (fix B).
- `relational.smli` 3365–3374, 3387–3395, 3412–3445 — `FromRowSink` (unblocked by `f8b21ff3`); fix D (verify).

Need investigation — may be separate bugs, not plan-format:

- `built-in/general.smli` 88–106 — `fail.smli` shows an
  `Option::unwrap()` panic (`code.rs:2613`); likely a distinct bug.
- `built-in/general.smli` 114–122 — `plan differs`; check after C/D.
- `hybrid.smli` (7 regions, 15 calls) — **split**: Calcite-pushed cases
  (`calcite(...)`, `globalMarshal(...)`) are permanent type-E
  divergences; native `max`/`min`-fallback cases
  (`from(... group(... collect(get(name max))))`) are achievable once
  fix D handles the aggregate/group sink (currently panics per the
  backlog). Expect this script to remain partly gated.
- `blog.smli` 261–1683 — a 1400-line region gated for reasons beyond
  `Sys.plan` (the `fail.smli` catalogue shows `ApplyClosure ... EagerF0`
  panics in this range); out of scope for #48, leave gated.

## Permanent divergences (record, don't fix)

- Any `Sys.plan` output containing `calcite(plan ...)` or
  `globalMarshal(...)` — rust has no Calcite backend.
- Cases where rust's optimizer compiles a query to a structurally
  different `Code` tree than morel-java (operator inlining differences).

## Decisions

- **Labels come from strum props.** `EagerFn::plan()` reads each
  builtin's `(p = structure, name = mlName)` props and applies the
  `"op "`-strip rule; `camel_to_dotted` and `operator_plan_name` are
  retired. First pass: audit that every native variant declares `p` and
  `name`, and add them where missing (this is a prerequisite, not
  optional).
- **Attempt the native `hybrid.smli` fallbacks.** Fix D must render the
  `group`/aggregate sink (which currently panics) so the native
  `max`/`min`-fallback cases — `from(... group(... collect(get(name
  max))))`, no `calcite` node — can be enabled. Only the genuinely
  Calcite-pushed cases (`calcite(...)`, `globalMarshal(...)`) stay gated
  as permanent type-E divergences.
- This doc lives in `plan.md`.
