# Migrate morel parser from pest to lalrpop

## Background

morel-rust uses [pest](https://pest.rs/) (PEG, with `pest_consume`) for the Morel parser. The Datalog port (#323) introduced [lalrpop](https://lalrpop.github.io/lalrpop/) as an experiment. Should the Morel parser migrate too?

## Measurements

| Component                | Source LOC | Release binary |
| ------------------------ | ---------: | -------------: |
| Morel pest grammar       |        586 |              — |
| Morel parser driver      |      2 581 |      434.5 KiB |
| Morel AST                |      1 739 |      195.3 KiB |
| **Morel parser + AST**   |  **4 906** |  **629.9 KiB** |
| Datalog lalrpop grammar  |        199 |              — |
| Datalog parser driver    |        237 |       31.3 KiB |
| Datalog AST              |        259 |        5.3 KiB |
| **Datalog parser + AST** |    **695** |   **36.6 KiB** |

Per-line compiled cost: pest ≈ 740 B, lalrpop ≈ 144 B (~5×). Release binary 7.3 MiB; `.text` 3.6 MiB.

## Pros

- **Binary size** — extrapolating gives ~456 KiB vs current 630 KiB (~27% / 170 KiB saved). Rough: lalrpop tables grow super-linearly with conflicts.
- **Stack usage** — pest is recursive descent; deeply nested `let`/`case`/`from` can stack-overflow. lalrpop uses heap stacks, bounded only by memory. **Strongest argument.**
- **Speed** — lalrpop LR(1) typically 2–5× faster than pest (single pass, no backtracking). Needs a Morel benchmark.
- **Consolidation** — Datalog already uses lalrpop; drop one parser generator from the build.

## Cons

- **LR(1) grammar surgery.** ML-family languages fight LR(1):
  - Postfix dispatch `x.f y` (field vs method) — pest uses `expr_unary_arg` lookahead (parser.rs:225–238); LR(1) needs duplicated non-terminals.
  - 13-level precedence cascade with `over` at fractional 7.5 — needs a wrapping non-terminal.
  - Function application by juxtaposition `f x y` competes with infix ops at the same precedence — forces a separate `aexpr` non-terminal.
  - Pattern/expression overlap — `(x, y)` is a pattern in `fun f (x, y) = ...`, expression elsewhere; needs separate non-terminals.
- **Nested block comments** `(* outer (* inner *) outer *)` — regex tokens can't match nesting. Need a custom lexer (`extern { type Token = ...; }`) or a preprocessing pass (loses span fidelity).
- **Error messages** — pest auto-emits `expected expr_unary at line 5, col 12`; lalrpop emits `unrecognized token ',' expected one of "=", "->", ...`. Recovering pest quality needs a custom formatting layer.
- **Conflict debugging** — PEG picks first match; LR(1) shift-reduce/reduce-reduce conflicts can be opaque without `lalrpop --report`. Cost is during migration, not after.
- **Build cost** — `build.rs` codegen produces 10K+ lines; slow incremental rebuilds on grammar changes.

## AST and Span compatibility

**Both preserved unchanged** — migration touches the parser, not its outputs.

- AST nodes are plain types; pest builds them via `pest_consume::match_nodes!`, lalrpop builds them in action blocks (`Expr: Expr = { <l:@L> <a:Expr> "+" <b:Term> <r:@R> => ... }`). Same AST, different construction site.
- `Span { input: Rc<str>, start: usize, end: usize }` maps 1:1 onto lalrpop's `@L`/`@R`. Thread `Rc<str>` in via `grammar(input: Rc<str>);` or a closure-captured action helper.
- Delete `Span::make` (ast.rs:56) and `Span::to_pest_span` (ast.rs:102); keep `union`, `merge`, `sum`, `code`, `start_pos`.
- External pest usage outside the parser: ~7 lines.

## Recommendation

Migrate, but spike the hard cases first:

1. Skeleton for the 13-level precedence cascade with `over` at 7.5 — no unresolved conflicts.
2. Postfix-dispatch lookahead — encodable without grammar explosion.
3. Custom lexer for nested block comments and the keyword/identifier disambiguation pest does atomically.
4. Benchmark parse time and binary size on `tests/script/*.smli`.
5. Error-message quality on malformed inputs.

If 1–3 fall out cleanly, the rest is mechanical. If any are nasty, savings don't justify a fragile parser.

## Out of scope

- `unifier.pest` — small, works fine.
- AST surface changes — separate issue.
- Pretty-printer — operates on `&Expr`, untouched.

## References

- `src/syntax/morel.pest` (586 lines), `src/syntax/parser.rs` (2 581), `src/syntax/ast.rs` (1 739)
- `src/datalog/grammar.lalrpop`, `src/datalog/parser.rs` (35 lines around generated code) — reference lalrpop setup

## Execution plan

Phased migration with a go/no-go gate after the spike. Each phase ends with `fullMake --no-clean` passing, a commit, and an update to this section before moving on.

### Phase 0 — Spike (go/no-go gate)

Throwaway lalrpop grammar + lexer skeleton, no AST construction, exercising only the LR(1)-hostile cases:

1. **Precedence cascade with `over` at 7.5.** All 13 levels including unary `~`, right-assoc `::`/`@`, and `expr_application = expr_unary expr_unary_arg* trailing_method_call*` (morel.pest:225–227). Zero conflicts under `lalrpop --report`.
2. **Postfix dispatch.** `id_postfix_chain` (morel.pest:233–234) + `trailing_method_call` (morel.pest:238–239). Test cases: `cs.complement ()`, `cs.complement ().complement ()`, `f x.y (z)`.
3. **Custom lexer skeleton** (`extern { type Token = ...; }`) handling nested block comments, keyword-vs-identifier atomicity, `~`-prefix lookahead for negative literals vs unary op.

Output: `spike.lalrpop` + lexer prototype + conflict/state-count table. **Decision point:** if any of (1)–(3) is fragile, stop and report.

### Phase 1 — Production lexer

Hand-written lexer (logos preferred). Tokens emit `(usize, Tok, usize)` triples. Must handle:

- Skipped: whitespace, line comments (morel.pest:21), nested block comments (morel.pest:22).
- All 55 keywords (morel.pest:26–82) with `!(alnum|_|')` lookahead.
- Identifiers (unquoted + backtick-quoted with `` `` `` escape), record selectors `#foo`, type vars `'a`, naturals, integers, reals, scientific notation, string literals with full escape set (parser.rs:2100–2146), char literals `#"x"`.
- Negative-number lookahead: `~` is `NEG_INT_LIT` / `NEG_REAL_LIT` only when followed by digits with no space; otherwise emit `TILDE`. Mirrors morel.pest:243's `!literal ~ "~"`.

Independent of the parser and unit-testable alone.

### Phase 2 — Grammar port

Mechanical port of morel.pest rule-by-rule into `src/syntax/morel.lalrpop`, building the existing AST in action blocks. Order: declarations → types → patterns → atoms → expressions (deepest precedence first) → top-level statement. Patterns and expressions stay as separate non-terminals.

Pass `input: Rc<str>` via `grammar(input: Rc<str>);`. Action blocks construct `*Kind` with `Span { input: input.clone(), start: l, end: r }` from `<l:@L> ... <r:@R>`. Keep the three entry-point signatures unchanged: `parse_statement`, `parse_unadorned_statement`, `parse_type_scheme` (parser.rs:45–79).

### Phase 3 — Grammar expansion (bulk of remaining work)

Extend `src/syntax/morel.lalrpop` until every `.smli` statement parses to an AST equivalent to pest. Driven by walking the `tests/script/*.smli` corpus and the existing pest tests, adding rules one feature at a time so we keep finding lalrpop conflicts early.

Order (each row = one small commit, fullMake passes between):

1. **Records and `case`/`fn`.** Add `RecordExpr`, `case ... of`, `fn ... =>`, `MatchList`. The `if`/`let` placement learning applies: keep `case`/`fn` at the top-level `Expr`, not inside `Atom`.
2. **Type annotations.** `<e>:<t>` plus the `Type` cascade (`FnType` → `TupleType` → `ApplyType` → `AtomicType`).
3. **Full pattern grammar.** `ConsPat`, `AsPat`, `ConstructorPat`, `RecordPat`, `ListPat`, `TuplePat`, `LiteralPat`, `AnnotatedPat`. Then upgrade `ValBind` to use `Pat` and add `and` chains.
4. **`fun`/`type`/`datatype`/`signature` decls.** Includes `Spec`, `ValDesc`, `TypeDesc`, `DatatypeDesc`, `ExnDesc`. Watch for `and` re-use as both decl chain separator and the keyword in `andalso`.
5. **`over` operator and decl.** `over` as infix at 7.5 (right-assoc tight RHS per spike), plus `over <id>` as a top-level declaration. Same-token disambiguation by leading position.
6. **`#foo` record selectors, `'a` type vars, `` `quoted` `` identifiers.** Wire the lexer's existing tokens into the grammar.
7. **Op section `op +`, `op ::`, ...** `OpSection` with the operator-name table.
8. **`current`/`elements`/`ordinal` keyword atoms.**
9. **Relational queries: `from`/`exists`/`forall` + steps.** The biggest remaining piece. Steps: scan, where, yield, skip, take, order, through, group, group-compute, union/except/intersect (with optional `distinct`), join, distinct, unorder, into, compute, require. Watch for lalrpop state count — may need to break this into multiple commits if it triggers the same blowup that scuttled the first Phase 2 attempt.
10. **`TypeSchemeTop` entry point.** `forall N type` for built-in signatures.

The full draft from the first Phase 2 attempt is at `/tmp/morel.full.lalrpop.draft` outside the repo — useful as a reference but should not be pasted in wholesale.

Gate for moving to Phase 4: every `.smli` file parses through the new parser and produces an AST whose `Display` matches what pest produces.

### Phase 4 — Cutover and Span cleanup

- Swap callers in `src/shell/main.rs:896`, `src/compile/type_parser.rs:34,47`, `tests/unparse.rs:24` from `crate::syntax::parser` to `crate::syntax::lalr_parser`.
- Replace `pub type ParseError = pest::error::Error<Rule>;` (parser.rs:33) with the lalrpop wrapper already in `lalr_parser.rs`. Expose a `line_col` accessor that `Span::from_line_col` consumes (shell/main.rs:898).
- Delete `Span::make` (ast.rs:56) and `Span::to_pest_span` (ast.rs:102).
- Refactor `compile/span.rs::from_pest_span` to take `(input: &str, start: usize, end: usize, base_line)` directly. Update the 25+ call sites in `src/compile/resolver.rs`, `src/compile/type_resolver.rs`, `src/shell/main.rs` to drop the no-op `to_pest_span()`→`from_pest_span()` round trips.
- Delete `pest_ascii_tree` usage in parser.rs:2206–2213 (`assert_parse_tree`); replace dependent tests with assertions on the AST `Display` form.
- Update tests that depend on `Rule::X` (parser.rs:2169–2204).
- Delete `src/syntax/spike.{lalrpop,rs}` (throwaway, served its purpose).

### Phase 5 — Benchmark & validate

- Full `tests/script/*.smli` suite passes unchanged via the new parser only.
- Add a `cargo bench` over the 39 `.smli` files; compare to baseline (pest is still in tree at this point for A/B comparison).
- `cargo bloat --release`; compare to the 629.9 KiB baseline.
- 5 hand-crafted malformed inputs; pest vs lalrpop error messages side-by-side. Decide whether a custom error-formatting layer is needed before Phase 6.

### Phase 6 — Remove pest

- Delete `src/syntax/parser.rs` (the pest version).
- Drop `pest`, `pest_consume`, `pest_ascii_tree` from `Cargo.toml`.
- Delete `src/syntax/morel.pest`.
- Record measured binary/parse-time delta here.

### Out of scope (reaffirmed)

- `src/unify/unifier.pest` (51 lines) — stays on pest.
- AST surface changes.
- `src/datalog/` — already lalrpop.

## Status

**Migration stopped 2026-05-18.** See "Decision: stop the
migration" below for reasoning, and "Grammar ambiguities vs LR(1)
limitations" for the full categorisation. Regression tests for
the three genuine ambiguities live in `tests/ambiguity.rs`.

Pre-stop progress (record only — does not get merged):

- [x] Phase 0 — Spike (see findings below)
- [x] Phase 1 — Production lexer (`src/syntax/lexer.rs`, 29 tests)
- [x] Phase 2 — Grammar port (subset; see Phase 2 notes below)
- [~] Phase 3 — Grammar expansion (steps 1-3 of 10 landed; step 4 hit the wall and was rolled back)
- [ ] Phase 4 — Cutover and Span cleanup
- [ ] Phase 5 — Benchmark & validate
- [ ] Phase 6 — Remove pest

## Phase 0 findings

Spike in `src/syntax/spike.{lalrpop,rs}` — 18/18 tests pass after the
restructure described below. Branch: `43-lalrpop`, commit
[Phase 0 spike].

### What works cleanly

- 13-level precedence cascade, iterative form (`<head> <(op tail)*>`
  rather than left-recursion). Left-recursive precedence rules tripped
  spurious shift/reduce conflicts because lalrpop's lane-table
  algorithm merges lookaheads across precedence levels; the iterative
  form (which is what `morel.pest` already uses) avoids this.
- Right-assoc `::` and `@` via collect-then-reverse in the action
  (mirrors `parser.rs:269-300`).
- Postfix dot on the leading expression (`PostfixExpr`) — greedy chain
  on any atom.
- Trailing-method `.label arg` on a built-up application — works as
  long as it requires preceding args (which matches the morel.pest
  semantic; see below).
- Tuple/paren atom — once the empty-alt CommaTail was replaced with a
  variant-per-form rule, no conflicts.

### One hard case the LR(1) grammar can't represent

The pest pattern `f x.y` — where `.y` is a postfix chain on the arg
`x`, giving `(apply f (dot x y))` (morel.pest:233-234,
`id_postfix_chain`) — is **genuinely ambiguous in LR(1)** with the
trailing-method rule. After `f x .`, the parser must decide between:

  (a) Extend the IdChain inside arg `x` (PEG/pest greedy behavior).
  (b) End the arg, reduce to AppliedExpr, treat `.` as the start of a
      trailing method on `Apply(f, x)`.

Both are valid parses; one-token lookahead can't choose. The pest PEG
resolves by ordered choice. morel-java (`MorelParser.jj:70`) uses a
mutable `inArg` flag plus multi-token `LOOKAHEAD({...})` semantic
predicates. lalrpop has neither.

The spike grammar compiles by dropping `id_postfix_chain`, which
means `f x.y` no longer parses (user must write `f (x.y)`).

**Mitigation: lexer trick.** A grep of `tests/script/*.smli` shows
that real Morel code never puts whitespace between an identifier and
`.label` in a postfix chain — only license headers and prose comments
do. So Phase 1's custom lexer can emit `x.y.z` as a single
`QUALIFIED_IDENT` token when there is no intervening whitespace.
Then `f x.y (z)` lexes as `f QID(x.y) (z)` — no `.` for the parser
to decide on, and `(apply f (dot x y))` falls out trivially. The
trailing-method rule continues to see `.` only when there IS
whitespace, distinguishing `cs.complement ().complement ()` (chain)
from `cs.complement().complement()` (different lex).

Cost: a one-line user-visible rule change ("no spaces inside a
postfix dot chain"). morel.pest currently allows them
(`postfix_tail = ${ "." ~ WHITESPACE* ~ label }`) but no code uses
the freedom.

### Other deliberate divergences

- `over` (precedence 7.5): pest grammar lets the RHS be a full `expr`
  (morel.pest:214). That creates shift/reduce conflicts with every
  higher precedence. We encode `over` as right-associative at its own
  level — equivalent on every input the pest action handles, since
  `parser.rs:366-373` only matches the single-binary-`over` case.

### Decision recorded

**Option 2 chosen** (2026-05-18): no lexer trick. Users must write
`f (x.y)` instead of `f x.y`. Affected `.smli` tests will be updated
in Phase 4. The grammar drops the arg-position `.label` chain rule
entirely; whitespace inside `.` chains remains as flexible as pest.

## Phase 1 notes

Lexer at `src/syntax/lexer.rs`, built on `logos = "0.16"`. 29 unit
tests cover every token category and the trickier edge cases.

- Nested block comments use a callback (`skip_block_comment`) that
  scans the remainder manually — regex can't recognize balanced
  delimiters. EOF mid-comment surfaces as
  `LexError::UnterminatedBlockComment` via a sentinel variant.
- `~`-prefix numerics (`~5`, `~3.14`, `~6.02e~23`) are single tokens
  by virtue of the regex matching the longer span; `~ 5` (with
  whitespace) lexes as `Tilde` then `IntLit`. Mirrors morel.pest:243.
- `Ident` has `priority = 1` so every same-length keyword wins the
  tie. Without this, single-letter keywords like `o` (morel.pest:116)
  collide with the identifier regex.
- `_` is `Underscore` (wildcard); pest's identifier rule disallows a
  leading `_` so `_x` lexes as `Underscore + Ident(x)`.
- The lexer wraps logos into the `(usize, Tok, usize)` triple
  iterator that lalrpop's custom-token mode expects (Phase 2).

## Phase 2 notes

Grammar at `src/syntax/morel.lalrpop`; parser entry points at
`src/syntax/lalr_parser.rs`. 19 unit tests pass, including a parity
check that diff-compares the lalrpop AST against pest for a handful
of inputs.

### Scope (intentional subset)

Landed: arithmetic, comparison, logical, cons/append operators;
function application; unary negation; `if`/`let`; `val [rec]` decls
with single identifier pattern; tuples; lists; literals; parens.

Deferred to a follow-up commit (preserved as a draft at
`/tmp/morel.full.lalrpop.draft` outside the repo): records, `case`,
`fn`, type annotations, full pattern grammar (cons, record, list,
ctor, `as`), `fun`/`type`/`datatype`/`signature` decls, relational
queries (`from`/`exists`/`forall` + steps), the `over` operator,
type-scheme entry point. These will go in piece-by-piece in Phase 4.

### Three grammar lessons learned

1. **Iterative tail with `*` macro, not explicit `Empty | Recursive`.**
   The Phase 0 spike worked because it used `<h:X> <r:("op" <X>)*>`.
   Re-encoding as `<h:X> <r:Tail>; Tail = empty | "op" X Tail`
   surfaced shift/reduce conflicts (the empty alt's lookahead leaks
   into adjacent precedence levels). lalrpop treats `*`/`+` macros
   specially.

2. **`if`/`let` cannot be atoms in LR(1).** Morel-pest allows
   `f (let val x = 1 in x end)` without parens because PEG is
   greedy; in LR(1) it creates a dangling-else-like ambiguity
   between `f (let ... end)` and `(f let) ...`. The grammar places
   them at top-level Expr only; users parenthesize to apply.

3. **First grammar draft hit lalrpop state explosion.** A complete
   port covering ~150 morel.pest rules ran lalrpop for 7+ minutes
   without finishing. The fix was scope reduction, not algorithm
   tuning — lalrpop's lane-table works fine on a tighter grammar
   that compiles in ~15s.

### `grammar` parameter

`grammar<'input>(input: &'input Rc<str>);` — passed by reference so
the same `Rc` can be cloned into many `Span`s without being moved.
The first attempt (`grammar(input: Rc<str>);`) produced 98 "use of
moved value" errors in the generated code.

## Phase 3 progress and wall

Three sub-steps landed; step 4 attempt was rolled back.

### What works (committed)

* **Step 1** (records, case, fn): labeled-only records (no anonymous
  fields, no `{e with ...}`); `case`/`fn` at top-level Expr only.
* **Step 2** (type annotations + Type cascade): `e : t` annotations
  on parenthesized atomic types; full Type cascade FnType →
  TupleType → ApplyType → AtomicType worked at this commit.
* **Step 3** (pattern subset): wildcard, identifier, literal,
  `IDENT as <atomic>` (non-recursive RHS), tuple, cons. Constructor
  patterns, list patterns, record patterns, and `pat : type`
  annotations all deferred.

### What broke step 4

Adding `fun`/`type`/`datatype`/`sig`/`exception` keywords and
`FunDecl` with multi-arg pattern lists pushed lalrpop's lane-table
past what it can resolve. The same `ApplyType (*) IDENT` and
`TupleType (*) "*"` shift-reduces that the earlier commits dodged
came back, plus new ones in `ValDecl`/`FunDecl` `and`-chains and
`FnType` `->` recursion. Every "fix" exposed another conflict
elsewhere. Reverted step 4 entirely.

The grammar appears to have crossed a size threshold where lalrpop's
default conflict-resolution algorithm can no longer separate states
cleanly. Beyond this point, each new feature requires either:

* A language-level user-visible restriction (parens here, no
  chaining there).
* A grammar-level inlining or precedence trick that lalrpop may or
  may not support.

### Cumulative user-visible restrictions

By step 3 the lalrpop parser already requires:

* `f (x.y)` instead of `f x.y` — Phase 0 finding.
* `f (let val x = 1 in x end)` and `f (case x of ...)` — `if`/`let`/
  `case`/`fn` cannot appear as Atom; parens required to apply.
* `(e : t)` for annotations, not bare `e : t`.
* `(e : (int -> int))` for compound-type annotations (extra parens).
* `{x = x}` instead of `{x}` for anonymous record fields.
* No `{e with field = val}` syntax.
* No list patterns `[a, b]`.
* No record patterns `{x = pat}`.
* No constructor patterns `Leaf x` (would-be ctors parse as bare
  identifier).
* `case` body's `IDENT as p` requires `p` to be atomic (so nested
  cons in an `as`-pat needs another wrapper).

Step 4 would add: single-bind `val`/`fun` only (no `and`); fun
without result-type annotation; no `type`/`datatype`/`sig` decls.

### Decision: stop the migration

**Decided 2026-05-18.** Keeping pest. The lalrpop migration is
abandoned on branch `43-lalrpop`. The grammar work and its findings
remain in tree (and in this document) as a record; nothing merges
to main.

Recap of the gate from the original plan:

> If any are nasty, savings don't justify a fragile parser.

Three of the conflicts ARE nasty (and inherent to the language —
not parser-tool-specific). Most of the rest are LR(1) algorithmic
limitations, not real ambiguities, but they still cost
user-visible language changes to dodge in lalrpop because the
tool has no `LOOKAHEAD(k)`, `inline`, or semantic-predicate
escape hatch strong enough.

The .smli corpus passes against the pest parser today; the
do-nothing option preserves morel-rust's surface syntax
compatibility with morel-java.

## Grammar ambiguities vs LR(1) limitations

The conflicts encountered during the migration attempt fall into
two qualitatively different categories. **Same word, very
different problems.**

### A. Genuine grammar ambiguities

Same input string admits two valid parse trees. The grammar
itself doesn't pick one. No amount of lookahead — not LR(k), not
GLR, not LL(∞) — can resolve these without a tiebreaker rule
imposed *outside* the grammar (e.g., ordered choice in a PEG,
semantic predicates in JavaCC, or a written-in-the-language-spec
convention like SML's "innermost match owns the `|`").

Every parser implementation — pest, lalrpop, JavaCC,
hand-written — has to commit to a convention for each of these.

Each genuine ambiguity has a regression test in
`tests/ambiguity.rs` that pins down which parse Morel produces
and documents what the alternative parse *would* have produced.
Where SML/NJ has the same ambiguity, the test references its
behaviour.

| # | Input | Parse A (chosen) | Parse B (rejected) | SML/NJ |
| --- | --- | --- | --- | --- |
| A1 | `f x.y (z)` | `Apply(Apply(f, x.y), z)` | `Trailing(Apply(f, x), y, z)` | N/A — Morel-specific extension |
| A2 | `if a then b else c d` | `If(a, b, Apply(c, d))` | `Apply(If(a, b, c), d)` | Same as A — verified |
| A3 | `fn p => fn q => 1 \| r => 2` | inner fn owns `\| r => 2` | outer fn owns `\| r => 2` | Same as A — verified |

A1 is unique to Morel because Standard ML has no postfix `.field`
syntax — it uses prefix `#field`. The chosen resolution mirrors
the PEG-greedy "argument absorbs the chain" rule already in
`morel.pest:225-239` and `MorelParser.jj:835-911`.

A2 and A3 are classic ML dangling-`X` ambiguities. SML/NJ resolves
both by making the inner / right-most construct greedy; Morel does
the same. Verified by running both in `sml` and comparing.

### B. LR(1)/LALR(1) algorithm limitations

These look like conflicts but are *not* grammar ambiguities. Each
input has exactly one valid parse tree. The grammar is
unambiguous. The problem is that LR(1) with one-token lookahead
(or LALR(1)'s extra state-merging) can't *decide* which
production to use at the point it must commit.

Pest, JavaCC, hand-written recursive descent, GLR — all handle
these natively because they have more flexibility (PEG's ordered
choice, JavaCC's `LOOKAHEAD(k)` with arbitrary `k`, RD's
arbitrary peek, GLR's parallel parses with later commit).
Lalrpop's lane-table can resolve *some* of these (it did so for
the smaller Phase 2 grammar), but the resolution power isn't
enough once the grammar grows past a threshold.

Each B-class problem below names the input that triggers it and
which two productions lalrpop confused.

#### B1. Anonymous vs labeled record field

```
{ foo }      → Record(None, [Anonymous(Identifier "foo")])
{ foo = 1 }  → Record(None, [Labeled("foo", 1)])
```

After `{ IDENT`, lookahead `=` says labeled, `}` says anonymous.
Each input has one parse. lalrpop blocks because the
`Atom → IDENT` reduction has `=` in its FOLLOW set (since `x = y`
is a valid comparison expression in some other context), so it
can't tell whether to reduce-then-comparison or shift-as-label.

#### B2. `{e with field = val}` vs `{field = val}`

```
{ x = 1 }          → labeled-only record
{ x with y = 1 }   → copy x, update y
```

After `{ IDENT`, lookahead `with` says with-form, `=` says
labeled, `+`/`*`/etc. says with-form starting an expression. One
token decides. Unambiguous. Lalrpop fails because the LALR
state-merge across the two RecordBody alternatives loses the
discrimination.

#### B3. Type-application boundary: `(x : int list)` vs `f (x : int) list`

```
(x : int list)    → AnnotatedExpr where the type is App(int, list)
f (x : int) list  → apply (x : int) to `list` (then to nothing)
```

Both inputs have one parse. Lalrpop blocks at
`ApplyType (*) IDENT` because IDENT is in FOLLOW(ApplyType) when
the type appears in an Expr position (since Expr's apply chain
also takes IDENTs). The lookahead is the same token; the
context — "inside paren type" vs "outside as function arg" —
differs but LALR loses that distinction.

#### B4. Constructor with vs without type: `Red` vs `Pair of int`

```
datatype t = Red                  → bare ctor
datatype t = Pair of int          → ctor with type
```

After IDENT in a constructor binding, lookahead `of` is shift,
anything else is reduce. Unambiguous. Lalrpop fails because `of`
also appears in `case e of` and the LALR-merged state combines
both contexts' lookaheads.

#### B5. Multi-bind `val x = 1 and y = 2`

```
val x = 1            → single bind
val x = 1 and y = 2  → two binds in one decl
val x = 1; val y = 2 → two separate decls
```

After the first bind, lookahead `and` continues, `;`/`val`/etc.
stops. Unambiguous. Lalrpop fails because `and` is the prefix of
`andalso` and the val-decl's `and` follow conflates with the
expression context where `andalso` lives.

#### B6. `<head> <(op tail)*>` precedence pattern

The iterative-tail pattern that works fine on the small Phase 2
grammar (and matches `morel.pest`'s structure) develops spurious
shift/reduce conflicts at every precedence level once the
grammar grows. Cause: LALR(1) FOLLOW computation merging
lookaheads across all uses of a non-terminal. E.g., `AddExpr`
appears as the RHS of `*` in `MultExpr`, the LHS of `+` in
itself, inside `(...)`, inside `case _ of _ =>`, etc. The merged
FOLLOW union includes tokens from every position, producing
phantom conflicts inside the iterative tail.

### Migration-attempt user-visible restrictions (cumulative)

The lalrpop work-in-progress on this branch (commits 363cde5,
7ee9763, c5f8b32, 1b7e361, 1e81258, dd4118d, e1b038f) forced
*twelve* user-visible language changes to side-step the
B-category limitations. Each is a real divergence from
`morel.pest`:

1. `f x.y` requires parens: `f (x.y)` (A1 resolution choice).
2. `if a then b else c d` and `let val x = 1 in x end d` and `case ... of _ => x d` cannot apply the if/let/case directly; parenthesise to apply.
3. `e : t` annotations must be in parens: `(e : t)`.
4. Compound-type annotations need extra parens: `(e : (int -> int))`, not `(e : int -> int)`.
5. Anonymous record field shorthand `{x}` doesn't work; write `{x = x}`.
6. `{e with field = val}` copy-update form doesn't work.
7. List patterns `[a, b]` not supported in patterns.
8. Record patterns `{x = pat}` not supported.
9. Constructor patterns `Leaf x` parse as bare identifier `Leaf` only.
10. `IDENT as <pat>` requires `<pat>` to be atomic; nested cons in an as-pat needs another wrapper.
11. Single-bind `val` and `fun` only; no `and`-chained multi-bind.
12. No type annotation on `fun` result: `fun f x = e`, not `fun f x : t = e`.

This list is the real cost-of-migration number. Beyond these,
step 4 (fun/type/datatype/sig decls) was a rolling
whack-a-mole — every fix surfaced another conflict — and
relational queries (step 9 in the plan) were never attempted.
