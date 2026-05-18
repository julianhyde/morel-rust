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

- [x] Phase 0 — Spike (see findings below)
- [x] Phase 1 — Production lexer (`src/syntax/lexer.rs`, 29 tests)
- [x] Phase 2 — Grammar port (subset; see Phase 2 notes below)
- [ ] Phase 3 — Grammar expansion (10 incremental steps; gate: full `.smli` corpus parses)
- [ ] Phase 4 — Cutover and Span cleanup
- [ ] Phase 5 — Benchmark & validate
- [ ] Phase 6 — Remove pest

## Phase 0 findings

Spike in `src/syntax/spike.{lalrpop,rs}` — 18/18 tests pass after the
restructure described below. Branch: `46-lalrpop`, commit
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
