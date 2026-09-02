# Checked types (#239) — propagation plan for morel-rust

Propagating the checked-types work from morel-java (`~/dev/morel.1`) into
morel-rust. Branch `239-check`.

## Sources

* Issue: <https://github.com/hydromatic/morel/issues/239> (closed by the
  java commit).
* morel-java `origin/main` head **`06f806b2` "Checked types (#239)"**, and
  the two commits below it.
* Design record: branch `julianhyde/239-check`, which is `origin/main` plus
  three markdown files and **no code difference** — `06f806b2` is the squash
  of its 92 commits. Read `plan.md` (1936 lines, the design), `squash.md`
  (how the branch was reorganized; mostly of historical interest) and
  `follow-up-issue.md` (what was deliberately deferred).
  Fetch with `git -C ~/dev/morel.1 fetch julianhyde 239-check`, read with
  `git show julianhyde/239-check:plan.md`.

## The queue

morel-rust is otherwise caught up with morel-java (last propagation
`c599a871`, #459). Exactly three java commits are outstanding, and they must
land in this order — M4 does not stand alone.

| | java sha | subject | size |
| --- | --- | --- | --- |
| **M1** | `4493439b` | Type a modified record as written, and build it in `Resolver` | 801+/341-, 3 src + `type.smli` |
| **M2** | `0f24b1b0` | Ground a record variable from constraints on its fields | 100+/52-, `Generators.java` + `such-that.smli` |
| **M4** | `06f806b2` | Checked types (#239) | 4560+/204-, 37 files, `check.smli` 1370 lines |

(M3 was #459, "A type alias should survive inference" — already propagated,
in nine parts. The numbering is java's; the gap is kept so references to
the design record line up.)

M1 and M2 are independent of checked types and each fixes a bug that exists
in morel-rust today. Do them first, as separate commits, exactly as java
did.

## What morel-rust already has

The #459 work is the foundation, and it is done:

* `Type::Alias(String, Rc<Type>, Vec<Rc<Type>>)` in `src/compile/types.rs`.
* An alias survives inference: `ALIAS_PREFIX = "$alias:"` terms in
  `src/unify/unifier.rs`, `head_reduce`, `weaken`, the `weakened` map, and
  `unalias_term`/`unalias_sequence` for looking through one.
* `var_pre_term_map` / `var_alias_map`, so a node's *written* type is
  recoverable, not just the (weakened) substitution. This is what a claim
  has to read; see "the single most important thing the sketch got wrong"
  in java's plan, phase 3.
* Rendering in source syntax (`nat (alias for int)`, `T22 bag`).
* `typeof` in `type` and `datatype` declarations (#463), and a datatype
  displaced by a `type` declaration (#429).
* `as` is already a reserved word in `src/syntax/morel.pest` (`_as`, for
  layered patterns), so the expression-level `as` costs no new keyword.
* `plan.md` at the repo root is exempt from `tests/lint.rs` (header and
  line-length checks), so this file may live here for the branch's life.

## M1 — Type a modified record as written

Java `4493439b`. A record with modifiers was desugared into nested `let`s
*before* it was typed, and the destructure at the front of each erased the
type of the record being modified, so `{pt replace x = 3}` where
`pt: point` lost `point`.

morel-rust has the same shape and the same bug. `desugar_modifiers` is at
`src/compile/type_resolver.rs:6919` and its doc comment says "Mirrors
morel-java's `desugarModifiers`". This is also the known #459 residue
recorded in memory: *"a record modifier over an aliased base types the
untouched fields too generally … the loss is in the desugaring, not the
look-through"*. M1 is the fix.

What to build:

1. A new `src/compile/record_modifiers.rs`, mirroring java's
   `RecordModifiers`: the rules deciding where each field of the result
   comes from — kept from the operand, assigned by a modifier, or taken
   from an `all` argument. One place, consulted by both the type resolver
   and the resolver, which is what keeps them in agreement.
2. `TypeResolver` applies each modifier to a map of field name to type
   variable, reading the operand's fields out of its **term by an action**
   — the same mechanism `#f e` uses — rather than by unifying the term with
   a record of variables. Unifying would meet an alias with a plain record
   and erase it. morel-rust already has the record-selector action from
   #459 part 4; reuse it.
3. `Resolver` builds the `let`s once the types are settled.
4. Two consequences to carry over: the unresolved-flex-record check can no
   longer be "a record still has modifiers" (they all do now), so collect
   unresolved records as they are found; and a `yield` step reads the
   fields it binds from the record's *type*, not from the expression.
5. Behaviour change to expect: a value a verb skips
   (`{r replace or skip j = e}` where `r` has no `j`) used to vanish with
   the desugaring and is now typed, so `1 + "a"` and an unbound name are
   errors there.

Tests: `type.smli` +9 lines from java. Also re-check the two `type-alias.smli`
lines listed in memory as "record modifier over an aliased base (2)" — they
should close here.

## M2 — Ground a record variable from constraints on its fields

Java `0f24b1b0`. `from p: {i:int, j:int, k:int} where p.i elem [0,1]
andalso p.j elem [2] andalso p.k elem [3..4]` reports `pattern 'p' is not
grounded`. No `check` anywhere; it is a plain query bug.

Target: `src/compile/generators.rs` (3107 lines; java's `Generators.java`
is the counterpart). Collect a collection constraint **per value it
generates** rather than one per pattern. Then the three things that fall
out, each a place the machinery had only been asked about one field:

* A `Range.contains` constraint must match a *field* of the pattern, not
  only the pattern, and must ask discreteness of the value being
  generated rather than of the pattern. A record is not discrete; its
  fields may be. Without this, `p.i elem [0..2]` cannot ground a field
  while `p.i elem [0,1,2]` can.
* Build the derived value at the *pattern's* type, not at a type deduced
  from its fields — otherwise `int * int` where `{i:int, j:int}` was
  wanted, and the group's key does not match its declared type.
* Joining the field generators wraps each scan's pattern in a tuple
  pattern, and a one-element tuple pattern throws. With one field there
  was no join, so nothing had wrapped anything before.

A tuple is grounded the same way, by its components.

Tests: `such-that.smli` +26 lines. Check whether the `such-that.smli`
`set("mode","validate")` bracket recorded in memory (tuple-type extent)
is affected.

## M4 — Checked types

Java `06f806b2`, 4560 added lines. Too big for one morel-rust commit; the
plan is nine, each green under `fullMake`. The order is the java plan's own
phase order, which was validated by the branch actually being built that
way.

### The design in one paragraph

`check` is a clause on a `type` declaration: `type nat = int check i => i
>= 0`. A checked type is an **alias that carries conditions**, and it is
**erased** — its representation is the base type's, and the condition does
not survive `unalias`, so everything structural (overload choice,
aggregation, printing) behaves as for the base. That makes widening free
and narrowing checked. The one invariant: *a condition is claimed only
where the type says so, and a check is inserted wherever a value flows into
a claim.* Type inference is unchanged; a second syntax-directed pass
(`Enforcer`) decides where the checks go. A condition must be **closed** —
only the value it is given and the standard basis — which is what lets a
checked type be interned like any other, two being the same type when their
conditions are textually equal.

### M4.1 — Syntax and type representation

* `src/syntax/morel.pest`: `check` clause in the type-bind rule; `as` and
  `asOpt` as alternatives in the `:` annotation loop (same precedence as
  `:`, left-associative). `asOpt` is a new reserved word. Java's split of
  `expression` into `expression`/`expressionNoCheck` is the trick that
  makes `int check i => i >= 1 check j => j <= 12` parse: a match body is
  parsed at the no-check level so `check` ends the match rather than being
  taken into it.
* `src/syntax/ast.rs`: `TypeBind` gains `checks: Vec<Fn>`; new `As` /
  `AsOpt` expression kinds. A clause is a **list of functions, one per
  clause, not a flat list of matches** — branches within a clause are
  alternatives, separate clauses are conjoined.
* `src/compile/types.rs`: `Type::Alias` gains a `checks` field. Its
  rendered form (java's `moniker`) is the name when it has one, and
  `body check <match>` when it does not.
* **Interning / type identity.** Java puts the *rendered* condition text in
  the alias key. morel-rust's alias term is `$alias:<name>` with arity 1
  (`unifier.rs:1962`), so a nameless checked type has nothing to key on.
  Decide early: synthesize a stable op name from the condition text, e.g.
  `$alias:` plus the rendered condition. Getting this wrong makes two
  distinct anonymous checked types unify.
* `src/shell/highlight.rs`: `check` and `asOpt` join the keyword set (the
  `MOREL_KEYWORDS` category added under #460).
* Reject a `check` on a **parameterized** type.
* The condition is type-checked as `base -> bool`.

Tests: the first ~120 lines of `check.smli` (declaration forms, repeated
clauses, non-exhaustive matches, destructuring, redeclaration identity).

### M4.2 — The `Constraint` exception and the internal operators

* `Constraint` joins `BuiltInExn` alongside `Subscript` (see
  `src/eval/list.rs:119` for the shape) and `General` in `lib/general.sig`
  / `docs/lib/general.md`.
* Three internal operators, all in the `$` structure and never written by a
  user:
  * `$check : bool * 'a * string * string -> 'a` — given the condition's
    result, the value, the type's name and the blame path, returns the
    value or raises `Constraint`.
  * `$require : bool * 'a * string * string -> bool` — the same, but
    returns `true`, so it can be a conjunct of the containing value's
    condition. This is what lets a message name and quote the *component*
    that failed.
  * `$attempt : bool * 'a * string * string -> bool` — returns the
    condition's result rather than raising, so `asOpt` can answer `NONE`.
    It still raises if evaluating the condition raised.
  Their types cannot be derived and are never checked; java gives them
  `unit`.
* A `Description` payload: `uncaught exception Constraint [~1 is not a
  valid nat]` — rendered without a value, unlike `Fail: no such file`.
  morel-rust's uncaught-exception rendering is in `src/shell/` and
  `src/eval/code.rs`; find the single place and add the variant.

### M4.3 — Closedness, and completing a non-exhaustive match

* **Closedness.** A condition may refer only to the value it is given and
  to the standard basis; a reference to anything the user declared is an
  error. Decide it **by the binding, not by the name**, so shadowing a
  basis name does not smuggle an environment in. (Java notes one residual
  hole here: it needs a built-in marker on `Binding`.)
* **Exhaustiveness.** Append `| _ => false` to a match that is not already
  exhaustive. Appending blindly would make the appended branch redundant in
  the issue's own three-branch example, and redundancy is an error. So:
  when match-coverage checking is disabled, append blindly; when enabled,
  call the coverage checker (`src/compile/pat_coverage.rs`, the SAT path)
  and append only if the match is not exhaustive. This must run **before**
  the general coverage pass, and it is a Core-level rewrite — which is why
  java does it in `Resolver`, not `TypeResolver`. The appended branch takes
  the position of the whole match and is never blamed.

### M4.4 — Narrowing at the simple sites

New `src/compile/enforcer.rs`, mirroring java's `Enforcer` (1001 lines,
itself extracted from `Resolver`). One belongs to each resolver and is
copied with it, because deciding closedness reads the environment and
compiling a condition converts an expression in it.

Sites: a binding, a function parameter, a function result, an ascription,
`as`, `asOpt`.

**The thing to get right:** every one of these reads the type *the user
wrote*, not the type inference deduced. Inference gives the meet, which for
a checked type is the base type, so a deduced type has no condition left.
`fun decr (n: nat) = n - 1` has type `int -> int`. morel-rust's
`var_pre_term_map` from #459 part 3 is the written-type source; java's
counterpart is `claimedPatType` / `claimedType` reading the `Ast.Pat`.

A parameter's check is compiled **inside** the function, so it travels with
the function value and fires even when called from polymorphic code that
knows nothing of `nat`.

`as` / `asOpt` typing rule is stated on erasures: well-typed if the
erasure of the target unifies with the inferred type of the operand.
Different erasures is an ordinary type error and needs no new code — the
unifier already names both types and says which is an alias. Elision is
**textual**, not entailment: `n as nat` is free, `k as nat` where `k` is
`int check z => z > 0` is not.

**A conversion displays the type it was asked for.** `i as nat` is `nat`
and `i asOpt nat` is `nat option`; the conversion is the record of what was
verified, so it must not be weakened away.

This is the one place where **morel-rust implements the corrected
behaviour rather than the behaviour of the java commit**. As committed,
`06f806b2` gives `int` and `int option`. The cause is in
`TypeResolver.deduceCastType`: the operand and the target share one type
variable, so the target's alias meets the operand's `int` and the #459 meet
rule weakens it; `asOpt` then wraps the weakened variable.

The fix is not to unpick that unification — the erasures must still meet —
but to add the conversion to the **written-type** path, which is exactly
what an annotation already uses. In java that is `deduceRealTypes` /
`realTypes` / `getRealType`; morel-rust mirrors it, added in #459 part 7
(`f2576bd3`). A `Cast` node joins the annotation and list cases there, and
reports `t` for `as` and `t option` for `asOpt`.

Julian has this fix in progress in the java working tree, uncommitted at
the time of writing (`TypeResolver.java` +22, `check.smli` +24/−11).
**Re-fetch and re-check before implementing**: it may land as a follow-up
commit or be folded into a rewritten `06f806b2`. If it has landed, this is
an ordinary propagation and the note above is history.

Ten `check.smli` lines carry the corrected types — `i as nat`,
`i asOpt nat`, `j asOpt nat`, `i - 1 as nat`, `(i : int) as nat`,
`3 asOpt odd`, `2 asOpt odd`, and the two section comments at lines 161 and
195. Until java commits its fix, `etc/check-convergence.py` will flag them;
that is expected and correct. `i as nat as int` stays `int` — the last
conversion is the one that decides — and `j asOpt int` stays `int option`,
because `int` is what was asked for.

### M4.5 — Composites

Records, tuples, lists and datatype constructors, followed to any depth.
Components are checked **before** the whole, so the message names the
innermost failure. Blame paths: `field empno`, `component 1` (numbered from
1, matching `#1`), `element` (no index — `List.all` offers none),
`argument of Box`.

The mechanism is java's `deepCondition`, which walks **two types in step**
— the claimed type, which keeps its aliases and so knows where the
conditions are, and the erased type, which the expressions being built are
typed with. A single walk builds a selector typed `nat`, which a predicate
typed `int -> bool` then rejects. A datatype may contain itself, so the
walk is a function applied to itself.

### M4.6 — Rejections

What is rejected is a condition on a function's **parameter or result**,
which would need a check at every call site. A condition on the function
type *itself* is given the function value and is checked like any other
(`type fnFalse = (int -> int) check c => false` raises). Where the
condition lands is decided by parenthesization. Message: "cannot claim",
which serves a binding and a parameter as well as a conversion.

Until this is rejected it is a silent hole: the "does this type carry a
condition" test only looks in positions a value can be checked at, so a
function type passes over and the claim goes unenforced. Add the rejection
in the same commit as the test that would otherwise pass vacuously.

### M4.7 — Record modifiers claim and inherit

Builds on M1. A modifier that **assigns** claims the type of the record it
modifies, and that claim is checked where it is made. A modifier that adds,
removes or renames cannot claim the type — the shape changed — but the
record's own condition may still be carried over.

New `src/compile/conditions.rs`, mirroring java's `Conditions` (233 lines):
given a map from each field of the original record to its name in the new
one, rewrite the condition to hold of the new record, or give up. Two
rewrites: `rename` (when every branch's pattern is an id) and `select`
(when the condition selects fields and there is one branch). Give up — and
therefore claim less, which is sound — when the condition uses the record
as a whole, or when the match is one this cannot rewrite. A condition that
depends on a removed or assigned field is dropped.

`lenient` says a field need not keep its type, so nothing is claimed of it.
A verb that skips assigns nothing, so the record is the one it was given.

### M4.8 — The planner

A scan over a checked type conjoins the type's condition into the query, so
a generator enumerates only conforming values rather than
generate-and-filter. This is the one site whose condition does **not**
raise: which values the type has is the question being asked, not something
claimed of a value in hand.

`src/compile/generators.rs` / `src/compile/from_builder.rs`. Mechanical
once M2 and the rest of M4 are in; the issue's `parity_pair` example is the
acceptance test.

### M4.9 — Tests, docs and convergence

* `tests/script/check.smli`: java's file verbatim, 1370 lines, ~448
  expected outputs. It is the bulk of the work's verification. Add the
  matching entry that `tests/lint.rs` requires for each `.smli` file.
* Deltas: `type.smli` +15, `type-alias.smli` +7, `misc.smli` +4,
  `built-in/sys.smli` +6 (the three `$` operators appear in `Sys.env`).
* `docs/reference.md` +63, `docs/lib/general.md` +7, `docs/lib/index.md`,
  `lib/general.sig` +6.
* `etc/check-convergence.py HEAD --java-repo ~/dev/morel.1 --verbose` must
  pass — pass `--java-repo` explicitly, its default is wrong.

Expect the gate to FAIL on `type.smli` and `check.smli` for the whole of
M4.1 to M4.8, as it did for the split #459 propagation. That is normal for a
split; it must pass at M4.9 — **except** for the ten conversion lines
described in M4.4, which stay divergent until morel-java commits its own
fix. Record them as a known divergence, with the reason, rather than
copying java's weakened types to make the gate green.

## Where this stands

The grounding fixes are on branch **`grounding`**, off `origin/main`, so
that they can go ahead of the checked-types work; `239-check` is
rebased onto it.

morel-java's `main` has moved past `06f806b2`: `fa512393` and `028cdbc2`
are checked-types follow-ups that morel-rust already satisfies,
`9d10a8c9` is a grounding test that is propagated here, and `927cf86d`
is unrelated.

Done, each green under `cargo test` + clippy + lint:

| commit | what |
| --- | --- |
| `28f66022` | **M1** a modified record is typed as written |
| `b3157c1a` | **M2** a record variable is grounded from its fields |
| `c93be349` | **M4.1** a type declaration may carry `check` conditions |
| `c7199b49` | **M4.2** a binding at a checked type is checked |
| `4be5b399` | **M4.3** a condition must be closed, and need not be exhaustive |
| `475883c1` | **M4.4a** a parameter and an ascription are checked |
| `3fa82274` | **M4.4b** `as` and `asOpt` |
| `586894f7` | **M4.5** composites: records, tuples, collections |
| `1446c56d` | a constructor's argument resolves against the aliases in scope |
| `70c3ef87` | **M4.5b** applying a constructor is a construction site |
| `2e20cd1f` | **M4.6** a claim written in full; a checked function type is rejected |
| `c95b855b` | a condition reached through a datatype is checked |

Everything probed against morel-java matches byte for byte -- messages,
blame paths and spans -- except the divergences listed below.

`etc/check-convergence.py` fails on `check.smli` (+1370), `type.smli`
(+15) and `type-alias.smli` (+7), which is expected until M4.9.
`built-in/sys.smli` and `datatype.smli` **converged** on the way.

## What is left

### M4.7 -- record modifiers

Two halves. The first is four statements that differ today:

```
{e replace empno = ~1};            (*) java raises; rust does not check
{e replace empno = 2};             (*) java `: employee`; rust `: {empno:int, ...}`
{e replace all {empno = ~1}};      (*) java raises; rust does not check
{e replace or skip hired = true};  (*) java `: employee`; rust `: {empno:nat, ...}`
```

A modifier that **assigns** claims the type of the record it modifies --
the field keeps its declared type, so the value must have it -- and the
claim is checked at the modifier, because nobody else wrote the type
down. `lenient` says the field need not keep its type, so nothing is
claimed. A modifier that adds, removes or renames cannot claim the type,
because the result has a different shape, and needs no check either:
every value it carries over was checked when it was put there. Every
modifier in a chain must leave the shape alone for the chain to claim
anything.

In morel-rust the shape-preserving case should give the result the
*base's* type variable rather than a record built from field variables,
so the alias survives; the assigned value is then checked against the
field's declared type rather than weakening it.

The second half is "a modifier inherits the record's own condition",
java's `Conditions`: a condition is carried across a change of shape
when every field it depends on survives, rewritten to name them as the
result names them.

```
{v0 extend c = 5};
> val it = {a=1,b=2,c=5} : {a:int, b:nat, c:int} check r => #a r < 10
{v0 remove a};      > val it = {b=2} : {b:nat}
{v0 remove b};      > val it = {a=1} : {a:int} check r => #a r < 10
{v0 rename z = a};  > val it = {b=2,z=1} : {b:nat, z:int} check r => #z r < 10
```

**The anonymous-checked-type plumbing is cheaper than this plan feared,
and was tried.** The `check_predicates` keying is not the obstacle: the
alias term's body comes from the *term*, not from `type_aliases`, so an
anonymous checked type needs only a generated name (`$check1`, which a
user cannot write) in `type_checks`, an `alias_term` over the record's
term, and a `Display` arm that writes body-plus-conditions when the name
begins with `$`. That much builds.

**The obstacle is that morel-rust has no AST walker.** Deciding whether
a condition can be carried over is java's `Conditions.selectsOnly`: every
use of the record must be a selection of a surviving field. That is a
read-only walk over an arbitrary expression, and `ExprKind` has some
forty variants with no `visit`. A *partial* walker is not an option: one
that misses a bare use of the record would carry a condition over that
does not hold of the new record, which claims more rather than less.
`rename` needs a shuttle as well, to rewrite `#a r` to `#z r`, and the
destructuring form needs one to build the `let` that java's
`Conditions.select` builds.

So the order of work is: an AST visitor and shuttle first (useful well
beyond this), then `selectsOnly`, then the two rewrites. `extend` and
`remove` need only the visitor; `rename` and a destructuring condition
need the shuttle.

A partial attempt is on `stash@{0}` (`m47b-partial`): the `Display` arm,
the generated-name counter, and `inherited_checks` down to the point
where the walker is needed.

### M4.8 -- the planner

A scan over a checked type conjoins the type's condition into the query.
The one site whose condition does not raise: which values the type has
is the question being asked. M2 built the grounding half already.

### M4.9 -- `check.smli`, and the divergences below

## Divergences to close

1. **An operator must drop the condition.** `fun decr (n: nat) = n - 1`
   is `nat -> nat` in morel-rust, `int -> int` in morel-java. An
   operator computes a value the type has not been shown to contain, so
   it drops the condition whatever it was applied to, and a unary
   operator drops it too. morel-rust's overloaded arithmetic carries the
   alias through. Affects `n + 1`, `~n`, `abs n`, `s * s`, `dbl`. A
   wrong displayed type, not an unenforced claim.
2. **A parameter's check is blamed a few characters late.** morel-java
   blames the whole `fun` clause (`f (n: nat) = n`, 1.5-1.19), morel-rust
   the match (1.8-1.19); and for `fn (n: nat) => ...` morel-java starts
   at the `(`. Same family as the #422 fix, for patterns.
3. **A condition that does not typecheck** reports `int vs bool` where
   morel-java says `bool vs int` -- the operand-order divergence #459
   left behind.
4. ~~**A conversion's type.**~~ **Settled.** morel-java committed the
   fix as `fa512393`, "A conversion should display the type it converts
   to"; morel-rust already agreed, including the cases that commit adds
   (`val n = i as nat` is a `nat`, `[i as nat, 0]` a `nat list`,
   `i asOpt nat` a `nat option`). `028cdbc2`, which pins that a chained
   conversion checks every step, also passes unchanged.

## Working rules

From `AGENTS.md` and prior propagations:

1. `git -C ~/dev/morel.1 fetch --all` **every session**, not once. Julian
   rewrites commits; check
   `git merge-base --is-ancestor <trailer-sha> origin/main` after a fetch.
   Pin every diff you apply with `git show <sha>:path`.
2. Move every changed `.smli` section **literally**, adding sections that do
   not exist. Where morel-rust cannot yet run one, bracket it in
   `set("mode","validate")` / `set("mode","evaluate")` with the text
   verbatim. Do not comment it out.
3. An **unbalanced** `set("mode", ...)` bracket does not fail the script
   test — only `tests/lint.rs` catches it, and its message reads
   `Redundant set("mode","validate")`, meaning *unclosed*, not
   *unnecessary*.
4. `cargo fmt`, then `/usr/local/bin/fullMake --no-clean`, then
   `etc/check-convergence.py`, then commit.
5. Commit subject = java's subject with `(#N)` rewritten to
   `(hydromatic/morel#N)`; body; then
   `Propagates hydromatic/morel#N commit <sha>`. The trailer regex is
   `[Pp]ropagates\s+\S*\s*commit\s+<sha>`, so "Propagates **part of** …"
   does not parse — use the plain form and say "part N" in the subject.
6. Do **not** `git add -A`: the repo root holds Julian's untracked scratch
   files, and committing them fails `cargo test --test lint`.
7. Two consecutive `(*) ...` line comments are a lint error; use a block
   comment.

## Risks, in the order they are likely to bite

1. **Anonymous checked types and term identity.** morel-rust keys an alias
   term on its name alone. Settle this in M4.1 (see above) or two unrelated
   anonymous conditions will unify.
2. **Written type vs deduced type.** The single most important thing java's
   own sketch got wrong. morel-rust has the machinery (`var_pre_term_map`,
   `var_alias_map`) but it was built for display, and a claim is a
   different consumer. Expect to widen it.
3. **`deepCondition`'s two-type walk.** Doing it with one type produces
   selectors typed `nat` that a predicate typed `int -> bool` rejects — a
   failure that looks like a unifier bug and is not.
4. **Erasure must reach everything structural.** morel-rust's `unalias`
   equivalents are scattered (`unalias_term`, `unalias_sequence`,
   `Type::Alias` matches in `types.rs`, `pretty.rs`, `tabular.rs`). A
   condition that survives one of them is a wrong answer somewhere far
   away.
5. **Size.** `check.smli` is 1370 lines of oracle-free expected output.
   Bring it over in the order its sections are written; each section states
   what it is about, and they follow the phases above.
6. **The java commit is not the specification.** `06f806b2` types a
   conversion as the meet rather than as what was asked for (see M4.4), and
   morel-rust implements the corrected behaviour. Where the java tree and
   the design record disagree, the design record wins, and `check.smli` is
   a *report* of what java does today — check it against
   `julianhyde/239-check:plan.md` before copying an expected output that
   looks wrong.

## Deferred (java deferred them too; do not chase)

* Constrained **function** types, and recovering a constraint that has
  reached a type variable. Both need type-directed dispatch, which #290
  needs too. Not soundness holes: the constraint is erased, so nothing is
  claimed.
* **Values from outside** (foreign rows). A claim over a Calcite-backed bag
  would walk it, turning a streamed query into a materialized one.
* Message quality, capture for a non-closed condition, `e check m` as a
  general expression form, `unchecked t`, `predicate t`, environment
  refinement after `assert`/`assume`/`prove`. All are logged in
  `follow-up-issue.md` on `julianhyde/239-check`.
* A `case` branch that **destructures** is not checked (the check goes on a
  name the pattern binds, and such a pattern binds none covering the whole
  value). A function parameter of the same shape *is* checked.
