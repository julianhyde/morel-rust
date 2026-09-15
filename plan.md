# Relational tree (hydromatic/morel#449) — propagation plan for morel-rust

Branch `449-tree`. This work is **not for `main` yet**. Its first
purpose is to find bugs in morel-java's implementation by building a
second one against the same written contract: where the two disagree,
one of them is wrong, and the disagreement is cheap to find and dear to
reason about after the fact.

**Status, 2026-09-14: R1 to R9 are done.**
morel-java's `rel-tree.smli` at tag `449-tree.3` is copied across, and
**every plan in it is now morel-java's text byte for byte**, which is
the acceptance criterion in "The contract" below.

The findings log at the end has twenty-two entries, twelve of them from
the differential harness -- among them a wrong answer on `main` that no
test covered. **Thirteen are fixed**: five in the translator on this
branch, four on `main`, and four in morel-java itself. The harness asks
both implementations for the plan of 1,241 queries across the whole of
`tests/script`, and over the session they went from agreeing on 385 of
them byte for byte to agreeing on **508**.

## Start here: what the next session does

Read this section and the findings log at the end. The rest of this
file is why things are the way they are, and is worth reading when
something surprises you, not before.

### What R7 says, in one table

`etc/rel-diff.py` replays a `.smli` file in both shells and asks each
for `Sys.planOf` of every `from` statement as it goes. Over the 42
files of `tests/script`:

| | queries | |
| ---: | --- | --- |
| 508 | agree | byte for byte |
| 378 | differ | 99 of them fully accounted for by four rewrites |
| 247 | morel-rust declined | the translator turned the query down |
| 0 | morel-java declined | its own invariant, and now checkable |
| 19 | morel-rust answered and morel-java did not | all but three in `overload.smli` |
| 88 | neither compiled | the corpus's error cases |
| 1 | both declined | |
| 0 | killed a shell | |

That is against **morel-java with findings 5, 10, 17 and 20 fixed**
(`~/dev/morel.2` on `449-tree`, `240129bb`); run the harness with
`--java ~/dev/morel.2`. Against morel-java as it was, the same corpus
gave 503 agreeing, 192 rust declines, 16 java declines and 55 "both
declined".

**The decline column was wrong about 54 queries**, which is finding 20's
point and the best argument for having fixed it. A node-free tree and a
decline were the same text, so the harness read 54 of morel-java's trees
as declines and called them "both declined"; they are morel-rust's
declines alone. morel-java now declines nothing, which is what
`RelShadow` asserts and what no reader could check before.

The session started at 385 agreeing, 491 differing, 177 declined and
five shells killed. R9's five translator fixes bought 33 agreements and
17 declines -- every one of the 17 a query reading `current` or
`ordinal` that used to print a tree naming them -- and R8's four `main`
fixes bought 84 more agreements and emptied three of the seven rewrite
classes. Four queries came back from fixing the harness itself, and
five more agreements from fixing morel-java.

A difference is *accounted for* when a rewrite makes the two texts
equal exactly, so the classes are measurements rather than guesses.
Three of the seven are now empty; what is left is morel-java's to
answer, not ours:

| cases | class |
| ----: | ----- |
| 58 | morel-java prints the function an aggregate desugars to, `fn $col => count (#fromList Bag $col)` |
| 48 | a group of one field: morel-rust's element is the field, morel-java's the record, and `spec.md` §3 says ours |
| 22 | the two break a long line in different places |
| 3 | `only` written bare where the query wrote it and qualified where the compiler supplied it |

The last is small and is a finding of its own: morel-java writes a
built-in as the resolver *found* it, so `only` is bare in a `yield`
that wrote it and `#only Relational` where `compute` supplied it.
morel-rust's Core keeps the resolved function and not the name it was
written under, so it cannot tell the two apart.

That leaves 279, and `--kind unexplained` groups them by the first line
on which the two disagree. Every row this table used to have is now
empty but one: **141 are finding 9**, grounding landing on different
sides of the printer, and nearly all of the remaining 138 is finding
15, the two front ends normalizing a query differently before a tree is
ever built. Neither is a translator bug, and no work on the translator
will close either. They are the whole of what is left.

### The order for the next session

1. **Send morel-java's four fixes on.** Findings 5, 10, 17 and 20 are
   fixed in `~/dev/morel.2` on `449-tree` (`240129bb`), each with a
   test that fails without it, and `java-findings.md` says what each
   one was. They are not on `~/dev/morel.4`, where the 449 work is
   happening, so someone has to move them. Until then the harness needs
   `--java ~/dev/morel.2` to see the numbers in the table above.
2. **Findings 9 and 15, which are the whole of what is left**, and
   both are conversations rather than changes: 141 and 138 of the 279
   differences the rewrites do not explain. Grounding lands on
   different sides of the printer, and the two front ends normalize a
   query differently before a tree is ever built -- so for those
   queries the two translators are not even given the same query. The
   plan text cannot be a cross-implementation contract across either,
   and agreeing where `Sys.planOf` sits in the pipeline is worth more
   than any fix on this list.
3. **Finding 4** (`exists`, `ordinal`, `current`) last, and R7 has
   shifted it: morel-java's `ordinal` plans carry `$ordinal` as a free
   name that nothing defines, one of them crashes its printer
   (finding 10), and finding 13 showed morel-rust building the same
   broken tree wherever its decline did not reach -- which is now 17
   more declines rather than 17 more wrong trees. Declining looks
   better than matching, but it is still morel-java's call.
4. **Not the lowering.** morel-java's step 2 built `RelLowerer` (949
   lines) and the flip; `spec.md` does not freeze the lowered form, so
   a second lowering would be checked against nothing. It is worth
   doing when the tree is what executes, and that is not what this
   branch is for.

### What the translator still declines, and why

The shadow translates 1,312 of the corpus's 1,741 queries and declines
429. Reading that tally is what buys coverage -- it is what took the
translator from 958 to 1,338 in an afternoon -- and until now there was
no way to read it without editing `tests/smile.rs`, because it prints
only when the assertion fires. There is now:

```
MOREL_SHADOW_TALLY=1 cargo test --test smile -- --nocapture
```

| declines | reason |
| -------: | ------ |
| 200 | a query that tests for existence |
| 137 | a query that reads `ordinal` or `current` |
| 23 | a tree whose type is not the query's |
| 23 | a query whose row is not a record |
| 13 | a scan source over the enclosing row |
| 11 | a scan over something that is not a collection |
| 11 | a group's part that has no name |
| 4 | a query whose row names an unbound binder |
| 3 | a `let` that binds a function |
| 2 | a scan pattern that is not a name or a tuple |
| 1 | a group's parts that are not a record |
| 1 | a correlated outer join |

**337 of the 429 are finding 4** -- `exists`, `ordinal` and `current`,
which are morel-java's call and not coverage we are missing. Another
34 are grounding: the 11 ungrounded scans, and 23 of the "tree whose
type is not the query's" are `such-that.smli` queries whose expansion
rewrites the row into something the query's own type does not name.
That leaves **58 that are real gaps**, and the largest of them is a
dozen queries at a time. Anyone buying coverage should start from this
table rather than from the count.

The count itself moved the wrong way this session -- 1,338 translated
became 1,312 -- and that is the fix working: 17 of the 26 are queries
reading `current` or `ordinal` through a set operator's operand, which
used to print a tree that named them (finding 13).

### Running the harness

```
etc/rel-diff.py --quiet --save /tmp/all.json tests/script/*.smli
etc/rel-diff.py --load /tmp/all.json --kind unexplained --limit 20
```

The whole corpus takes about six minutes and needs a built morel-java
in `~/dev/morel.4` at tag `449-tree.3`. `--save` and `--load` are worth
using, because reading the differences takes many passes and running
the shells takes one. It is not in the test suite, which has no JVM.

Two things it does that are worth knowing before reading its output.
It **strips the `set("mode", "validate")` brackets**, so it runs the
statements the corpus knows to be broken -- which is how finding 18
turned up. And a shell that stops answering is **not** allowed
to take the rest of the file with it: the marker before each statement
is a progress report, so a run that stops short names the statement it
stopped on, drops it, and replays. **Nine statements stop a shell on the
corpus, and every one is a morel-rust panic** (finding 18). Ten more
were the harness's own, four were finding 19, and three were
morel-java's findings 10 and 17; all are fixed.

## What morel-java did

`julianhyde/449-tree` in `~/dev/morel.4`, tag `449-tree.3`
(`01f24633`), replaces the *step list* representation of a `from` query
with a balanced *relational tree*. It is 227 commits and about 17,000
added lines on top of `main` (`29ac6903`), across 65 files.

Three documents on that branch are the source material, and they are
the contract rather than the code:

| file | lines | what it is |
| ---- | ----- | ---------- |
| `spec.md` | 725 | the datatype, its invariants, and the plan-text grammar |
| `plan.md` | 1995 | the implementation plan and session log |
| `discussion.md` | 930 | the arguments behind the design |

Read them with `git -C ~/dev/morel.4 show 449-tree.3:spec.md`, and so
on. The tags `449-tree.0`, `.1` and `.2` are on rewritten history and
are **not ancestors** of `.3`; only `.3` is a commit we can diff
against.

## What morel-java asks of us

Verbatim, from the end of its `plan.md`:

> ## Milestones for morel-rust and morel-go
>
> Fork after step 3, when the plan text is frozen. Implement the
> datatype, type derivation, validator, printer, and lowering against
> the frozen plan-text golden files; script tests are shared. The rule
> framework ports after the Java version stabilizes in step 4–5.

So the rule framework (its steps 4–6) is out of scope; it is not
written in Java yet.

## The contract

`Sys.planOf e` prints the tree that the resolver builds for `e`, and
does not evaluate `e`. Its text is the cross-implementation contract.
The conformance suite is `src/test/resources/script/rel-tree.smli` (390
lines), which says so in its header and names morel-rust. It is the
acceptance criterion: **morel-rust passes when its copy of
`rel-tree.smli` reproduces morel-java's expected output.**

The suite relies on raw string literals in expected output, which we
propagated in `e81bff3b` (morel-java #471), so the harness is ready.

A node prints on one line, indented two spaces per level, with its
collection type after a colon. A type longer than the width prints as
`t$0` and once in a legend below, separated by a blank line. The
element is `$0`; a join's components are `#1 $0`, `#2 $0`; a join that
carries a binder prints it, `join [v$0]`.

```
project [{dname = #dname (#1 $0), ename = #ename (#2 $0)}] : t$0
  filter [#deptno (#2 $0) = #deptno (#1 $0)
      andalso #job (#2 $0) = "PRESIDENT"] : t$1
    join : t$1
      #depts scott : t$2
      #emps scott : t$3
```

## The datatype, in one page

From `spec.md` §1–§4. The surprises are as important as the list.

**A node is a Core expression** whose type is a collection type, so the
algebra is closed and a query may appear wherever an expression may.
**There is no leaf constructor**: a node's input is simply an
expression, and the boundary between tree and the rest of Core is
wherever the expression stops being a node.

**Two things our `From` carries do not exist.** There is no binding
list (no counterpart to the bindings a `Step` carries) and no `atom`
flag. An element's type is the type of the expression that builds it.

Eleven constructors:

| arity | constructors |
| ----- | ------------ |
| one input | `filter`, `project`, `group`, `ifEmpty`, `sort`, `unorder`, `skip`, `take` |
| two inputs | `join` (kind, optional binder, condition) |
| n-ary | `union`, `intersect`, `except` (each with `distinct`) |

And four things that are **not** constructors, each of which we will be
tempted to add: `distinct` is a `group` whose keys are the whole
element; `compute` is a keyless `group` plus an extraction the
enclosing expression performs; `yieldAll` is a dependent join plus a
projection; an outer apply is a `join` of kind `left` carrying a
binder. Correlation is likewise not a mode — it is a free occurrence
of the join's binder in its right input, so decorrelation is dropping
the binder rather than rewriting one node into another.

**Names.** An expression sees the enclosing environment, `$0` (the
input's element) and, in a `join` only, `$1`. `$0` is rebound by every
node and does not accumulate. `skip` and `take` arguments are evaluated
before the first row and may name neither. A nested tree shadows `$0`,
so crossing that boundary needs a `let`, which is also how a join's
binder reaches its right input. `$0` is never a record label: fields
are addressed by label, inputs by position.

**`$0` must be a node of its own, not an identifier.** This is
morel-java's goal 1, and the warning it wrote before doing it is the
one to heed:

> `$0` is an ordinary `Core.Id` over an `IdPat` named `"$0"` with
> ordinal 0, and `IdPat.equals` compares name and ordinal and *not
> type*. So every `$0` in a tree is the same variable to anything that
> reasons about free variables. [...] The moment a tree survives the
> inline loop it is not harmless, and it will not announce itself -- a
> use count that is too high only makes the inliner decline, while one
> that is too low makes it substitute across a node boundary. Decide
> how `$0` is told apart [...] before the first pass sees a tree, not
> after.

So: a new `Expr` variant carrying the input's ordinal, from the start.
The payoff java records is that `free_names_in`, the inliner and the
analyzer are then right about it without being told.

**Joins concatenate.** `components(join(a, b))` is `components(a) ++
components(b)`, so three inputs give three flat components read as
`#1 $0`, `#2 $0`, `#3 $0`, and reassociating changes nothing. A join
has no yield; the projection above it is where names come back. In an
outer join each *component* of the side that may be absent is wrapped
in `option` on its own, and the condition still sees both sides
present.

**Kinds.** `sort` gives `list`, `unorder` gives `bag`, `join` gives
`list` only if both inputs are lists, set operators `list` only if all
are; the rest pass the input's kind through.

## The plan text, in one page

From `spec.md` §6, which is the frozen part and the fiddly part.

The invariant that makes the text parseable: **a relational operator is
the first non-whitespace on its line.** Everything else is a leaf, a
continuation, or the definitions region. A relation that would print
mid-line — inside a `let`, a `case`, a record field — is broken out
instead.

- One node per line; inputs indented **two**; a wrapped line's
  continuation indented **four**, which is how a reader tells a
  continuation from a grandchild.
- Arguments in brackets in the order §3 lists them, and **absent
  arguments are omitted**: an inner join's kind, a `true` condition, a
  `project` of `$0`.
- A relation reached from inside an expression prints as `r$0`, and its
  block follows the tree. The head lists the variables the fragment
  reads from outside, **transitively**, and the same text stands at the
  reference and at the definition: `r$1[v$0, v$1]`. An implementation
  must therefore compute that list before writing anything.
- Every node line ends `: type`; continuations carry none. A moniker of
  **24 characters or fewer** prints in full, longer ones as `t$0` with
  a legend after a blank line at the end. Two types with the same
  moniker share a reference.
- Lines wrap at the session's `lineWidth` and nothing else does: the
  nodes, the indentation and every number are the same at any width.
  The golden plans are all at 78.
- **Three renumbering sequences — `v$`, `r$`, `t$` — are properties of
  the text, not of any node**, each numbered from zero by first
  occurrence. Binders are allocated freely and renumbered when printed,
  so `v$123, v$110, v$200, v$110` prints as `v$0, v$1, v$2, v$1`.

That last point is the one that will bite us. An implementation that
builds the text by concatenating strings its children returned gets all
three sequences wrong, and silently, because each child restarts at
zero. **Thread one writer through.** `lindig.rs` gives us the document
model; the writer state has to sit outside it.

## What is in scope

Enough to print a tree, and nothing that changes what executes.

morel-java's branch does far more: it flips execution onto the tree,
moves grounding onto it (`RelExpander`, 2057 lines), deletes the step
list's grounding engine, and rewrites `Sys.planEx`. That is why its
branch churns `such-that.smli` (669 lines), `optimize.smli` (192) and
`built-in/sys.smli` (557). **We should change no existing script**
except `built-in/sys.smli`, which gains one name because `Sys.planOf`
is a new binding. If another script moves, something is wrong.

Keeping the step list as what executes is also what makes this a bug
hunt rather than a rewrite: the tree is built, validated and printed
alongside the machinery that already works, so a disagreement is
visible without anything being at risk.

## Milestones

Each is a commit, `fullMake --no-clean` green, on the `449-tree`
branch. morel-java's own sequencing put execution before observability,
on the argument that "freezing [the plan text] on trees that have never
run risks churning it". That argument does not apply to us: the text is
already frozen, which is precisely why its plan says to fork here. We
build, validate and print; we do not flip execution.

**R1 — `Sys.planOf`, printing a placeholder.** Add the built-in to the
library, to `lib/sys.sig` and to the docs. Expand it in `resolver.rs`
at the `Apply`, as morel-java does in `Resolver` line 1321, into a
string literal. Its argument must not be evaluated, and expanding it in
the resolver rather than later is deliberate: the rewrite passes run to
a fixed point, so a later expansion would make a plan's text depend on
when the inliner reached the call. Assert only that it exists and does
not evaluate. `built-in/sys.smli` gains a name here, and that is the
only existing script that should move in this whole effort.

**R2 — the datatype and its types.** The eleven constructors, the
element-type derivation and the kind derivation, in `compile/core.rs`
beside `Expr`. Includes the input-reference node. Build trees by hand
in unit tests; no translator yet.

**R3 — the validator.** `spec.md` §5's five invariants, each a numbered
check with its own test, plus rejecting the binder collision §5 leaves
open. It is what turns a wrong tree into a named error instead of a
wrong plan.

**R4 — the printer.** `spec.md` §6, the frozen grammar, in three
parts.

*R4a, the layout.* One node per line, inputs two spaces in, arguments
in brackets in the datatype's order with the absent ones omitted, the
type on every node line, the legend for a moniker over 24 characters,
and the generated binders renumbered by first occurrence. Done.

Layout is not a function of the width -- tree mode breaks a relation
out whatever the width -- so this needs no document model, and does not
use `lindig.rs`. morel-java moved its writer to a document and recorded
that Lindig "undoes something", because a document has no current
column until it is rendered and the decision to break a relation out
asks whether it is at the start of a line. Here that decision is
structural, so the question does not arise.

*R4b, wrapping.* Done. A node's own line folds at the session's
`lineWidth`, with its continuation indented four from the node. Break
points are found in the *rendered* line rather than built into it --
before a conjunction's keyword at the top level, after the comma
between a record's fields -- so a line that fits is character for
character the line an unwrapped printer would write, and the flat form
cannot drift from how an expression prints elsewhere. `lindig.rs` then
makes the fold one decision for the whole line, which is what the
golden text shows: a record folds after every comma or none.

**R4c came after R5**, decided 2026-09-12 because it is about
byte-exact output, which only R6 requires, while the shadow in R5
finds disagreements without printing anything at all. Done 2026-09-12,
ahead of the rest of R5, because the fragment rule turned out to be
cheap and the two examples in `spec.md` §6.4 are exact enough to be a
test on their own.

R4b was deferred for the same reason and then done, because the fold
turned out not to need what morel-java's does. Its writer renders an
expression *into* a document, so the break points are built in and
every expression's printing changes; finding them in the rendered line
instead leaves the rest of the printer alone, and is exact by
construction because the pieces join back into the line.

*R4c, fragments.* Done. A relation reached from inside an expression
cannot print where it stands, because an operator must be the first
non-whitespace on its line. It prints as `r$0` and its block follows
the tree. The head lists what the fragment reads from outside itself,
transitively, and the same text stands at the reference and at the
definition, so the list must be computed before anything is written.

`Display` is what prints an expression, and Rust's `Display` carries no
state, so the list a reference goes into lives in a thread-local that
`plan` installs for the length of one plan and puts back after. That is
where morel-java threads its writer, and putting it back is what keeps
a node printing in place everywhere else -- an error message, a trace.
A fragment is keyed by its *address* in the tree, because two
structurally equal subqueries are two subqueries and one reference
would say they are one. What a fragment reads from outside itself is
its free names less the plan's own, which is transitive without trying:
a fragment nested inside this one is part of its subtree however far
away it is printed. The names are sorted in `renumber`, not where the
header is built, because it is the text's numbering they are in order
of and not their maker's.

*R4d, a `let` and a `case` may start a line.* Done, and not foreseen:
morel-java added it in `01f24633`, the tip of tag `449-tree.3`, and two
of the suite's fragment cases need it.

```
filter [let
      val v$0 = $0
    in
      #nonEmpty Relational (r$0[v$0]) andalso #nonEmpty Relational (r$1[v$0])
    end] : int list
```

This overturned R4b's decision. Finding the break points in the
rendered line works while every piece of a fold shares one indent and
one decision; here the `in` and `end` sit at four from the node and
what they bracket at six, and the `let` broke while the `andalso`
inside it did not. Two indents and two decisions, which is to say
nested groups -- and a flat list of pieces has one group by
construction. So R4d is the work R4b avoided: a node's line is a
document, with a group per `let`, `case`, conjunction and record, and
`lindig.rs` deciding each.

It is not the whole rewrite it looked like, because only a construct
that holds a break point needs an arm: everything else is its `Display`
text, which is what a document with no break point renders to anyway.
That is also the contract, and a test: rendered at a width nothing
exceeds, the document gives back exactly what `Display` gives, so a
line that fits is character for character the line an unwrapped printer
would write, and nothing outside a plan changed at all.

**R5 — the translator, and a shadow over the corpus.** Step list to
tree, morel-java's `RelTranslator` (966 lines): variable elimination,
where a binder becomes an expression over `$0` and the binding list
disappears. It declines rather than guesses, returning `None` for what
it cannot translate, and we count the declines.

Then borrow morel-java's step-1 technique, which is the cheapest bug
detector on offer: translate every query the script corpus compiles and
assert two things — that the tree's type equals the query's type, and
that the validator accepts it. Java ran that over 1534 queries and
declined none. Do not attempt a structural round trip against the step
list; java tried and explains why it cannot work, as the translation
normalizes.

*R5c, the shadow.* Done 2026-09-12. The resolver builds the tree for
every query it resolves, in a debug build only, and records what
happened; each script test then asserts that no tree failed the
validator. The type equality is inside `translate`, which returns
nothing where the tree's type is not the query's, so a failure there
shows up as a decline rather than as a fault.

*R5d, the decline reasons.* A count of declines says how much coverage
is missing and nothing about what. So a decline says why, at the point
the decision is taken, and the shadow keeps the tally and the first
query for each reason. The *first* reason stands, not the last: an
outer caller sees the `None` too, and a coarse reason written there
buries the exact one underneath it. One attempt is forgotten on
purpose -- an expression holding a query declines the plain
substitution and succeeds through the `let` -- because what it said is
about a path not taken.

Reading the tally bought fourteen translations in an afternoon, and
the count went from 804 declines out of 1762 queries to 397 out of
1735:

| what it bought | what it was |
| -------------- | ----------- |
| `distinct` | a group on every binder with no aggregate, which is what the compiler makes of it |
| a `let`, `case` or `fn` in an expression | substitution stops at a name the construct binds |
| any scan pattern that cannot fail | a path is a list of hops, so a pattern nests as deep as it likes |
| a tuple pattern over a record | a record has components too: its fields in label order |
| a record or wildcard scan pattern | the same walk |
| `group ()` | a group on nothing, which is one group |
| `from` with no steps | the unit leaf, which is what `from` evaluates to |
| a `compute` query | a value, not a collection: the tree's *element* is the query's type |
| `group ()`'s element | `record_type` answers `unit` for a record of no fields |
| a statement that will not compile | not shadowed at all |
| `yield i + j distinct` | `distinct` keys on the whole element, under a name the printer made |
| a scan pattern that can fail | a filter over the source and a projection over that, which is how morel-java splits it |
| a query with one binder | its row is that binder's value: the element atomizes rather than becoming a record of one field |

Every decline now says why; none is unaccounted for. What is left
divides in two. Three quarters of it -- 303 of the 397 -- are queries
with nothing to build: `exists` short-circuits into a boolean, and
`ordinal` and `current` are the row's place and the row itself, and
none of §3's eleven constructors carries any of the three. The rest
are real gaps, and the largest are a query whose row is not a record,
a scan source holding a query inside an expression, and a `group` key
that is an expression with no name.

Two are worth reading twice, because reading a reason is what found
them. An ungrounded scan leaves an `Extent` that is not a collection,
so every node over it failed to derive a type -- which read as fifteen
findings and was one query that was never going to run; the shadow now
leaves a statement the resolver has rejected alone. And a `compute`
query is a value rather than a collection, which is exactly what
`spec.md` §3 says about it, so the check at the end had been asking
the wrong question of fifty queries.

It paid for itself on its first run, on a query nothing else looked
at:

```
from j in [1, 2] join i in ["x", "y"] except [{i = "y", j = 2}]
```

The set operator was built over `int * string` and `{i:string, j:int}`.
A set operator compares its inputs element by element, and after
several binders the tree's element is its inputs' components, which
carry no names, while the operand is the row the query wrote. So the
components are named before the set operator rather than at the end.

Two smaller gaps closed on the way, both found by reading the decline
count rather than a failure: a `group` whose single key is not written
as a record takes its name off the expression, and a projection that
builds the element it was given has no argument, which `spec.md` §6.3
lists beside an inner join's kind.

*R5b, a query inside an expression, and a scan that destructures.*
Done 2026-09-12, and the two together are what make R4c reachable from
a script: morel-java's own fragment cases are
`where nonEmpty (from (a, b) in pairs where a = x)`, which needs both.

A nested query is a tree of its own and its `$0` is its own element, so
it cannot read the row the expression is about that way. The expression
is wrapped in a `let` that gives the row a name, and the nested tree
reads the binders through the name; the `let` appears only where there
is a nested tree to want it. `substitute` grew a hook for it rather
than a second copy of itself.

A scan's pattern binds one name per component, so `Path` became a list
of hops rather than one. A join then prepends a component to every
binder its left input had, where before it rewrote a whole-element
binder into the first component -- the same thing when the path is one
hop, and the right thing when it is two. A pattern that nests is still
declined: two hops mean two different things there, and nothing yet
says which is which.

Both of morel-java's fragment cases now print its text byte for byte
except where a node's own line folds, which is R4d.

**R6 — the conformance suite.** Done 2026-09-12. morel-java's
`rel-tree.smli` at tag `449-tree.3` is copied across whole, and its
fifteen plans print morel-java's text byte for byte except in two
places, each marked in the file and logged below. morel-rust's own
cases -- what `Sys.planOf` promises, and where the translator declines
-- follow at the end, so that the two stay easy to tell apart.

The two differences are both morel-rust bugs on `main`, which is what
this branch was for: a `where true` step is dropped before the tree is
built, and an aggregate prints with parentheses, a structure member's
name, and an instance rather than the generic. Neither is fixed here.

**R7 — the differential harness.** Done 2026-09-13, as
`etc/rel-diff.py`. Everything up to R6 checks morel-rust against
itself; R7 is the first thing that checks it against morel-java over
more than fifteen queries, and it asks 1,235 of them.

It replays a `.smli` file in both shells rather than extracting the
queries, because a query needs the declarations above it, and it asks
`Sys.planOf` of each `from` statement as it goes. A marker before each
statement anchors the two outputs, so a statement that compiles in one
implementation and not the other shifts nothing. The marker is a
declaration, `val relDiff = 7`, rather than a string expression,
because an expression sets `it` and a declaration does not -- and
`it.smli` is in the corpus.

*The stall was not a stall.* The first run read 605 of 989 answers as
"unanswered" because both shells stopped partway through a long file,
which I had written down as a shell waiting for input it thought was
missing. It is not: morel-java throws an uncaught `ClassCastException`
(finding 10) and morel-rust panics (finding 18), and each takes the
rest of the session with it. So the marker before each statement is
also a progress report, and a run that stops short names the statement
it stopped on, drops it, and replays -- one attempt per death, rather
than the chunking the last session proposed, which would have cost
more and named nothing. `relational.smli` went from 523 unanswered to
74, and the 74 are the corpus's own error cases.

*Classifying by hand does not scale to 491 differences.* So a class is
a **canonicalization**: a rewrite applied to *both* answers that erases
one distinction and nothing else. A case is explained when the two are
equal after every rewrite has run -- equal exactly, so a rewrite cannot
take credit for a case it did not account for -- and its class is the
rewrites it needed, which is found by leaving each out and asking
whether the two are still equal. Applying a rewrite to both sides is
what makes this safe: a one-sided rewrite would have to know which
implementation writes which form, and would turn a form the two agree
on into a difference.

Seven rewrites explain 152 of the 491. What is left groups by the
first line on which the two disagree, which is how findings 11 to 16
were read off rather than looked for. Finding 19, the one that
matters most, came from none of that: it came from asking why a shell
stopped.

*And ten of the stops were the harness's own*, which took two goes to
see. A `.smli` file comments a statement out by wrapping it, and
`parse_blocks` splits on `;` without tracking comments, so the `*)`
that closes the wrapper arrives at the head of the *next* block: fed
to a shell one block at a time, that is an unterminated comment, and a
shell waiting for the rest of it reads from outside exactly like a
shell that has died. Joining a block to the one after it until the
comment closes fixes it -- but the first attempt lost 214 queries,
because `(*)` *inside* a block comment is a line comment and not a
nested `(*`, which `simple.smli` says in as many words and names the
case. The lesson is the harness's own: a count that moves the wrong
way is the check, and reading it is what caught a fix that looked
right.

Twelve statements stop a shell now, and every one is a finding.

**R9 — what R7 found in the translator.** Done 2026-09-13, before R8
and out of numerical order, because these are bugs in code this branch
owns: fixing them here hides nothing, where a fix to findings 1 to 3
would. Findings 11 to 14 and 16, and the five together took the two
implementations from agreeing on 385 of the corpus's queries byte for
byte to agreeing on 418.

The one worth reading is 11, because the fix is a *check* and the check
found four more bugs than the finding did. Three things had to be true
for it to work.

*The names come from the compiler, not from the translation.* A step's
binders are `step.env.bindings`, which is what the compiler says is in
scope after the step. The translation used to read them off the
expression instead -- `yield f = d` binds `f`, the expression is `d`,
and `implicit_label` answers `d` -- so a translation that got a name
wrong agreed with itself and said nothing. The same change fixed six
queries in `type.smli` whose `yield` built its record through a `let`,
where the old code answered "no names at all".

*Scope decides it, and a finished tree has none.* `from i in [1, 2]
yield {h = h}` reads an outer `h` and binds a field called `h`, and in
the tree they are the same four characters. A check over the finished
tree flagged it; a check that asks, after each step's rewrite, whether
any name that *was in scope for that expression* is still free in it,
does not. So the translator records what leaked and the validator
reports it, which is `validate_eliminating` and
`rel_translator::leaked`.

*A decline is not always the answer.* `elements` looked like finding
4's family -- a name the compiler answers out of the group's frame,
which no node defines -- and the reflex was to decline. It is the
identity function over the whole element, which §3's `group` already
expresses, so the translator now writes what morel-java's resolver
writes and nothing was added to the datatype.

The other four are smaller. A set operator's operands were cloned into
the node untranslated, which cost a legend entry and let `current`
through (12 and 13); a literal pattern over `unit` made a filter that
cannot fail (16). Three of the five now print morel-java's text byte
for byte; the other two differ only in ways logged as findings 3 and
15. The six cases are at the end of `rel-tree.smli`.

**R8 — land the findings on `main`.** Done 2026-09-13, all four, in a
`main` session:

| finding | commit | what it was |
| ------- | ------ | ----------- |
| 19 | `709e5d8f` | a comma-scan's `on` condition read an outer binding of the same name -- the only wrong *answer* on the list |
| 1 | `69e6a205` | `union distinct` re-planned as `union all` |
| 2, 3, 6 | `4dd4137d` | a dropped `where true`, and how an operator and an aggregate print |

and one more that turned up on the way: `inlinePassCount` was accepted
and ignored (`d972d0f8`), which I found trying to use it to tell
whether the `on`-condition bug was the inliner's.

The last commit is what the acceptance criterion turned on, and the
answer came from reading morel-java rather than from arguing about the
spec. Two of the three questions it settled had an answer sitting in
morel-java's source: `FILTER_TRUE` is a *simplification* there, off by
default, which is why its plan keeps a `where true`; and
`AstWriter.infix` looks an operator up in `Op.BY_OP_NAME` rather than
going through `Resolver.toOp`, which is why it writes far more
operators infix than our comment claimed to mirror. Widening the set
then exposed a worse bug underneath: we had no bracketing at all, so
`i + (i + 1)` printed as `i + i + 1`.

`main` is merged into this branch, and **`rel-tree.smli`'s every plan
is now morel-java's text byte for byte**. That is the acceptance
criterion in "The contract" below, and it is met.

**Later, not now.** The lowering (`RelLowerer`, 949 lines) matters when
the tree becomes what the passes carry. Grounding on the tree
(`RelExpander`, 2057 lines) and the rule framework follow, and
morel-java has not written the rule framework yet — its steps 4 to 6
are all unchecked. `Sys.plan` keeps printing the step list, in both
implementations, until the tree is what executes.

## Files: morel-java to morel-rust

| morel-java | lines | morel-rust |
| ---------- | ----- | ---------- |
| `ast/Core.java` (node kinds) | +1015 | `compile/core.rs` |
| `ast/CoreBuilder.java` | +427 | `compile/core.rs` builders |
| `ast/RelBuilder.java` | 1050 | new `compile/rel_builder.rs` |
| `compile/RelTranslator.java` | 966 | new `compile/rel_translator.rs` |
| `compile/RelValidator.java` | 337 | new `compile/rel_validator.rs` |
| `ast/AstWriter.java`, `AstNode.java` | +633 | `compile/lindig.rs` + new printer |
| `compile/Resolver.java` (planOf hook) | — | `compile/resolver.rs` ~1937 |
| `compile/RelLowerer.java` | 949 | deferred |
| `compile/RelExpander.java` | 2057 | out of scope |

Java tests worth porting as unit tests: `RelTest` (444), `RelBuilderTest`
(628), `RelTranslatorTest` (389).

## How to verify

`fullMake --no-clean` for each milestone. `etc/check-convergence.py` is
not the gate here: it compares against morel-java's `main`, which does
not have this work, so it would read every added line as divergence.
The gate is `rel-tree.smli`.

## Risks

- **The spec may not say everything the Java code does.** That is the
  point of the exercise, and the reason to write findings down rather
  than to quietly match the implementation. Where the code and the
  spec disagree, the spec is what we implement, and the disagreement is
  a finding.
- **The plan text is fiddly and exact.** Wrapping, legends and binder
  numbering are where two implementations drift apart without either
  being obviously wrong. `spec.md` §6 is long for that reason.
- **Generated binder numbering is shared across a whole statement**,
  not per tree; the suite tests exactly that, and an implementation
  that numbers per tree passes everything else and fails there.

## Lessons morel-java paid for

Worth reading before repeating them.

- **A pass cannot shadow the resolver by re-running it.** Java tried a
  differential shadow and backed it out: the resolver takes names from
  a generator and registers in the type map, so running it twice
  corrupts the run that counts. Our shadow asserts about the tree we
  already built, and never rebuilds it.
- **Names must not depend on what was compiled before.** Java's plan
  text said `d_14` in one run and `d_16` in another until it renumbered
  at print time. Allocate binders freely; renumber when printing.
- **A record label is printed as text, not through the identifier
  path.** A renumbering writer that renames identifiers but not labels
  prints one binder under two names, which looks like a semantic bug
  and is not. Java lost half an hour to it; we can lose none.
- **Classify diff hunks that add lines, not only those that delete
  them.** A script that skipped pure additions hid seven wrong rows and
  cost java a session's worth of wrong conclusions.

## Findings log

Disagreements between morel-rust, morel-java and `spec.md`. One line
each, with the query, what each produced, and which we think is wrong.

Three in morel-rust, found by building the tree beside the step list.
None is fixed here: this branch is not for `main`, and a fix made on it
would hide the bug rather than report it. They are the branch's
product, and getting them onto `main` is a session of its own.

1. **`union distinct` re-plans as `union all`.** The step flag holds
   *distinct*, and `core::write_set_step` names its parameter `all` and
   prints the word when the flag is set. So `from i in [1, 2] union
   distinct [3]` prints as `from i in [1, 2] union all [3]`: the plan
   says the opposite of the query, and re-running the plan would change
   the answer. Found because translating the flag into a node inverted
   it, which sent me to look at what the flag means.

   **Fixed on `main` 2026-09-13, `69e6a205`.** The core unparser writes
   `distinct`, the word the flag means. The AST unparser had the word
   right and wrote it before every operand, so `union distinct a, b`
   came back as `union distinct a, distinct b`, which does not parse;
   `distinct` qualifies the operator and the grammar takes it once.
   `Sys.planEx "core"` is where the text is visible, and
   `relational.smli` now pins it.
2. **A `where true` step is dropped, and morel-java keeps it.** For
   `from where true yield 1`, morel-java's golden text is
   `project [1]` over `filter [true]` over `[()]`, and ours has no
   filter, because the step is gone before the tree is built. One of
   the two is wrong about what a plan should show; the spec does not
   say.

   **Fixed on `main` 2026-09-13, `4dd4137d`**, and reading morel-java
   settled which. It skips `where true` in its own `FromBuilder` as we
   did -- the same three lines, the same comment -- and keeps it in the
   `RelBuilder` that builds the tree, where dropping it is a
   *simplification* that is off by default, so that a plan shows the
   query as written. We build the tree from the step list, so a step
   dropped there can never reach a plan; it is kept.

3. **An aggregate prints differently inside a node.** For
   morel-java's group case the tree, the types and the legend all
   agree, and only the aggregates differ: we write
   `[c = (#count Relational over ()), total = (sum$real over #sal $0)]`
   where morel-java writes `[c = count over (), total = sum over #sal
   $0]`. Three differences in one line, and they want separating: we
   parenthesise an aggregate and morel-java does not; we resolve
   `count` to the structure member and print it in selector form, where
   morel-java keeps the global name; and we dispatch `sum` to
   `sum$real` by the element type, where morel-java keeps the generic.
   The parentheses are not cheap to change -- they are how an aggregate
   has printed in every plan, and the corpus has them -- so this is a
   `main` conversation, not a branch one.

   **Fixed on `main` 2026-09-13, `4dd4137d`**, all three, once that
   conversation was had. A built-in with a name of its own in the
   default namespace prints bare, because that is how the resolver
   found it -- `count`, `sum`, `abs`, `concat` -- while one merely
   *overloaded* under a global name stays qualified, `#only
   Relational`, which is what morel-java does too. An overload's
   instance prints as the generic it instantiates. And nothing
   parenthesises an aggregate. The corpus moved in three files, all of
   it plan text.

And one that is neither, found by asking why morel-java declines
nothing:

4. **The two Cores disagree about `exists`, `ordinal` and `current`,
   and the tree cannot express any of them.** morel-java's translator
   declines none of its 1534 queries and asserts as much; ours declines
   303 for these three. The reason is representation, not capability.
   `Resolver` in morel-java rewrites `exists ...` into `Relational.
   nonEmpty (from ...)` and `forall ... require e` into `not exists
   (from ... where not e)`, so its Core holds an ordinary `From` that
   the translator handles; morel-rust keeps a terminal
   `StepKind::Exists` step. And `ordinal` is `BuiltIn.Z_ORDINAL`, a
   built-in *name*, in morel-java, where morel-rust made it a node
   (`Expr::Ordinal`, commit `5e31f11a`).

   The finding is not that one Core is wrong. It is that **neither
   implementation has a node for the row's position, and morel-java
   does not notice**: its tree carries `$ordinal` as a free name that
   nothing in the tree defines, and its shadow passes because a name
   always substitutes. `spec.md` §3 lists eleven constructors and none
   of them numbers a row. Either the tree needs a constructor, or a
   query that reads `ordinal` cannot become a tree and morel-java's
   zero-decline invariant is wrong. Raise it with morel-java before
   changing either implementation.

And five from R7's first run, which is what a differential harness is
for. The first is the one worth the whole exercise.

5. **morel-java's type legend is not renumbered, so a plan names one
   binder under two names.** The tree says `v$0` and the legend says
   `v$8`, and which second name you get depends on what was compiled
   before. Minimally, against `~/dev/morel.4` at tag `449-tree.3`:

   ```
   Sys.set ("stringDepth", ~1);
   val emps = [{id=100,name="Fred",deptno=10}];
   (*) eight queries, to move the session's binder counter on
   from e0 in emps order e0.deptno where ordinal > 1 yield e0.name;
   ...
   Sys.planOf (from e in emps order e.deptno where ordinal > 1);
   ```

   gives `filter [#v$0 $0 > 1]` over `project [{e = $0, v$0 = $ordinal
   ()}]`, and `t$1 {e:{...}, v$8:int} list`. A binder inside a *type*
   is text that the renumbering writer never sees, exactly as
   morel-java's own lesson says about a record label -- "a renumbering
   writer that renames identifiers but not labels prints one binder
   under two names". The legend is the same mistake one level out.

   Invisible to any test that starts from a cold counter, which is
   every test morel-java has: with the counter at zero the allocated
   name and the printed name coincide. morel-rust is immune by
   construction, because it renumbers the finished text rather than
   the writer's identifiers, and the legend is part of the text.

   **Fixed in morel-java 2026-09-14**, `~/dev/morel.2` `240129bb`: its
   renumbering writer now renames the generated binders *inside* a
   type's text, where before it renamed only a string that was entirely
   one.

6. **An operator that morel-java writes infix, we write as a call.**
   `from i in [1, 2, 3] yield i - 5` is `project [$0 - 5]` in
   morel-java and `project [#- Int ($0, 5)]` in morel-rust; `abs x` is
   `abs $0` there and `#abs Int $0` here. `library.rs`'s `infix_op`
   says it "Mirrors morel-java's `Resolver.toOp`" and excludes
   everything but `+`, the comparisons, `::`, `@`, `andalso` and
   `orelse` -- and morel-java disagrees. This is finding 3's second
   half, and it is not about aggregates: it touches nearly every plan.

   **Fixed on `main` 2026-09-13, `4dd4137d`.** `toOp` is the wrong
   mechanism to mirror: `AstWriter.infix` looks the function up in
   `Op.BY_OP_NAME`, so morel-java writes *every* operator with a padded
   name infix, and `toOp`'s handful is only what it converts from a
   built-in literal. The set is now derived from the operator's own
   name rather than listed.

   Which exposed a second bug underneath, and a worse one: there was no
   bracketing at all. `i + (i + 1)` printed as `i + i + 1`, and
   `i > 1 andalso (i < 3 orelse i = 5)` lost the grouping it was
   written with -- a plan that says something the query does not.
   Operands now carry morel-java's precedence bounds, in `Display` and
   in the tree printer both.

7. **`distinct` atomizes in one implementation and not the other.**
   `from i in [2, 3, 1, 3] distinct` is `project [#i $0]` over `group
   [i = $0] : {i:int} list` in morel-java, and `group [i = $0] : int
   list` here. `spec.md` §3 says a `group`'s element is a "record of
   the key and aggregate types, **or the single field's type if there
   is exactly one**", which is what we do and morel-java does not.
   Raise it: on the spec as written, morel-java is wrong.

8. **A leaf that is a list does not fold here, and folds there.**
   morel-java breaks `[{d = 20, e = "x"}, {d = 10, e = "y"}, {d = 10,
   e = "z"}]` after a comma at width 78 and we leave it long, because
   `doc` in `rel_printer.rs` has an arm for a record but none for a
   list. morel-java also breaks *inside* the third record while the
   first two stay whole, which is a group per element and not one
   group over all of them. Ours to fix, and cheap.

9. **Grounding happens before the plan here and after it there.**
   `from x where abs x < 5` has the leaf `extent "int"` in morel-java
   and `#flatten Range ([OPEN (~5, 5)])` here, and `from u: unit` has
   no tree at all in morel-java. Neither is wrong, but the plan text
   is supposed to be a cross-implementation contract, and it cannot be
   one for a query whose grounding lands on different sides of the
   printer. Worth agreeing on before `such-that.smli` is ever
   compared.

And twelve from R7 over the whole corpus, which is what a differential
harness is for. Two of them stop a shell dead, and those came first
because nothing else could be measured until they did; finding 19,
found by asking why a third shell stopped, is the only wrong answer on
the whole list.

10. **morel-java's plan printer crashes on a unary `~`, and the crash
    is uncaught.** Three lines, against `~/dev/morel.4` at tag
    `449-tree.3`:

    ```
    val emps = [{id=100,name="Fred",deptno=10}];
    Sys.planOf (from e in emps yield ~e.deptno);
    ```

    gives `ClassCastException: Core$Apply cannot be cast to Core$Tuple`
    at `AstWriter.infix:390`, and the shell does not come back. The
    cause is two lines apart in `Op.java`: `NEGATE("~ ")` reaches
    `Op(String padded, int precedence, Assoc assoc)` with precedence 0
    and `Assoc.NONE`, and that constructor computes `left = precedence
    * 2 + (assoc == LEFT ? 0 : 1)`, so a *prefix* operator comes out
    with `left = 1`. `AstWriter.infix` reads `left > 0` as "binary
    infix" and casts the single argument to a tuple. `~1` is safe only
    because it folds to a literal before anything prints it.

    **Fixed in morel-java 2026-09-14**, `~/dev/morel.2` `240129bb`:
    `NEGATE` has an associativity of its own, `Assoc.PREFIX`, and
    `AstWriter.infix` asks `isPrefix()` rather than reading `left > 0`
    as "is infix". It also gained a precedence tighter than any binary
    operator, so `~x + 1` needs no brackets and `~(x + 1)` keeps them.

11. **morel-rust leaves a name the query bound free inside a node.**
    `from d in scott.depts yield f = d yield f.deptno` gives `project
    [#deptno f]` over an argument-less `project`, where morel-java
    gives `project [#deptno $0]` over the leaf; `from i in [1,2,3]
    group g = {x=i} compute {c = count over ()} order g.x` gives `sort
    [#x g]`. Variable elimination misses a binder the query names for
    the whole row. The plan is not merely different, it is wrong: `f`
    and `g` are free, and nothing in the tree defines them.

    What matters more than the bug is that **the validator accepted
    it**. A validator that rejected a tree naming something nothing
    binds would have caught this, and 13, and 14, none of which was
    being looked for. It is the cheapest fix on the list.

    **Fixed 2026-09-13**, and the validator first. A step's binders now
    come from the step's own environment -- the compiler's answer --
    rather than off the expression the step yields, which was the
    translation's own guess and said `d` where the query said `f`. The
    check is `rel_validator::validate_eliminating`, and what it is
    given comes from the translator, because scope decides it and a
    finished tree has none: `from i in [1, 2] yield {h = h}` reads an
    outer `h` and binds a field called `h`, and only the step that
    rewrote the expression knows which was which. Written for this
    finding, it caught six more queries in `type.smli` whose `yield`
    built its record through a `let` and lost every field name.

12. **morel-rust does not translate a set operator's operand.** `from
    e in emps yield e.deptno union (from d in depts yield d.deptno)`
    gives a `union` whose right input is the Core query `from d in
    depts yield #deptno d`, where morel-java's is a `project` over a
    leaf. Legal -- `spec.md` §1 has no leaf constructor, so an input is
    simply an expression -- but a translation not attempted, and it
    silently costs the plan a legend entry. Twenty-three cases, and not
    only under a set operator: any input reached through an expression
    the translator does not walk into.

    **Fixed 2026-09-13.** An operand goes through a rewrite of its own
    rather than being cloned: it is compared with the tree element by
    element and not evaluated once per row, so it does not read `$0`
    and the binders over `$0` are not in its map, but it may read
    `outer` and a query it holds is a tree. The plan is now
    morel-java's byte for byte.

13. **`current` survives into a fragment, unsubstituted.** `from x in
    [10,20] yield (from i in [1,2] union [current])` gives, in
    morel-java, `r$0[v$0] = ... [v$0]`, and in morel-rust `r$0 = ...
    [current]` -- a fragment whose head lists nothing and whose body
    reads a name nothing binds. Finding 4 says morel-rust declines
    `current`; this says the decline does not reach a nested tree, so
    where it does not reach, morel-rust builds exactly the tree finding
    4 accuses morel-java of building. It should decline. Ten cases.

    **Fixed 2026-09-13**, by the same rewrite as finding 12: an operand
    now passes through `substitute_with`, which is where `current` and
    `ordinal` decline. It declines.

14. **`compute {elements}` prints its own label as its aggregate.**
    `from i in [2,3,1,2] group i compute {elements}` gives `group [i =
    $0] [elements = elements]` in morel-rust and `[elements = #id Fn
    over $0]` in morel-java. Another free name, and the same validator
    would have caught it. Nine cases.

    **Fixed 2026-09-13**, and it did not need a decline after all.
    `elements` is a name the compiler answers out of the group's frame
    rather than out of any binding, which is why substitution left it
    alone; it stands for the identity function over the whole element,
    and `spec.md` §3's `group` already expresses that. So the
    translator writes what morel-java's resolver writes, `#id Fn over
    $0`, and nothing was added to the datatype. A group that bound the
    name itself keeps it, because then it is an ordinary binder and
    substitution has the answer.

15. **The two front ends normalize a query differently before a tree
    is built, and that is the largest unexplained class.** morel-java
    merges `from e2 in (from e in emps yield e.deptno) yield e2 + 1`
    into a single `project [#deptno $0 + 1]` and morel-rust keeps two
    projections; morel-rust drops the identity `yield {x = x}` of
    `from e in emps yield {x = e.deptno} where x > 10 yield {x = x}
    where x < 30` and morel-java keeps it; `from u in [(), (), ()]
    distinct` is `take [1]` in morel-java and a `group` in morel-rust.
    None of these is a translator difference at all -- the two
    translators are given different queries.

    This generalizes finding 9, and it is the finding that decides
    what the plan text is worth. **The plan text cannot be a
    cross-implementation contract for a query the two normalize
    differently**, and no amount of work on either translator will
    close it. Where `Sys.planOf` sits in the pipeline is the thing to
    agree on, and it is worth more than any single fix on this list.

16. **An irrefutable `()` scan pattern still filters in morel-rust.**
    `from i in [1,2,3], () in [()]` puts `filter [$0 = ()]` over the
    leaf, where morel-java has the leaf alone. R5d bought "any scan
    pattern that cannot fail", and `()` was missed: it has no
    components, so the walk that decides refutability never asks about
    it. Five cases.

    **Fixed 2026-09-13.** A literal pattern over a type with one value
    cannot fail, so it makes no test. The plan is morel-java's byte for
    byte.

17. **morel-java's shell mis-reads a backslash escape from stdin, and
    loses the rest of the session.** `val a = "a\"b";` and `#"\"";`
    each print nothing and take every statement after them with them;
    `val c = "\"\"";` raises `Lexical error ... Encountered: '\'`. Its
    *script* runner reads the same text correctly -- `pretty.smli` is
    morel-java's own file and contains all three -- so this is the
    stdin path alone. It costs the harness two files.

    **Fixed in morel-java 2026-09-14**, `~/dev/morel.2` `240129bb`:
    `isEscaped` is overridden, which is what `DefaultParser` asks once
    it is inside a literal, so the reader knows which quotes are escaped
    without unescaping anything.

18. **morel-rust panics where it should raise, on statements the
    corpus brackets off.** The harness strips the `set("mode",
    "validate")` brackets, so it runs what no test runs, and two
    distinct panics turn up: `group e.deptno compute {my_sum over
    e.id}` for a user-defined `my_sum` panics at `eval/val.rs:446`,
    "Expected code, closure, or fn, got Int(100)", and `aliasInc 7`
    in `overload.smli` panics at `eval/val.rs:256`, "Not a bool".
    All eight of `overload.smli`'s stops are that second one and one
    in `relational.smli` is the first. None is new to this branch and
    none is a tree bug; a bracket says "we know this is wrong", and a
    panic is a worse kind of wrong than the brackets promise.

19. **A comma-scan's `on` condition reads an outer binding of the same
    name, and morel-rust answers the wrong thing.** Three lines:

    ```
    val d = 10;
    from e in scott.emps,
        d in scott.depts on e.deptno = d.deptno
      yield {d.dname, e.ename};
    ```

    morel-java gives the fourteen rows. morel-rust panics at
    `compile/types.rs:278`, "Expected record type", because `d.deptno`
    in the `on` condition is the outer `d : int`; make the outer `d` a
    record and it stops panicking and **returns `[]`**, having compared
    every employee against `{deptno = 99}`. Drop the `on` and write the
    same condition as a `where` and it is right, so the scan's binder
    is in scope everywhere except the `on` that belongs to it.

    The quiet version is the one that matters: a wrong answer, no
    diagnostic, and nothing in the corpus covers it because `blog.smli`
    has a `val d = 10` three hundred lines above the query and no test
    runs the two together. This is a `main` bug and the only wrong
    *answer* on this list -- everything else here is a plan that reads
    differently.

    **Fixed on `main` 2026-09-13, `709e5d8f`.** The inliner shadows a
    scan's pattern names in the environment it hands to subsequent
    steps, and did that *after* transforming the condition. The source
    is evaluated before the pattern binds anything, so it reads the
    enclosing scope; the condition is evaluated once per candidate
    pair, with the row the scan produced, so it reads the pattern's
    names. Moving the shadow above the condition is the whole fix, and
    `relational.smli` pins both halves -- the raise and the empty
    answer -- with the outer `val` inside a `let`, so that it does not
    stay in scope for the rest of the file.

20. **A node-free tree and a decline are the same text, so neither can
    be told from the other.** `Sys.planOf (from)` gives `[()]` in
    morel-java and `[()] : unit list` in morel-rust; the same for
    `from u: unit`, and for fifteen queries the harness first read as
    "morel-java declined".

    They are not declines. `spec.md` §1 has no leaf constructor, so a
    query that translates to a bare expression has a tree with no node
    in it -- and `from;` appears five times in morel-java's own corpus
    while `RelShadow.check` throws an `AssertionError` wherever
    `RelTranslator.toRel` returns null, so its translator plainly does
    not turn the query down. Printing the expression is a defensible
    thing to do with a node-free tree.

    What is left is still a finding, and a sharper one: the two print a
    node-free query differently, and **no reader of either text can
    tell a decline from a leaf**. That makes the harness's
    "morel-java declined" column unreliable, and morel-java's
    zero-decline invariant unfalsifiable from outside -- the one place
    its assertion would show up in the plan text is the one place the
    plan text says nothing.

    **Fixed in morel-java 2026-09-14**, `~/dev/morel.2` `240129bb`,
    morel-rust's way: a query's plan prints as a leaf line with its
    collection type even when the tree has no node in it, and an
    expression that is not a query still prints as itself. It made the
    harness's decline column right about 54 queries, and morel-java's
    zero-decline invariant checkable from outside for the first time.

21. **morel-java writes a built-in as the resolver *found* it, and
    morel-rust cannot tell how it was found.** `from e in emps yield
    only (from d in depts ...)` gives `only (r$0[v$0])` in morel-java,
    because the query wrote `only`; a `compute` that the compiler
    supplied the same function for gives `#only Relational (r$0)`.
    morel-rust's Core keeps the `BuiltInFunction` the name resolved to
    and not the name it was written under, so it writes one of the two
    everywhere -- the qualified form, since `only` is *overloaded*
    under a global name rather than being global itself.

    Three cases, and the smallest finding here. It is worth a line
    because it is the last of finding 3's family and it is not fixable
    the way the others were: the information is thrown away at resolve
    time, so closing it means Core remembering the spelling, which is
    a larger change than three plans are worth.

And two in `spec.md`, from reading it alone:

1. **§6.3's grammar contradicts its prose and examples.** The `defn`
   production spells a fragment head with brackets, `'r' '[' int ']'
   ' ='`, where the prose and every example in §6.4 and §6.7 write
   `r$0[v$0] =`. The grammar block looks like the typo; the examples
   are what we implement.
2. **§6.7 says binders are "numbered per tree", then refines it to
   per text.** The refinement, and `rel-tree.smli`'s own comment that
   two nested trees side by side both print `v$0` because one `let`
   binds them, say the numbering spans the text. The first sentence
   reads the other way and should probably go.

