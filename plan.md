# Relational tree (hydromatic/morel#449) — propagation plan for morel-rust

Branch `449-tree`. This work is **not for `main` yet**. Its first
purpose is to find bugs in morel-java's implementation by building a
second one against the same written contract: where the two disagree,
one of them is wrong, and the disagreement is cheap to find and dear to
reason about after the fact.

**Status, 2026-09-12: R1 to R6 are done.** morel-java's
`rel-tree.smli` at tag `449-tree.3` is copied across and passes, and
its fifteen plans are morel-java's text byte for byte except in two
places, both of which are morel-rust bugs on `main` and neither of
which is fixed here. The shadow translates 1,338 of the corpus's
queries and declines 397, with no tree failing the validator.

## Start here: what the next session does

Read this section and the findings log at the end. The rest of this
file is why things are the way they are, and is worth reading when
something surprises you, not before.

### What we have been doing, and what is worth doing instead

The branch exists to find bugs by building a second implementation
against a written contract. It has done that: five findings are logged
below, three of them morel-rust bugs that belong on `main`.

But look at what the checking actually rests on. The conformance suite
is morel-java's fifteen queries. Everything else -- the shadow, the
validator, the decline tally -- checks morel-rust against *itself*:
that the tree's type is the query's type, that the validator accepts
it. Those are real checks and they found real bugs, but they cannot
find a disagreement, because morel-java is not in the loop. Fifteen
queries is the whole of the cross-implementation contract we test.

**The cheap generalisation is to ask morel-java for the plan of every
query we can translate, and diff.** `~/dev/morel.4` is a working
checkout at tag `449-tree.3`, and its shell answers `Sys.planOf` from
a script:

```
$ cd ~/dev/morel.4
$ echo 'Sys.planOf (from i in [1,2,3] where i > 1);' | ./morel
- val it = "filter [$0 > 1] : int list\n  [1, 2, 3] : int list\n" : string
```

We have 1,338 queries that translate. Fifteen of them are checked
against morel-java. That ratio is the argument for R7, and the reason
to stop where R5d stopped.

### R5d has hit diminishing returns, and its tail is mostly a finding

397 declines remain, and 303 of them are `exists`, `ordinal` and
`current` -- which I had written down as "nothing to build". That was
wrong, and finding out why is the most valuable thing in this section.

morel-java declines **none** of its 1534 queries; `RelShadow.check`
throws an `AssertionError` where the translator returns null, on the
stated invariant that "a query the translator turns down is a query
the flip cannot carry". So either morel-java translates what we
decline, or its corpus does not contain it. It is the first. Both
buckets are representation differences between the two Cores, not gaps
in the tree:

- **`exists`.** `Resolver` in morel-java translates `exists ...` as if
  the author had written `Relational.nonEmpty (from ...)`, and
  `forall ... require e` as `not exists (from ... where not e)`. Its
  Core holds an ordinary `From` inside an application, which the
  translator handles. morel-rust keeps a terminal `StepKind::Exists`
  step, which no node can express. 200 declines.
- **`ordinal` and `current`.** In morel-java `ordinal` is
  `BuiltIn.Z_ORDINAL`, a built-in *name* (`$ordinal`), so Core holds an
  identifier and the translator substitutes it like any other.
  morel-rust made it a node of its own (`Expr::Ordinal`,
  commit `5e31f11a`). 103 declines.

That is finding 4 below, and it wants a decision rather than more
translation. Neither implementation has a node for the row's position,
so morel-java's tree names something the tree cannot define, and ours
declines. One of those is wrong and `spec.md` does not say which.

### The order for the next session

1. **R7, the differential harness.** Build it, run it, read the first
   fifty differences. Everything else waits on what it says.
2. **Finding 4**, once R7 says how much it costs: either pass
   `ordinal` and `current` through as atoms, matching morel-java and
   buying 103 translations, or keep declining and raise the
   disagreement with morel-java. Do not do this before R7: R7 may show
   that morel-java's plans for those queries are wrong, which settles
   it.
3. **The three `main` findings**, in a session on `main`. They are the
   branch's product and they are sitting in a branch nobody reads.
4. **Not the lowering.** morel-java's step 2 built `RelLowerer` (949
   lines) and the flip; `spec.md` does not freeze the lowered form, so
   a second lowering would be checked against nothing. It is worth
   doing when the tree is what executes, and that is not what this
   branch is for.

### R7 — a differential harness, in detail

The shape, smallest first:

- A list of queries valid in both implementations. Start with the
  `.smli` files both repos share; the statements are already there and
  already agreed on. A script that pulls every statement beginning
  `from` out of a `.smli` file and wraps it in `Sys.planOf (...)` is
  enough to begin.
- Run the list through `~/dev/morel.4/./morel` and through
  `./target/debug/morel`, with `Sys.set ("stringDepth", ~1)` and the
  same `lineWidth`, and diff the answers.
- Classify what differs before fixing anything, and write each class
  in the findings log. morel-java's own lesson, paid for: classify
  hunks that *add* lines, not only those that delete them.
- Keep the harness out of the test suite at first. It needs a built
  morel-java, which CI does not have.

Two things it will find that nothing else can: a plan we print
differently from morel-java for a query neither suite covers, and a
query morel-java declines. The second is the more interesting, because
morel-java asserts there are none.

**Built 2026-09-12, as `etc/rel-diff.py`, and it earned its keep on the
first run** -- findings 5 to 9 below are all its. Over four files it
asked 989 queries and the two agreed on 108. Read the findings before
reading the counts: most of what differs is one of five classes, not
989 separate problems.

Two things it still needs, and the next session should do them first:

- **It stalls.** Both shells stop partway through a long file --
  morel-java after 176 of `relational.smli`'s 678 queries, morel-rust
  after 566 -- and everything past the stall reads as "unanswered",
  which was 605 of the 989. A shell waiting for more input has been
  given a statement it thinks is unfinished, and the two disagree
  about which. Feeding a file in chunks, so that a stall costs one
  chunk rather than the tail, is the cheap fix; finding out what they
  disagree about is a finding of its own.
- **It classifies by hand.** `--kind DIFFER` and reading is fine for
  the first hundred; grouping the differences by shape would make the
  next thousand readable.

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

**R7 — the differential harness.** Not started; the next session's
first job, and "Start here" at the top of this file has the shape.
Everything up to R6 checks morel-rust against itself. R7 is the first
thing that checks it against morel-java over more than fifteen
queries.

**R8 — land the findings on `main`.** Three morel-rust bugs are logged
below and none is fixed, because a fix on this branch would hide the
bug rather than report it. They need a `main` session: `union
distinct` re-planning as `union all`, a dropped `where true`, and how
an aggregate prints.

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
2. **A `where true` step is dropped, and morel-java keeps it.** For
   `from where true yield 1`, morel-java's golden text is
   `project [1]` over `filter [true]` over `[()]`, and ours has no
   filter, because the step is gone before the tree is built. One of
   the two is wrong about what a plan should show; the spec does not
   say.

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

6. **An operator that morel-java writes infix, we write as a call.**
   `from i in [1, 2, 3] yield i - 5` is `project [$0 - 5]` in
   morel-java and `project [#- Int ($0, 5)]` in morel-rust; `abs x` is
   `abs $0` there and `#abs Int $0` here. `library.rs`'s `infix_op`
   says it "Mirrors morel-java's `Resolver.toOp`" and excludes
   everything but `+`, the comparisons, `::`, `@`, `andalso` and
   `orelse` -- and morel-java disagrees. This is finding 3's second
   half, and it is not about aggregates: it touches nearly every plan.

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

