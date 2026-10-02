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
# Making `Core` the relational tree

The goal: `Core` carries a relational tree and no step list. The step
list stays in the AST, where the user writes it. This is morel-java's
issue 449, part 3, which morel-java has finished and morel-go has
not: morel-go translates to a tree, grounds on it, and lowers back to
a step list for its compiler.

## Where to take the design from

Read morel-java for the **data model** and morel-go for the
**algorithms**. Where this port improvised between the two it has
had to back the work out; the record of this is worth trusting.

morel-java's `Core` (`ast/Core.java`) has no `From`, `Scan`, `Where`
or `Yield` class at all. Its `Rel` nodes that see one row at a time
-- `Filter`, `Project`, `Group`, `Sort`, together `RowRel` -- each
bind a `row: IdPat` and an optional `ordinal: IdPat`. The writer
prints those as `$0`, `$1` and `$ordinal`. That last point matters:
**the cross-implementation contract is the plan text, not the
representation.** `rel-tree.smli` prints `$0`, and morel-java prints
`$0` while binding a name underneath. This port can adopt
morel-java's model without changing a character of the contract.

morel-go's `internal/compile/relexpander.go` and `generator.go` are
the grounder. This port's `rel_expander.rs` is a port of the first.
Where the port was faithful it worked; the two failures below were
both places where it invented something instead.

Three of the problems on the list are not problems. They are
artifacts of `Core` holding a step list while morel-java's does not,
and they dissolve rather than get solved:

* A plan of a query whose generator came from an `exists` differs
  from morel-java's because `Sys.planEx` re-translates the lowered
  step list, and the lowering is not a round trip. With no step list
  there is nothing to re-translate.
* `ordinal` had no home in the tree. It has one now, morel-java's
  optional `ordinal` binder on a row node (stage B, landed). What
  remains of the old answer -- `materialize_ordinal`,
  `drop_ordinal`, `replace_ordinal`, `ORDINAL_SLOT`, and two row
  sinks -- serves only the step list, and goes with it.
* The reverse-equality cycle guard in `generators.rs` exists because
  the step list's `topo_order` cannot schedule a cycle. The tree
  makes a generator that reads another leaf into a dependent join, so
  with no step list the guard has nothing to protect and can go.
  Narrowing it by hand was tried and gave wrong answers: `from x, y
  where x > 0 andalso x < y andalso y < 10` returned 81 rows instead
  of 36, because the same set feeds the range strategy, where two
  bounds that read each other do over-enumerate.

## Where it stands

Landed, each gated with `fullMake --no-clean` and
`etc/check-convergence.py`:

* Deleted the dead `Expr::Exists`/`Expr::Forall` Core variants, which
  nothing built.
* Grounding runs once, over the declaration, not also per query in
  the resolver. The resolver builds a query from the inside out, so
  grounding there answered a nested query's constraints before the
  query that encloses it had been seen.
* `exists` is `Relational.nonEmpty` over a query and `forall` its
  negation, as morel-java writes them. The step that tests for
  existence survives only as a step-list artifact: a query the tree
  declines has its calls written back to the step before the old
  passes run, and a function body is stored in that shape, because a
  body reaches those passes by being put in place of a call.
* A tuple or record `elem` may have fixed positions: `(x, 2) elem
  pairs` scans `pairs` under the pattern `(x, 2)`, whose literal
  filters by matching. This is morel-go's `patForExp`, as
  `generators.rs`'s `pat_for_exp`, except that anything neither a
  variable, a literal nor a tuple declines rather than getting a
  fresh name. A record is written as a tuple in `Core` but matched
  by a `Pat::Record`, as in morel-java, so the tree grounder's
  pattern walkers read either through `Pat::components`.
* A node binds named rows, as morel-java's does: `Row` on a
  filter, projection, group and sort, `JoinRows` on a join, each a
  unique `v$N` from `core::fresh_name`, and `Expr::Input` is gone. A
  join is dependent when its right input reads its left row. A pass
  builds a node over the placeholders `$0` and `$1`, which
  `Rel::bind` names, and reads one through `Rel::open`, which puts
  the placeholders back; so the grounder's reasoning is unchanged.
  The printer opens a node to print its arguments, and the plan
  text did not change.
* A row node binds `ordinal` as morel-java's does: `Row.ordinal`,
  which `Rel::bind` gives a node exactly when its expressions read
  the `$ordinal` placeholder. The translator turns a step's
  `ordinal` into the placeholder for the node the step becomes. A
  query nested in a per-row expression that reads the enclosing
  position -- a binder holding it, or `ordinal` where it evaluates
  once, before its first row -- reads it through a `let`, as it
  reads the enclosing row; each `let` is there only where the nested
  tree reads its name, row outside position, and the plan text
  matches morel-java's. The grounder keeps a conjunct that reads
  `$ordinal` out of the constraints, and does not merge two filters
  where either reads it. The lowerer yields a counted row as the
  record `{w$N, ordinal$w$N}`, the shape the resolver gives it.
  A pair under one binder ran, but a query nested in a yield that
  read an enclosing `let` read the wrong slot through it: the step
  list's compiler has a bug there that no query the resolver
  builds reaches.
* A query in a function body is left alone and grounded where the
  function is called. What bounds its variables may be an argument,
  and grounding it where it is written seals away the constraints the
  caller reads.

Measured over the whole corpus, the tree grounder grounds 214
queries and declines 46. (A further 36 report no tree; those are the
fallback's step form being retried, and are benign.) The 46 have to
reach about zero before the step list can go.

## The 46, by cause

| n | cause |
| --- | --- |
| 8 | recursive predicates and transitive closure: `path`, `isAncestor`, `odd_path`, `cousin` |
| 8 | abs and nonlinear arithmetic: `abs x > 5`, `(x+2)*(x-3) = 0`, `x*y = 100`, `x+y = ~1`, `x < y andalso y < x+10` |
| 1 | a tuple `elem` naming a variable bound already: `from x in [1, 2, 3], y where (x, y) elem pairs` |
| 3 | a nested `exists` under a row binder: `let val v = $0 in nonEmpty (...) end` |
| 2 | `Range.contains`: `#contains Range (AT_LEAST 1) x` |
| 2 | a bare extent with no constraint, correctly ungroundable |

Reproduce the tally with:

```
for f in tests/script/*.smli tests/script/*/*.smli; do
  MOREL_REL_DEBUG=1 ./target/debug/morel --directory=tests/script \
    --idempotent $f 2>>/tmp/g.txt >/dev/null
done
grep -c '^grounded:' /tmp/g.txt
grep '^ground: declined' /tmp/g.txt | sed 's/ -- .*//' | sort | uniq -c
```

Pair each `ground: declined` with the `ground: tree` line above it to
see which tree failed.

## Stages, in order

**B′. What `ordinal` and `current` still decline.** Of the 123
the translator declined, 43 remain (count them with
`MOREL_SHADOW_TALLY=1 cargo test --test smile -- --nocapture`):

| n | reason |
| --- | --- |
| 36 | `ordinal` or `current` where a query evaluates it once, before its first row -- a count, a set operand -- with no enclosing query: the language rejects it at the top level ("'ordinal' is only valid in a query"), and the shadow, which translates a nested query on its own as well, sees it there. Correctly declined. |
| 4 | `ordinal` in a later scan's source, which no node binds. |
| 3 | `ordinal` in a join condition; morel-java's `Join` has an ordinal binder, this port's `JoinRows` does not yet. |

`current` translates as morel-java resolves it: the value of the
one binder where the row is an atom, otherwise the record of the
binders, which is the element itself where the element is that
record. morel-java throws on `from i in ... yield i mod 3 distinct
order DESC (current)` ("cannot change position: CURRENT"), so that
plan has no oracle.

**Before C: what the translator still declines.** C has the
resolver build every query as a tree, with no step list to fall
back to, so the translator's declines are a forecast of what C
meets. On 2026-09-30 the shadow declined 354 queries. Reproduce the
list by printing `reason` and `exp` from `shadow_query` for every
`None` and running each script with `--idempotent`. They sort into
three kinds.

*Artifacts of the step list, which C and E dissolve: 210.*

| n | reason | why it goes away |
| --- | --- | --- |
| 183 | a query that tests for existence | A query with no unbounded extent is not grounded on its tree, and the step-list path rewrites its `nonEmpty` calls back into `exists` steps (`as_exists_steps`). A resolver that builds trees emits `nonEmpty` over a tree. |
| 14 | a tree whose type is not the query's | The step-list grounder's own output, such as the seed of a transitive closure, `from (x, y) in edges yield (x, y)` over records, which no user could write (it is a type error). Not every one was traced. |
| 13 | a scan source over the enclosing row | The step-list grounder's transitive closures, `iterate (...) (fn (__tc_all, __tc_new) => ...)`. Once a scan source may hold a query, these get further and decline as "a tree whose type is not the query's", which then counts 26, every one the step-list grounder's output. |

The 9 "scan over something that is not a collection" are extents
the grounder left unbounded: the 46 grounder declines, seen again.

*Correct declines: 36.* `ordinal` or `current` evaluated once, in a
count or a set operand, with no enclosing query; see B′.

*Real gaps: 99.* morel-java gives the plan text for each, except
one: it throws on `... distinct order DESC (current)` ("cannot
change position: CURRENT").

| n | gap | morel-java's plan |
| --- | --- | --- |
| ~~42~~ | a query whose value is a `compute`, not a collection | closed: `#only Relational (r$0)` over `project [#sum $0]` over `group [] [sum = ...]` |
| ~~8~~ | `compute elements`, `compute #id Fn over i` | closed: the same, `project [#elements $0]` over `group [] [elements = #id Fn over $0]` |
| ~~11~~ | a group key with no name: `group x + y`, `group ordinal mod 2`, `compute 1 + 2` | closed: the key labelled `v$0`, then `project [#\`v$0\` $0]`; an unnamed `compute` is `project [1 + 2]` over `group []`, and an aggregate whose function has no name is `aggregate` |
| ~~1~~ | a tuple group key, `group (x + y, x - y)` | closed: `group [v$0 = (..., ...)]` |
| ~~12~~ | scans that bind nothing: `from _ in ...`, `from () in ...`, `from {} in ...` | closed: `project [()]` over the join. (morel-java throws only on the shadow's printed form, `from (_) in ...`; written as source it prints this plan.) |
| ~~5~~ | `distinct` followed by a set operator | closed: `union [all]` over `project [#i $0]` over `group [i = $0]` |
| ~~5~~ | a `let val rec` in a per-row expression | closed. morel-java's resolver writes a `val rec` that is not recursive as a `val`, and simultaneous non-function bindings as a tuple and a `case`; this port's keeps them as written, so those two plans differ in `Core`, not in the tree. |
| ~~4~~ | a query whose row names an unbound binder: 2 `compute elements` over a tuple pattern, 2 in `check.smli` | closed: the first by `compute`; the second were a query declared with an alias (`depts = dept bag check ...`), whose tree's types carry no alias. The tree keeps its own type, as morel-java prints it. |
| ~~2~~ | a cons pattern, `from (hd :: tl) in lists` | closed, with one difference of text: morel-java's resolver writes the pattern's calls as `List`'s members, `#hd List $0`, `not (#null List $0)`; this port's tree writes them `hd $0`, `not (null $0)`. A built-in function here prints bare where it has a global name, whoever wrote it, and the translator has no `List` structure to select from. The shape is morel-java's. |
| ~~1~~ | a correlated outer join | closed: `join [left] [v$0] [#units $1 > 2]` over the right input `#items v$0` |
| ~~1~~ | a scan source that applies a function to a nested query (`descendants2 ... (from ...)` in `hybrid.smli`) | closed: `f ([]) (r$0)`, the nested query broken out |
| ~~1~~ | `from n: nat in ...`, a type with a `check` | closed by comparing types with their aliases expanded; but an unbounded scan of `n: nat` prints `extent "nat"` and `nat list` where morel-java prints `extent "int"` and `int list`. The type is the resolver's, and the grounder reasons with it. |
| 7 | `ordinal` in a later scan's source or a join condition | see B′ |

Closing the `compute` gap closed two more that the table did not
show. A group's part that is not `f over e` -- `from r in elements
compute sum over r.j`, `10 + 2 * sum over i`, `1 + 2` -- is
computed by a projection after the group, which computes each
aggregate the part holds under its function's name, and `elements`
as `#id Fn over` the row where the part reads it; and `elements` is
the row as the query sees it, `current`, not the bare element. Both
are morel-java's plans. morel-java also does not fold a group's
list of keys or aggregates between its items, and now neither does
this port.

These are the ones to close in the translator before C. A gap closed
there is a case `resolve_step` is known to need, with its plan text
already checked against morel-java; a gap found during C is found
in the middle of the rewrite. In order of size: the scalar
`compute`, the unnamed key, the scans that bind nothing, then the
rest.

**C. The resolver builds trees.** `resolve_step`, about 230 lines,
replaces `from_builder.rs`'s 1319.

**D. The compiler compiles `Rel`.** About 950 of `compiler.rs`'s 2968
lines are step-list query compilation: the `Expr::From` arm (32),
`create_row_sink_factory` (767), and its helpers. Decide up front
whether `row_sink.rs`'s 1757 lines are reused or replaced; its 18
sink types map almost one to one onto `StepKind`, and
`OrdinalRowSink`/`OrdinalFilterRowSink` have no tree counterpart.

**E. Delete.** `from_builder.rs` (1597), `expander.rs` (about 4350 of
4509), `rel_lowerer.rs` (about 870 of 1154), `rel_translator.rs`
(1877), and the step-walking arms in `inliner.rs`, `replacer.rs`,
`var_collector.rs`, `free_finder.rs` and `progressive_widen.rs`
(about 600). First move the shared helpers those files host, about
430 lines: `DatatypeMap`, `FnEnv`, `list_bounds`, `expr_eq`,
`and_all`, `build_eq` and `collect_fn_bindings` out of
`expander.rs`; `component_count`, `field_at`, `replace_inputs_with`,
`substitute_name` and `map_children` out of `rel_lowerer.rs`.

Net: on the order of 8 to 9 thousand lines removed, against whatever
the new `Rel` compiler costs.

## How to work

Every commit is gated with `fullMake --no-clean` and then
`python3 etc/check-convergence.py --java-repo ~/dev/morel.4 HEAD`.
Never chain a commit after a background wait in one shell command;
check the exit code first.

`etc/pull-passing.py --java-repo ~/dev/morel.4 [--apply] FILE...`
regenerates a script as the largest passing subset of morel-java's.
Run it without `--apply` first and only apply when the new size is at
least the current one: `relational.smli` and `blog.smli` carry
port-native statements and lose them otherwise.

morel-go, freshly built, is the best oracle for what morel-java does.
The binary checked out in the working tree is stale and ignored by
git; build your own:

```
cd ~/dev/morel-go.0 && go build -o /tmp/morel-go ./cmd/morel
```

Debug switches: `MOREL_REL_DEBUG` traces the grounder,
`MOREL_REL_LOWER` runs every query as the step list its tree lowers
to.
