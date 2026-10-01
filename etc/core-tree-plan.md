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
* `ordinal` has no home in the tree, so the translator declines 123
  queries. morel-java's answer is the optional `ordinal` binder on a
  row node. This port instead has `materialize_ordinal`,
  `drop_ordinal`, `replace_ordinal`, `ORDINAL_SLOT`, and two row
  sinks.
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
* A query in a function body is left alone and grounded where the
  function is called. What bounds its variables may be an argument,
  and grounding it where it is written seals away the constraints the
  caller reads.

Measured over the whole corpus, the tree grounder grounds 213
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

**B. `ordinal` in the tree.** 123 declines. The rows are named
(above); what is left is to give `Row` an optional ordinal binder,
as morel-java's `RowRel` has, and keep printing `$ordinal`.

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
