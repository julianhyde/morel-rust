# Findings for morel-java, from building the tree twice

Four things morel-rust found in morel-java while implementing
`hydromatic/morel#449`'s relational tree against `spec.md` rather than
against the Java code. Every repro below is against
`julianhyde/449-tree` at tag `449-tree.3` (`01f24633`), fed to `./morel`
on stdin from `src/test/resources/script`.

They are ready to file as they stand. The branch's own record is
`plan.md`, where these are findings 5, 10, 17 and 20; this file is the
half of it that is morel-java's.

Two of them stop the shell dead, which is how they were found: a
differential harness replays a `.smli` file in both implementations and
asks each for `Sys.planOf` of every `from` statement, and a shell that
dies takes the rest of the file with it.

## 1. The plan printer crashes on a unary `~`

```
val emps = [{id=100,name="Fred",deptno=10}];
Sys.planOf (from e in emps yield ~e.deptno);
```

gives

```
java.lang.ClassCastException: class net.hydromatic.morel.ast.Core$Apply
  cannot be cast to class net.hydromatic.morel.ast.Core$Tuple
	at net.hydromatic.morel.ast.AstWriter.infix(AstWriter.java:390)
	at net.hydromatic.morel.ast.Core$Apply.unparse(Core.java:3246)
```

and the shell does not come back. Any node's argument will do -- a
`filter`, a `sort`, a `project`.

**Cause**, two lines apart in `Op.java`. `NEGATE("~ ")` reaches

```java
Op(String padded, int precedence, Assoc assoc) {
  this.left = precedence * 2 + (assoc == Assoc.LEFT ? 0 : 1);
```

with precedence 0 and `Assoc.NONE`, so a *prefix* operator comes out
with `left = 1`. `AstWriter.infix` reads `left > 0` as "binary infix"
and casts the single argument to a `Core.Tuple`:

```java
final Op op2 = Op.BY_OP_NAME.get(((Core.Id) a0).idPat.name);
if (op2 != null && op2.left > 0) {
  final List<Core.Exp> args = ((Core.Tuple) a1).args;   // line 390
```

`~1` is safe only because it folds to a literal before anything prints
it, which is why nothing in the suite sees this.

## 2. The shell mis-reads a backslash escape from stdin

```
val before = 1;
val a = "x\"y";
val after = 2;
```

prints `val before = 1 : int` and then nothing at all: the second
statement produces no output and the third never runs. `#"\"";` does the
same. `val c = "\"\"";` instead raises

```
stdIn:1.13-1.13 Lexical error at line 1, column 13.
  Encountered: '\' (92)
```

The *script* runner reads the same text correctly -- `pretty.smli` is
morel-java's own file and contains all three -- so this is the stdin
path alone. It costs a differential harness two files.

## 3. A plan's legend is not renumbered, so one binder gets two names

Binders are renumbered when a plan is printed, and the legend is not
included in the renumbering, so a name that appears in both the tree and
a type is printed twice under two names. Which second name you get
depends on what was compiled before.

```
Sys.set ("stringDepth", ~1);
val emps = [{id=100,name="Fred",deptno=10}];
(*) eight queries, to move the session's binder counter on
from e0 in emps order e0.deptno where ordinal > 1 yield e0.name;
from e1 in emps order e1.deptno where ordinal > 1 yield e1.name;
from e2 in emps order e2.deptno where ordinal > 1 yield e2.name;
from e3 in emps order e3.deptno where ordinal > 1 yield e3.name;
from e4 in emps order e4.deptno where ordinal > 1 yield e4.name;
from e5 in emps order e5.deptno where ordinal > 1 yield e5.name;
from e6 in emps order e6.deptno where ordinal > 1 yield e6.name;
from e7 in emps order e7.deptno where ordinal > 1 yield e7.name;
Sys.planOf (from e in emps order e.deptno where ordinal > 1);
```

gives a tree that says `v$0` and a legend that says `v$8`:

```
project [#e $0] : t$0
  filter [#v$0 $0 > 1] : t$1
    project [{e = $0, v$0 = $ordinal ()}] : t$1
      sort [#deptno $0] : t$0
        emps : t$0

t$0 {deptno:int, id:int, name:string} list
t$1 {e:{deptno:int, id:int, name:string}, v$8:int} list
```

Drop the eight warm-up queries and the same plan prints `v$0` in both
places, which is why no test can see it: every test starts from a cold
counter, where the allocated name and the printed name coincide.

A binder inside a *type* is text that a renumbering writer never sees.
It is `plan.md`'s own lesson one level out:

> A record label is printed as text, not through the identifier path. A
> renumbering writer that renames identifiers but not labels prints one
> binder under two names, which looks like a semantic bug and is not.

morel-rust is immune by construction, because it renumbers the finished
text rather than the writer's identifiers, and the legend is part of the
text.

## 4. A node-free tree and a decline print the same

```
Sys.planOf (from);        (*) "[()]"
Sys.planOf (from i in [1,2]);   (*) "[1, 2]"
```

`spec.md` §1 has no leaf constructor, so a query that translates to a
bare expression has a tree with no node in it, and printing the
expression is a defensible thing to do with one. But a query the
translator *declined* would print exactly the same way, and there is no
way to tell from the text which happened.

Two consequences, and the second is the one worth fixing:

- A differential harness cannot classify these. Fifteen queries across
  the shared corpus read as "morel-java declined" and are almost
  certainly all node-free trees; `from;` appears five times in
  morel-java's own corpus while `RelShadow.check` throws
  `AssertionError` wherever `RelTranslator.toRel` returns null, so the
  translator plainly does not turn them down.
- **`RelShadow`'s zero-decline invariant is unfalsifiable from
  outside.** The one place a decline would show up in the plan text is
  the one place the plan text says nothing.

morel-rust prints `[()] : unit list` -- a node line with its collection
type, like any other leaf. A sentence in §6 saying which is right
settles both, and the cross-implementation contract needs it either way.
