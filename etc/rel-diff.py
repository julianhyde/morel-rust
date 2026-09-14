#!/usr/bin/env python3
# Licensed to Julian Hyde under one or more contributor license
# agreements.  See the NOTICE file distributed with this work
# for additional information regarding copyright ownership.
# Julian Hyde licenses this file to you under the Apache
# License, Version 2.0 (the "License"); you may not use this
# file except in compliance with the License.  You may obtain a
# copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
# either express or implied.  See the License for the specific
# language governing permissions and limitations under the
# License.
"""Asks morel-java and morel-rust for the plan of the same query, and
diffs the answers.

`Sys.planOf e` prints the relational tree of the query `e`, and that
text is the cross-implementation contract (morel-java's `spec.md` §6 on
its `449-tree` branch). The conformance suite pins fifteen queries. This
pins every query in a `.smli` file, by replaying the file in both shells
and asking for the plan of each `from` statement as it goes.

Replaying rather than extracting, because a query needs the
declarations above it: `scott`, `pairs`, a `fun` it calls. A marker
declaration before each statement anchors the two outputs against each
other, so a statement that compiles in one implementation and not the
other shifts nothing.

A marker is a declaration, `val relDiff = 7`, rather than a string
expression, because an expression statement sets `it` and a declaration
does not.

**A shell that dies takes the rest of the file with it**, and both of
them do: the replay walks into statements that no test runs, and an
uncaught exception or a panic ends the session. So the marker before
each statement is also a progress report, and a run that stops short
names the statement it stopped on. That statement is dropped and the
file replayed, until the shell reaches the end; what was dropped is
reported, because a shell that dies on a query is a finding of its own.

Usage:

    etc/rel-diff.py tests/script/relational.smli
    etc/rel-diff.py --java ~/dev/morel.4 tests/script/*.smli

Needs a built morel-java: `./morel` in the directory `--java` names.
Not part of the test suite, which has no JVM.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import enable_queries  # noqa: E402  (needs the path set first)

DEFAULT_JAVA = os.path.expanduser("~/dev/morel.4")
DEFAULT_RUST = "./target/debug/morel"

# Where each implementation's shell must run, so that a script's
# `useSilently "scott.smli"` finds the file it names.
JAVA_SCRIPTS = "src/test/resources/script"

# What every query's plan is asked at, so that a fold is the same fold.
PREAMBLE = 'Sys.set ("stringDepth", ~1);\nSys.set ("lineWidth", 78);\n'

# The marker before a statement, and the one before the plan it asks
# for. Both are declarations, so that neither disturbs `it`.
MARKER = "relDiff"
PLAN_MARKER = "relDiffPlan"

# How many times a file is replayed before we give up dropping the
# statements that kill a shell.
MAX_ATTEMPTS = 40


@dataclass
class Case:
    """One query, and what each implementation said its plan was."""

    ordinal: int
    query: str
    java: Optional[str] = None
    rust: Optional[str] = None
    java_died: bool = False
    rust_died: bool = False

    def agree(self) -> bool:
        return self.java == self.rust

    def kind(self) -> str:
        """Classifies what the two said, because most of what differs is
        not a disagreement.

        A tree ends in a newline, because every node line does; a
        translator that declined printed the Core expression instead,
        and that does not. So the four answers separate without either
        implementation being asked how it feels about the query.
        """
        if self.java_died or self.rust_died:
            return "killed a shell"
        java, rust = tree(self.java), tree(self.rust)
        if self.java is None and self.rust is None:
            return "neither compiled"
        if self.rust is None:
            return "morel-java only"
        if self.java is None:
            return "morel-rust only"
        if not java and not rust:
            return "both declined"
        if not rust:
            return "morel-rust declined"
        if not java:
            return "morel-java declined"
        return "agree" if self.agree() else "DIFFER"


def tree(answer: Optional[str]) -> bool:
    """Returns whether an answer is a tree rather than a step list.

    A tree ends in a newline, because every node line does, and a
    translator that declined printed the Core expression instead.

    It is not exact, and the inexactness is a finding rather than a
    nuisance. `spec.md` §1 has no leaf constructor, so a query that
    translates to a bare expression -- `from`, `from u: unit` -- has a
    tree with no node in it. morel-rust prints that as a node line with
    its type, `[()] : unit list`, and morel-java prints the expression,
    `[()]`. So a decline and a node-free tree are the same text in
    morel-java, and "morel-java declined" is an upper bound until the
    two agree on how a query with no node prints.
    """
    return bool(answer) and answer.endswith("\n")


@dataclass
class Replay:
    """A `.smli` file as the harness replays it: every statement, and
    the query some of them are."""

    path: str
    statements: List[str] = field(default_factory=list)
    queries: Dict[int, str] = field(default_factory=dict)


@dataclass
class Run:
    """What one shell made of one replay."""

    plans: Dict[int, str] = field(default_factory=dict)
    # Statements it died on, and whether the plan or the statement did it.
    deaths: List[Tuple[int, str]] = field(default_factory=list)
    attempts: int = 0


def statements(path: str) -> List[str]:
    """Returns the input statements of a `.smli` file, in order, without
    their expected output."""
    with open(path, encoding="utf-8") as f:
        lines = f.readlines()
    blocks = enable_queries.parse_blocks(lines, 0, len(lines))
    return [b.input_text for b in blocks]


def query_of(statement: str) -> Optional[str]:
    """Returns the query a statement is, or None where it is not one.

    Only a statement that *is* a query, because `Sys.planOf` takes an
    expression and a declaration is not one. Comments are stripped from
    the front, and the trailing semicolon from the end.
    """
    s = strip_comments(statement).strip()
    if not s.endswith(";"):
        return None
    s = s[:-1].strip()
    if not s.startswith("from"):
        return None
    # Two statements on one line would make the tail of this one a
    # statement of its own, which `Sys.planOf` cannot wrap.
    if ";" in s:
        return None
    return s


def strip_comments(s: str) -> str:
    """Removes `(* ... *)` and `(*) ...` comments, outside string
    literals."""
    return walk_comments(s)[0]


def unclosed_comment(s: str) -> bool:
    """Returns whether `s` leaves a `(*` block comment open.

    A `.smli` file comments a statement out by wrapping it, and the
    `*)` that closes the wrapper sits at the head of the *next* block
    the parser hands back, because the parser splits on `;` without
    tracking comments. Fed to a shell one block at a time, that is an
    unterminated comment: the shell waits for the rest of it, answers
    nothing more, and reads from outside exactly like a shell that has
    died. Ten of the corpus's twenty-two stops were this.
    """
    return walk_comments(s)[1] > 0


def walk_comments(s: str) -> Tuple[str, int]:
    """Returns `s` without its comments, and the `(*` depth it ends
    at."""
    out = []
    depth = 0
    i = 0
    in_string = False
    while i < len(s):
        c = s[i]
        if in_string:
            out.append(c)
            if c == "\\" and i + 1 < len(s):
                out.append(s[i + 1])
                i += 2
                continue
            if c == '"':
                in_string = False
            i += 1
            continue
        if depth == 0 and c == '"':
            in_string = True
            out.append(c)
            i += 1
            continue
        # `(*)` is a line comment at any depth. Inside a block comment
        # it does *not* open a nested one -- `simple.smli` says so, and
        # names the case -- and reading it as `(*` left the block open
        # for the rest of the file.
        if s.startswith("(*)", i):
            j = s.find("\n", i)
            i = len(s) if j < 0 else j
            continue
        if s.startswith("(*", i):
            depth += 1
            i += 2
            continue
        if s.startswith("*)", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(c)
        i += 1
    return "".join(out), depth


# `set("mode", "validate")`, which tells a shell to echo the expected
# output of what follows rather than evaluate it.
MODE = re.compile(r'^\s*(Sys\.)?set\s*\(\s*["\']mode["\']', re.M)


def evaluating(statement: str) -> str:
    """Removes a mode directive from a statement.

    The replay evaluates everything, because a plan is only asked of a
    query that runs. A directive left in would put the shell into
    validate mode, where it answers nothing -- which reads from outside
    exactly like a shell that has died.

    This is also why the replay walks into statements the corpus has
    bracketed off as known to fail. That is the harness working: what
    those brackets hide is worth seeing.
    """
    kept = [
        line for line in statement.split("\n") if not MODE.match(line)
    ]
    return "\n".join(kept)


def read(path: str) -> Replay:
    """Reads one `.smli` file into the statements the harness replays.

    A statement that leaves a comment open is joined to the one after
    it, and to the one after that, until the comment closes: a block
    the parser split inside a `(* ... *)` is not a statement, and
    feeding half of one to a shell stops it.
    """
    replay = Replay(path=path)
    pending = []
    for statement in statements(path):
        pending.append(evaluating(statement))
        statement = "\n".join(pending)
        if unclosed_comment(statement):
            continue
        pending = []
        if not statement.strip():
            continue
        i = len(replay.statements)
        replay.statements.append(statement)
        query = query_of(statement)
        if query is not None:
            replay.queries[i] = query
    if pending:
        replay.statements.append("\n".join(pending))
    return replay


def script(
    replay: Replay, dead_statements: Set[int], dead_plans: Set[int]
) -> Tuple[str, int]:
    """Builds the text fed to a shell, and the last marker it holds.

    A statement in `dead_statements` is left out, and so is the plan it
    would have asked for; a statement in `dead_plans` stays and its plan
    does not. Both sets hold what killed the shell on an earlier
    attempt.
    """
    parts = [PREAMBLE]
    last = -1
    for i, statement in enumerate(replay.statements):
        if i in dead_statements:
            continue
        parts.append(f"val {MARKER} = {i};\n")
        parts.append(statement)
        if not statement.endswith("\n"):
            parts.append("\n")
        last = i
        query = replay.queries.get(i)
        if query is not None and i not in dead_plans:
            parts.append(f"val {PLAN_MARKER} = {i};\n")
            parts.append(f"Sys.planOf ({query});\n")
            last = i
    return "".join(parts), last


def run(binary: str, cwd: Optional[str], text: str) -> str:
    """Feeds a script to a shell and returns what it wrote to stdout."""
    result = subprocess.run(
        [binary],
        input=text,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        encoding="utf-8",
        cwd=cwd,
        timeout=1800,
    )
    return result.stdout


# `val it = "..." : string`, possibly folded over several lines, which is
# how a shell prints the answer of `Sys.planOf`. The literal is matched
# exactly -- a run of anything but a quote or a backslash, or a
# backslash and whatever it escapes -- because a plan holds quotes of
# its own, and a greedy match would swallow the next answer with them.
PATTERN = 'val it =\\s*("(?:[^"\\\\]|\\\\.)*")\\s*:\\s*string'
ANSWER = re.compile(PATTERN, re.S)

# A marker, whichever of the two it is. `relDiffPlan` is written first
# so that the alternation does not stop at its prefix.
PROGRESS = re.compile(r"val (%s|%s) = (\d+)" % (PLAN_MARKER, MARKER))


def clean(output: str) -> str:
    """Strips the shell's prompt, which differs between the two, and
    joins what a fold split, since an answer is one string literal."""
    return "\n".join(re.sub(r"^- ", "", line) for line in output.split("\n"))


def plans(joined: str) -> Dict[int, str]:
    """Returns the plan each plan marker's query printed, by statement."""
    out = {}
    marks = list(PROGRESS.finditer(joined))
    for i, mark in enumerate(marks):
        if mark.group(1) != PLAN_MARKER:
            continue
        end = marks[i + 1].start() if i + 1 < len(marks) else len(joined)
        match = ANSWER.search(joined[mark.end() : end])
        if match:
            out[int(mark.group(2))] = unescape(match.group(1))
    return out


def reached(joined: str) -> Optional[Tuple[str, int]]:
    """Returns the last marker a shell got to, or None if it got to
    none."""
    last = None
    for mark in PROGRESS.finditer(joined):
        last = (mark.group(1), int(mark.group(2)))
    return last


def unescape(literal: str) -> str:
    """Turns an ML string literal into the text it stands for."""
    body = literal[1:-1]
    out = []
    i = 0
    while i < len(body):
        c = body[i]
        if c == "\\" and i + 1 < len(body):
            nxt = body[i + 1]
            out.append({"n": "\n", "t": "\t", '"': '"', "\\": "\\"}.get(nxt, nxt))
            i += 2
            continue
        out.append(c)
        i += 1
    return "".join(out)


def ask(replay: Replay, binary: str, cwd: Optional[str], verbose: bool) -> Run:
    """Replays a file in one shell, dropping whatever kills it, until it
    reaches the end.

    The last marker a run printed is the statement it was on when it
    died, and which of the two markers it was says whether the statement
    or the plan we asked for did the killing. So each attempt drops one
    thing and learns one fact; a file that kills nothing costs one
    attempt.
    """
    result = Run()
    dead_statements: Set[int] = set()
    dead_plans: Set[int] = set()
    for _ in range(MAX_ATTEMPTS):
        text, last = script(replay, dead_statements, dead_plans)
        result.attempts += 1
        joined = clean(run(binary, cwd, text))
        result.plans.update(plans(joined))
        mark = reached(joined)
        if mark is None or mark[1] >= last:
            return result
        kind, i = mark
        if kind == PLAN_MARKER:
            dead_plans.add(i)
            result.deaths.append((i, "plan"))
        else:
            dead_statements.add(i)
            dead_plans.add(i)
            result.deaths.append((i, "statement"))
        if verbose:
            print(f"  died on {kind} {i}; dropping it and replaying")
    return result


def compare(
    path: str, java_dir: str, rust: str, verbose: bool
) -> Tuple[List[Case], Run, Run]:
    """Runs one file through both shells, and returns every case."""
    replay = read(path)
    if not replay.queries:
        return [], Run(), Run()
    if verbose:
        print(f"{path}: morel-java")
    java = ask(
        replay,
        os.path.join(java_dir, "morel"),
        os.path.join(java_dir, JAVA_SCRIPTS),
        verbose,
    )
    if verbose:
        print(f"{path}: morel-rust")
    rust_run = ask(
        replay,
        os.path.abspath(rust),
        os.path.dirname(os.path.abspath(path)),
        verbose,
    )
    java_dead = {i for i, _ in java.deaths}
    rust_dead = {i for i, _ in rust_run.deaths}
    cases = []
    for i in sorted(replay.queries):
        cases.append(
            Case(
                ordinal=i,
                query=replay.queries[i],
                java=java.plans.get(i),
                rust=rust_run.plans.get(i),
                java_died=i in java_dead,
                rust_died=i in rust_dead,
            )
        )
    return cases, java, rust_run


# ---------------------------------------------------------------------
# Classification
#
# Most of what differs is one of a few shapes repeated hundreds of
# times, so the harness says which shape rather than showing the text.
# A shape is a *canonicalization*: a rewrite applied to both answers
# that erases one distinction and nothing else. A case is explained
# when the two texts are equal after every rewrite has run -- equal
# exactly, so a rewrite cannot explain a case it did not account for --
# and the rewrites it needed are its class. Leaving one out and asking
# whether the two are still equal is what "needed" means, so a rewrite
# that fired without mattering does not get the credit.
#
# Applying a rewrite to *both* sides is what makes this safe. A
# one-sided rewrite would have to know which implementation writes
# which form, and would turn a form the two already agree on into a
# difference.


# What morel-java prints as an infix operator: every `Op` with a padded
# name, which is what `AstWriter.infix` looks up in `Op.BY_OP_NAME`.
# Longest first, so that the alternation does not stop at a prefix.
INFIX_OPS = sorted(
    [
        "div", "mod", "elem", "notelem", "andalso", "orelse", "implies",
        "before", "o", "::", "@", "<=", ">=", "<>", ":=", "*", "/", "^",
        "+", "-", "<", ">", "=",
    ],
    key=len,
    reverse=True,
)

CALL = re.compile(
    r"#(%s) ([A-Z]\w*) \(" % "|".join(re.escape(o) for o in INFIX_OPS)
)

# `#size String`, `#abs Int`: a built-in reached through the structure
# it lives in. A field selector, `#deptno $0`, is not one, because a
# structure's name is capitalized and a record label is not.
SELECTOR = re.compile(r"#(\w+) ([A-Z]\w*)")

# `sum$real`: a name that carries the instance an overload resolved to.
# `t$0` and `v$1` are not, because what follows the `$` is a number.
INSTANCE = re.compile(r"\b(\w+)\$([a-zA-Z_]\w*)")


def closing(text: str, i: int) -> Optional[int]:
    """Returns the index of the parenthesis that closes the one at `i`,
    or None."""
    depth = 0
    quoted = False
    while i < len(text):
        c = text[i]
        if quoted:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                quoted = False
        elif c == '"':
            quoted = True
        elif c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return None


def split_args(text: str) -> List[str]:
    """Splits `a, b` at the commas that are not inside anything."""
    parts = []
    depth = 0
    quoted = False
    start = 0
    i = 0
    while i < len(text):
        c = text[i]
        if quoted:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                quoted = False
        elif c == '"':
            quoted = True
        elif c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif c == "," and depth == 0:
            parts.append(text[start:i])
            start = i + 1
        i += 1
    parts.append(text[start:])
    return parts


def as_infix(text: str) -> str:
    """`#- Int ($0, 5)` becomes `$0 - 5`.

    morel-rust writes an arithmetic operator as the call it is in Core;
    morel-java turns it back into the operator the author wrote. This is
    finding 6, and it touches nearly every plan.
    """
    at = 0
    while True:
        match = CALL.search(text, at)
        if match is None:
            return text
        end = closing(text, match.end() - 1)
        args = split_args(text[match.end() : end]) if end is not None else []
        if len(args) != 2:
            at = match.end()
            continue
        infix = f"{args[0].strip()} {match.group(1)} {args[1].strip()}"
        text = text[: match.start()] + infix + text[end + 1 :]
        at = match.start()


def unqualified(text: str) -> str:
    """`#abs Int $0` becomes `abs $0`, and so does `#size String`.

    Applied to both answers, so a built-in the two agree to qualify --
    `#sub String` -- stays qualified in both and is not a difference.
    """
    return SELECTOR.sub(r"\1", text)


def ungeneric(text: str) -> str:
    """`sum$real` becomes `sum`: the instance an overload resolved to."""
    return INSTANCE.sub(r"\1", text)


def finished(line: str) -> bool:
    """Returns whether a node's line is over.

    Indentation cannot say: a child is indented two from its parent, and
    so is the second line of a record that folded. What separates them is
    that a node's line ends -- with its type, or, for a fragment's head,
    with the `=` before its tree -- and closes every bracket it opened,
    while a line that folded is still inside one.
    """
    depth = 0
    quoted = False
    i = 0
    while i < len(line):
        c = line[i]
        if quoted:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                quoted = False
        elif c == '"':
            quoted = True
        elif c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        i += 1
    return depth == 0 and (" : " in line or line.rstrip().endswith("="))


def unfold(text: str) -> str:
    """Joins the lines a fold split.

    A line belongs to the one above it if it is indented further and the
    one above has not finished. This erases finding 8, where a leaf that
    is a list folds in one implementation and not the other, and every
    other place the two choose different break points.
    """
    out: List[str] = []
    indent = None
    for line in text.split("\n"):
        if not line.strip():
            out.append(line)
            indent = None
            continue
        here = len(line) - len(line.lstrip())
        if indent is not None and here > indent and not finished(out[-1]):
            out[-1] = out[-1].rstrip() + " " + line.strip()
        else:
            out.append(line)
            indent = here
    return "\n".join(out)


AGGREGATE = re.compile(r"\(")


def unparenthesized(text: str) -> str:
    """`(sum over #sal $0)` becomes `sum over #sal $0`.

    morel-rust parenthesises an aggregate and morel-java does not; the
    parentheses are how an aggregate has printed in every plan, so this
    is a `main` conversation rather than a branch one, and meanwhile it
    is a class.
    """
    at = 0
    while True:
        open_at = text.find("(", at)
        if open_at < 0:
            return text
        close_at = closing(text, open_at)
        if close_at is None:
            return text
        inner = text[open_at + 1 : close_at]
        if " over " in split_args(inner)[-1] and len(split_args(inner)) == 1:
            text = text[:open_at] + inner + text[close_at + 1 :]
            at = open_at
        else:
            at = open_at + 1


# A projection that takes the one field out of a group's element, and
# one that puts it back. `spec.md` §3 says a group's element is "a
# record of the key and aggregate types, or the single field's type if
# there is exactly one".
UNWRAP = re.compile(r"^(\s*)project \[#(\w+) \$0\] : (.*)$")
WRAP = re.compile(r"^(\s*)project \[\{(\w+) = \$0\}\] : (.*)$")


def atomized(text: str) -> str:
    """Drops the projection either implementation puts over a group of
    one field.

    morel-rust reads §3 as morel-java does not: its group of one field
    has that field's type for an element, and morel-java's has the
    record. So morel-java projects the field out where the query wants
    the value, and morel-rust builds the record back where the query
    wants the record -- the same disagreement seen from each end, and
    finding 7.
    """
    lines = text.split("\n")
    out: List[str] = []
    i = 0
    while i < len(lines):
        match = UNWRAP.match(lines[i]) or WRAP.match(lines[i])
        child = lines[i + 1] if i + 1 < len(lines) else ""
        stem = match.group(1) + "  group " if match else None
        if stem is None or not (
            child.startswith(stem) and ("[" + match.group(2) + " = ") in child
        ):
            out.append(lines[i])
            i += 1
            continue
        # The projection goes, the group takes the projection's type,
        # and the subtree it heads comes up two spaces.
        indent = len(match.group(1))
        out.append(child[2:].rsplit(" : ", 1)[0] + " : " + match.group(3))
        i += 2
        while i < len(lines):
            line = lines[i]
            if line.strip() and len(line) - len(line.lstrip()) <= indent:
                break
            out.append(line[2:] if line.startswith("  ") else line)
            i += 1
    return "\n".join(out)


# `fn $col => count (#fromList Bag $col)`: the function an aggregate
# desugars to, which morel-java prints and morel-rust does not.
DESUGARED = re.compile(r"fn \$col\w* => (\S+) \(#fromList Bag \$col\w*\)")


def resugared(text: str) -> str:
    """`fn $col => count (#fromList Bag $col)` becomes `count`."""
    return DESUGARED.sub(r"\1", text)


REWRITES = [
    ("fold", unfold),
    ("aggregate function", resugared),
    ("infix", as_infix),
    ("aggregate parens", unparenthesized),
    ("overload instance", ungeneric),
    ("structure name", unqualified),
    ("group of one key", atomized),
]


def canonical(text: str, rewrites) -> str:
    for _, rewrite in rewrites:
        text = rewrite(text)
    return text


def explain(case: Case) -> Tuple[bool, List[str]]:
    """Returns whether the rewrites account for a difference, and which
    of them were needed."""
    java, rust = case.java or "", case.rust or ""
    if canonical(java, REWRITES) != canonical(rust, REWRITES):
        return False, []
    needed = [
        name
        for i, (name, _) in enumerate(REWRITES)
        if canonical(java, REWRITES[:i] + REWRITES[i + 1 :])
        != canonical(rust, REWRITES[:i] + REWRITES[i + 1 :])
    ]
    if needed:
        return True, needed
    fired = [
        name
        for name, rewrite in REWRITES
        if rewrite(java) != java or rewrite(rust) != rust
    ]
    return True, fired


DIGITS = re.compile(r"\d+")
QUOTED = re.compile(r'"(?:[^"\\]|\\.)*"')


def shape(case: Case) -> str:
    """A key that groups the cases the rewrites do not explain, by the
    first line on which the two disagree."""
    java = canonical(case.java or "", REWRITES).split("\n")
    rust = canonical(case.rust or "", REWRITES).split("\n")
    for i in range(max(len(java), len(rust))):
        j = java[i] if i < len(java) else "(end)"
        r = rust[i] if i < len(rust) else "(end)"
        if j != r:
            return f"{blur(j)}  /  {blur(r)}"
    return "(equal)"


def blur(line: str) -> str:
    """Removes what makes one case different from the next like it."""
    return DIGITS.sub("#", QUOTED.sub('"_"', line.strip()))


def obituary(label: str, replay_run: Run, replay: Replay) -> List[str]:
    """Says what stopped a shell, because that is a finding, not a
    nuisance."""
    out = []
    for i, what in replay_run.deaths:
        text = replay.statements[i].strip().replace("\n", " ")
        if len(text) > 100:
            text = text[:97] + "..."
        which = "the Sys.planOf of" if what == "plan" else "statement"
        out.append(f"{label} stopped answering at {which} #{i}: {text}")
    return out


def report(path: str, case: Case) -> None:
    print(f"\n=== {case.kind()}: {path} #{case.ordinal}")
    if case.kind() == "DIFFER":
        explained, names = explain(case)
        print("class: " + (", ".join(names) if explained else "unexplained"))
    print(case.query)
    print("--- morel-java")
    print(case.java if case.java is not None else "(no answer)")
    print("--- morel-rust")
    print(case.rust if case.rust is not None else "(no answer)")


def gather(args) -> List[Tuple[str, List[Case], List[str]]]:
    """Returns, for each file, its cases and what it killed -- by
    running both shells, or by reading a file an earlier run saved."""
    if args.load:
        with open(args.load, encoding="utf-8") as f:
            saved = json.load(f)
        return [
            (
                entry["path"],
                [Case(**case) for case in entry["cases"]],
                entry["deaths"],
            )
            for entry in saved
        ]
    out = []
    for path in args.files:
        cases, java, rust = compare(path, args.java, args.rust, args.verbose)
        if not cases:
            continue
        replay = read(path)
        killed = obituary("morel-java", java, replay) + obituary(
            "morel-rust", rust, replay
        )
        out.append((path, cases, killed))
    if args.save:
        with open(args.save, "w", encoding="utf-8") as f:
            json.dump(
                [
                    {
                        "path": path,
                        "cases": [vars(case) for case in cases],
                        "deaths": killed,
                    }
                    for path, cases, killed in out
                ],
                f,
            )
    return out


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", help=".smli files to replay")
    parser.add_argument("--java", default=DEFAULT_JAVA, help="morel-java dir")
    parser.add_argument(
        "--rust", default=DEFAULT_RUST, help="morel-rust binary"
    )
    parser.add_argument(
        "--limit", type=int, default=0, help="report at most this many cases"
    )
    parser.add_argument(
        "--kind",
        default="DIFFER",
        help="which class to report: DIFFER, 'morel-java declined', "
        "'morel-rust declined', 'both declined', agree, 'killed a shell', "
        "unexplained (a DIFFER the rewrites do not account for), or all",
    )
    parser.add_argument(
        "--quiet", action="store_true", help="counts only, no cases"
    )
    parser.add_argument(
        "--verbose", action="store_true", help="say what each replay does"
    )
    parser.add_argument(
        "--save", help="write the cases to a JSON file, to read back later"
    )
    parser.add_argument(
        "--load", help="read the cases from a JSON file; runs no shell"
    )
    parser.add_argument(
        "--shapes",
        type=int,
        default=20,
        help="how many unexplained shapes to list",
    )
    args = parser.parse_args(argv)

    tally = Counter()
    classes = Counter()
    shapes = Counter()
    example: Dict[str, Tuple[str, int]] = {}
    shown = 0
    for path, cases, killed in gather(args):
        here = Counter(case.kind() for case in cases)
        tally.update(here)
        print(f"{path}: " + ", ".join(f"{n} {k}" for k, n in here.most_common()))
        for line in killed:
            print(f"  {line}")
        for case in cases:
            wanted = case.kind()
            if case.kind() == "DIFFER":
                explained, names = explain(case)
                key = ", ".join(names) if explained else "unexplained"
                classes[key] += 1
                example.setdefault(key, (path, case.ordinal))
                if not explained:
                    shapes[shape(case)] += 1
                    wanted = "unexplained"
            if args.quiet or args.kind not in ("all", wanted):
                continue
            if args.limit and shown >= args.limit:
                continue
            report(path, case)
            shown += 1
    print("\nTOTAL")
    for kind, n in tally.most_common():
        print(f"{n:6}  {kind}")
    if classes:
        differ = sum(classes.values())
        explained = differ - classes["unexplained"]
        print(
            f"\nWHAT DIFFERS: {explained} of {differ} accounted for by these"
            " rewrites, each counted in every case that needed it"
        )
        for name, _ in REWRITES:
            n = sum(k for key, k in classes.items() if name in key.split(", "))
            if n:
                key = next(
                    key for key in classes if name in key.split(", ")
                )
                path, ordinal = example[key]
                print(f"{n:6}  {name}  (e.g. {path} #{ordinal})")
        print(f"{classes['unexplained']:6}  unexplained")
    if shapes:
        print("\nUNEXPLAINED, by the first line that disagrees")
        for key, n in shapes.most_common(args.shapes):
            print(f"{n:6}  {key}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
