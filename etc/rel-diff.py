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
statement before each plan anchors the two outputs against each other,
so a statement that compiles in one implementation and not the other
shifts nothing.

Usage:

    etc/rel-diff.py tests/script/relational.smli
    etc/rel-diff.py --java ~/dev/morel.4 tests/script/*.smli

Needs a built morel-java: `./morel` in the directory `--java` names.
Not part of the test suite, which has no JVM.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass, field
from typing import List, Optional

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import enable_queries  # noqa: E402  (needs the path set first)

DEFAULT_JAVA = os.path.expanduser("~/dev/morel.4")
DEFAULT_RUST = "./target/debug/morel"

# Where each implementation's shell must run, so that a script's
# `useSilently "scott.smli"` finds the file it names.
JAVA_SCRIPTS = "src/test/resources/script"

# What every query's plan is asked at, so that a fold is the same fold.
PREAMBLE = 'Sys.set ("stringDepth", ~1);\nSys.set ("lineWidth", 78);\n'

MARKER = "rel-diff"


@dataclass
class Case:
    """One query, and what each implementation said its plan was."""

    ordinal: int
    query: str
    java: Optional[str] = None
    rust: Optional[str] = None

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
        java, rust = tree(self.java), tree(self.rust)
        if self.java is None or self.rust is None:
            return "unanswered"
        if not java and not rust:
            return "both declined"
        if not rust:
            return "morel-rust declined"
        if not java:
            return "morel-java declined"
        return "agree" if self.agree() else "DIFFER"


def tree(answer: Optional[str]) -> bool:
    """Returns whether an answer is a tree rather than a step list."""
    return bool(answer) and answer.endswith("\n")


@dataclass
class Script:
    """A replay of one `.smli` file, with a plan asked after each query."""

    text: str
    cases: List[Case] = field(default_factory=list)


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
        if s.startswith("(*)", i) and depth == 0:
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
    return "".join(out)


def build(path: str) -> Script:
    """Builds the replay script for one `.smli` file."""
    script = Script(text="")
    parts = [PREAMBLE]
    for statement in statements(path):
        parts.append(statement)
        if not statement.endswith("\n"):
            parts.append("\n")
        query = query_of(statement)
        if query is None:
            continue
        case = Case(ordinal=len(script.cases), query=query)
        script.cases.append(case)
        parts.append(f'"{MARKER} {case.ordinal}";\n')
        parts.append(f"Sys.planOf ({query});\n")
    script.text = "".join(parts)
    return script


def run(binary: str, cwd: Optional[str], text: str) -> str:
    """Feeds a script to a shell and returns what it wrote to stdout."""
    result = subprocess.run(
        [binary],
        input=text,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        encoding="utf-8",
        cwd=cwd,
        timeout=600,
    )
    return result.stdout


# `val it = "..." : string`, possibly folded over several lines, which is
# how a shell prints the answer of `Sys.planOf`. The literal is matched
# exactly -- a run of anything but a quote or a backslash, or a
# backslash and whatever it escapes -- because a plan holds quotes of
# its own, and a greedy match would swallow the next answer with them.
PATTERN = 'val it =\\s*("(?:[^"\\\\]|\\\\.)*")\\s*:\\s*string'
ANSWER = re.compile(PATTERN, re.S)


def answers(output: str) -> dict:
    """Returns the plan each marker's query printed, by marker."""
    # Strip the shell's prompt, which differs between the two, and join
    # what a fold split, since the answer is one string literal.
    lines = [re.sub(r"^- ", "", line) for line in output.split("\n")]
    joined = "\n".join(lines)
    out = {}
    pattern = re.compile(r'"%s (\d+)"' % MARKER)
    marks = list(pattern.finditer(joined))
    for i, mark in enumerate(marks):
        end = marks[i + 1].start() if i + 1 < len(marks) else len(joined)
        chunk = joined[mark.end() : end]
        match = ANSWER.search(chunk)
        if match:
            out[int(mark.group(1))] = unescape(match.group(1))
    return out


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


def compare(path: str, java_dir: str, rust: str) -> List[Case]:
    """Runs one file through both shells, and returns every case."""
    script = build(path)
    if not script.cases:
        return []
    java_out = run(
        os.path.join(java_dir, "morel"),
        os.path.join(java_dir, JAVA_SCRIPTS),
        script.text,
    )
    rust_out = run(
        os.path.abspath(rust), os.path.dirname(os.path.abspath(path)), script.text
    )
    java = answers(java_out)
    rust = answers(rust_out)
    for case in script.cases:
        case.java = java.get(case.ordinal)
        case.rust = rust.get(case.ordinal)
    return script.cases


def report(path: str, case: Case) -> None:
    print(f"\n=== {case.kind()}: {path} #{case.ordinal}")
    print(case.query)
    print("--- morel-java")
    print(case.java if case.java is not None else "(no answer)")
    print("--- morel-rust")
    print(case.rust if case.rust is not None else "(no answer)")


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="+", help=".smli files to replay")
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
        "'morel-rust declined', 'both declined', agree, or all",
    )
    parser.add_argument(
        "--quiet", action="store_true", help="counts only, no cases"
    )
    args = parser.parse_args(argv)

    tally = Counter()
    shown = 0
    for path in args.files:
        cases = compare(path, args.java, args.rust)
        if not cases:
            continue
        here = Counter(case.kind() for case in cases)
        tally.update(here)
        print(f"{path}: " + ", ".join(f"{n} {k}" for k, n in here.most_common()))
        for case in cases:
            if args.quiet or args.kind not in ("all", case.kind()):
                continue
            if args.limit and shown >= args.limit:
                continue
            report(path, case)
            shown += 1
    print("\nTOTAL")
    for kind, n in tally.most_common():
        print(f"{n:6}  {kind}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
