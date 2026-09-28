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
"""Regenerate morel-rust's `.smli` files as the largest subset of
morel-java's that morel-rust reproduces.

For each shared file it starts from java's copy and repeatedly
runs it through the morel-rust binary built from the current tree,
dropping every statement whose replayed output differs from
java's (a statement morel-rust cannot yet reproduce — an
unimplemented member, `Sys.plan`, and so on). Dropping a
statement can change a later one's output, so it iterates to a
fixed point.

Because it only ever DELETES whole statements from java's file,
the result is always an ordered subsequence of java: a `diff`
against java shows insertions only, never a line go has that java
lacks or a line in the wrong place. Both invariants — the result
round-trips through morel-rust, and it is a subsequence of java —
are asserted before anything is written. (The previous
insert-into-go design could silently misplace a pulled block;
this cannot.)

Report mode (the default) prints, per shared file, java's size,
the regenerated size, and the current go size, and lists java
files go does not have yet. Apply mode (--apply) writes the
regenerated files.

Because it builds morel-rust from the working tree and takes java
as a fixed reference, it can run against any morel-rust commit:
check the commit out and run it.

Usage:
    etc/pull-passing.py [--apply] [--java-repo PATH] [FILE...]

FILE args (relative to tests/script, e.g. simple.smli) limit
the run to those files; the default is every shared file.
"""
import argparse
import difflib
import os
import subprocess
import sys
import tempfile

GO_PREFIX = "tests/script/"
JAVA_PREFIX = "src/test/resources/script/"
DEFAULT_JAVA_REPO = os.path.expanduser("~/dev/morel.1")


def output_prefix(line):
    """Whether a line has the "> " expected-output prefix. Whether
    it actually IS output also depends on comment state — see
    segment — because inside a block comment such a line is
    content, as morel's RunScript treats it."""
    return line == ">" or line.startswith("> ")


def scan_depth(line, depth):
    """Updates block-comment nesting depth after one content line,
    matching morel's lexer: '(*' opens a (nesting) block comment,
    '*)' closes one, and '(*)' is a line comment (the rest of the
    line, inside a block comment too). At depth 0, string and char
    literals are skipped so a '(*' inside one does not open a
    comment."""
    i, n = 0, len(line)
    while i < n:
        if line[i:i + 3] == "(*)":
            return depth  # line comment: the rest of the line
        two = line[i:i + 2]
        if depth > 0:
            if two == "(*":
                depth += 1
                i += 2
            elif two == "*)":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if two == "(*":
            depth += 1
            i += 2
        elif line[i] == '"':
            i += 1
            while i < n and line[i] != '"':
                i += 2 if line[i] == "\\" else 1
            i += 1
        else:
            i += 1
    return depth


def line_has_code(line, depth):
    """Whether the line, entered at the given block-comment depth,
    has any code outside comments — used to tell a leading comment
    or blank line (trivia) from the statement it precedes."""
    i, n = 0, len(line)
    while i < n:
        if line[i:i + 3] == "(*)":
            return False  # line comment: no code seen before it here
        two = line[i:i + 2]
        if depth > 0:
            if two == "(*":
                depth += 1
                i += 2
            elif two == "*)":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if two == "(*":
            depth += 1
            i += 2
        elif not line[i].isspace():
            return True
        else:
            i += 1
    return False


def split_trivia(inp):
    """Splits a unit's input into (trivia, body): the leading blank
    and comment lines, and the statement itself. Dropping a
    statement keeps its trivia, so comments — including the file's
    header — survive even when the statement they precede does
    not."""
    depth = 0
    for k, line in enumerate(inp):
        if line_has_code(line, depth):
            return inp[:k], inp[k:]
        depth = scan_depth(line, depth)
    return list(inp), []


def segment(text):
    """Splits text into units, one per statement: (input_lines,
    output_lines). A unit's input is every line since the previous
    output block — leading blanks and comments, then the statement
    itself, however many lines, blank lines, or internal ';'s (in a
    'let', say) it spans — and its output is the '> ' block that
    follows. java emits output after every statement, so an output
    block reliably marks a statement's end. A '> '-prefixed line
    inside a '(* ... *)' comment is content, not output (depth
    tracking), matching morel's RunScript."""
    lines = text.split("\n")
    units = []
    inp = []
    depth = 0
    i, n = 0, len(lines)
    while i < n:
        if depth == 0 and output_prefix(lines[i]):
            out = []
            while i < n and output_prefix(lines[i]):
                out.append(lines[i])
                i += 1
            units.append((inp, out))
            inp = []
            continue
        inp.append(lines[i])
        depth = scan_depth(lines[i], depth)
        i += 1
    if inp:
        units.append((inp, []))
    return units


def go_outputs(replay, units):
    """morel-rust's output block for each java unit, found by walking
    the replay and, for each unit, consuming the unit's input lines
    (echoed verbatim, so identical) then taking the '> ' output
    that follows. This aligns java's units with the replay even
    where morel-rust emits no output for a statement — the case that
    defeats segmenting the replay on its own."""
    rl = replay.split("\n")
    ri = 0
    outs = []
    for inp, _ in units:
        for line in inp:
            if ri >= len(rl) or rl[ri] != line:
                raise RuntimeError("replay input mismatch")
            ri += 1
        out = []
        while ri < len(rl) and output_prefix(rl[ri]):
            out.append(rl[ri])
            ri += 1
        outs.append(out)
    return outs


def prune(java_text, run):
    """Returns java_text with every statement morel-rust cannot
    reproduce removed, iterated to a fixed point. Dropping a
    statement removes its whole unit — the statement, its output,
    and any leading blanks and comments — so blank-line structure
    stays intact."""
    text = java_text
    while True:
        replay = run(text)
        units = segment(text)
        gouts = go_outputs(replay, units)
        kept, changed = [], False
        for idx, ((inp, out), gout) in enumerate(zip(units, gouts)):
            if out == gout:
                kept.extend(inp)
                kept.extend(out)
                continue
            changed = True
            # Drop the statement and its output. A comment before a
            # dropped statement goes too — keeping it would leave a
            # dangling, possibly consecutive, line comment that the
            # smli lint rejects (the comment returns when the
            # statement it describes does). The one exception is the
            # file header: unit 0's leading trivia, which every file
            # must keep.
            if idx == 0:
                trivia, _ = split_trivia(inp)
                while trivia and not trivia[-1].strip():
                    trivia.pop()
                kept.extend(trivia)
        text = "\n".join(kept)
        if not changed:
            return text


def is_subsequence(result, java):
    """Whether result's lines are an ordered subsequence of java's
    (every result line matched in java, in order — no line added
    or moved)."""
    sm = difflib.SequenceMatcher(None, java.split("\n"),
                                 result.split("\n"), autojunk=False)
    return all(op in ("equal", "delete")
               for op, _, _, _, _ in sm.get_opcodes())


def statements(text):
    """The number of statements — units that produce output — in
    the text. Comment-only units do not count."""
    return sum(1 for _, out in segment(text) if out)


def build_morel():
    """Builds the morel-rust binary from the working tree into a
    temp path and returns it. Exits on build failure."""
    tmp = tempfile.mkdtemp(prefix="pull-passing-")
    binary = os.path.join(tmp, "morel")
    env = dict(os.environ,
               PATH=os.path.expanduser("~/.cargo/bin") + ":"
               + os.environ["PATH"])
    r = subprocess.run(
        ["cargo", "build", "-q"],
        capture_output=True, text=True, env=env)
    if r.returncode != 0:
        sys.exit("error: cargo build failed:\n" + r.stderr)
    del tmp, binary
    return os.path.join(os.getcwd(), "target", "debug", "morel")


def make_runner(binary):
    """Returns run(text, rel) -> replayed text: feed script text to
    the morel-rust binary and return its idempotent replay. go names
    the session 'stdIn' regardless of path, matching java's files.

    `rel` names the file the text came from, because one file is
    replayed from a different directory: `file.smli` browses the
    file system, so it starts in the data directory, where what it
    finds is predictable. `scripts_test.go` does the same, and a
    replay that does not agree with it prunes statements that in
    fact pass."""
    scratch = tempfile.mkdtemp(prefix="pull-passing-run-")
    path = os.path.join(scratch, "x.smli")

    def run(text, rel=""):
        with open(path, "w") as f:
            f.write(text)
        # `use` and `.input` resolve against the working directory, so
        # a replay runs where the script harness would put it.
        directory = "tests/data" if rel == "file.smli" else "tests/script"
        r = subprocess.run(
            [binary, "--directory=" + directory, "--idempotent", path],
            capture_output=True, text=True,
            env=dict(os.environ, MOREL_GAPS="1"))
        for line in r.stderr.splitlines():
            if line.startswith("gap: "):
                n, _, msg = line[len("gap: "):].partition(" x ")
                GAPS[msg] = GAPS.get(msg, 0) + int(n)
        return r.stdout

    return run


# Suppressed not-implemented tally, aggregated across every replay
# this run performs; reported at exit as a ranked worklist.
GAPS = {}


def report_gaps():
    if not GAPS:
        return
    print("\ngaps (not-implemented errors suppressed during "
          "replays, largest first):")
    for msg, n in sorted(GAPS.items(), key=lambda kv: -kv[1]):
        print(f"  {n:5} x {msg}")


def smli_files(root):
    """Relative `.smli` paths below root (a directory)."""
    files = set()
    for dirpath, _dirs, names in os.walk(root):
        for name in names:
            if name.endswith(".smli"):
                p = os.path.join(dirpath, name)
                files.add(os.path.relpath(p, root))
    return files


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("files", nargs="*", metavar="FILE",
                   help="limit to these files (rel. to "
                        "tests/script)")
    p.add_argument("--apply", action="store_true",
                   help="write the regenerated files (default: "
                        "report)")
    p.add_argument("--java-repo", default=DEFAULT_JAVA_REPO)
    p.add_argument("--min-pass", type=float, default=0.4,
                   metavar="FRACTION",
                   help="create a go-absent java file only if this "
                        "fraction of its statements pass (default "
                        "0.4); lower ones mostly fail and are "
                        "deferred")
    p.add_argument("--min-statements", type=int, default=5,
                   metavar="N",
                   help="also require this many passing statements "
                        "(default 5), so a file that is only its "
                        "Sys.set preamble is not brought over")
    args = p.parse_args()

    go_root = os.path.join(os.getcwd(), GO_PREFIX)
    java_root = os.path.join(args.java_repo, JAVA_PREFIX)
    if not os.path.isdir(java_root):
        sys.exit(f"error: no java scripts at {java_root}")

    go_files = smli_files(go_root)
    java_files = smli_files(java_root)
    if args.files:
        shared = sorted(set(args.files) & go_files & java_files)
        unknown = set(args.files) - (go_files & java_files)
        if unknown:
            sys.exit(f"error: not a shared file: {sorted(unknown)}")
    else:
        shared = sorted(go_files & java_files)
    missing = sorted(java_files - go_files)

    print("building morel-rust from the working tree...")
    run = make_runner(build_morel())

    grew = same = 0
    print(f"\n{'file':34} {'java':>6} {'go→':>6} {'new':>6} {'Δ':>5}")
    for rel in shared:
        with open(os.path.join(java_root, rel)) as f:
            java_text = f.read()
        with open(os.path.join(go_root, rel)) as f:
            go_text = f.read()
        # The runner needs to know which file this is; see
        # make_runner.
        def frun(text, rel=rel):
            return run(text, rel)

        try:
            new_text = prune(java_text, frun)
        except RuntimeError:
            # morel-rust crashes partway through java's copy (a
            # feature it does not have yet), so the replay does not
            # line up. Leave the go file as it is; the crash is a
            # signal for a future task.
            print(f"  {rel:34} {'—':>6}  skip (morel-rust crashes)")
            continue
        # Invariants: the result round-trips, and is a subsequence
        # of java. Never write a file that violates either.
        if frun(new_text) != new_text:
            sys.exit(f"error: {rel}: regenerated file does not "
                     f"round-trip")
        if not is_subsequence(new_text, java_text):
            sys.exit(f"error: {rel}: regenerated file is not a "
                     f"subsequence of java")
        jn = len(java_text.splitlines())
        gn = len(go_text.splitlines())
        nn = len(new_text.splitlines())
        if new_text == go_text:
            same += 1
            continue
        grew += 1
        print(f"{rel:34} {jn:6} {gn:6} {nn:6} {nn - gn:+5}")
        if args.apply:
            with open(os.path.join(go_root, rel), "w") as f:
                f.write(new_text)

    verb = "changed" if args.apply else "would change"
    print(f"\n{grew} files {verb}, {same} already current")
    if not args.apply and grew:
        print("re-run with --apply to write these changes")
    if missing and not args.files:
        print(f"\njava files go does not have — pruned pass rate "
              f"(statements go reproduces); creating "
              f">= {args.min_pass:.0%}:")
        created = deferred = 0
        for rel in missing:
            with open(os.path.join(java_root, rel)) as f:
                java_text = f.read()
            def frun(text, rel=rel):
                return run(text, rel)

            try:
                new_text = prune(java_text, frun)
                ok = (frun(new_text) == new_text
                      and is_subsequence(new_text, java_text))
            except RuntimeError:
                # morel-rust crashes partway (e.g. a stack overflow on
                # unbounded recursion), so its replay does not line
                # up with the input. Such a file mostly fails.
                ok = False
            if not ok:
                print(f"  {rel:32} {'—':>9}  defer (morel-rust "
                      f"cannot run it)")
                deferred += 1
                continue
            total = statements(java_text)
            kept = statements(new_text)
            rate = kept / total if total else 0.0
            take = rate >= args.min_pass and kept >= args.min_statements
            print(f"  {rel:32} {kept:4}/{total:<4} {rate:4.0%}  "
                  f"{'create' if take else 'defer'}")
            if take:
                created += 1
                if args.apply:
                    path = os.path.join(go_root, rel)
                    os.makedirs(os.path.dirname(path), exist_ok=True)
                    with open(path, "w") as f:
                        f.write(new_text)
            else:
                deferred += 1
        verb = "created" if args.apply else "to create"
        print(f"\n  {created} {verb}, {deferred} deferred "
              f"(mostly failing)")
    report_gaps()
    return 0


if __name__ == "__main__":
    sys.exit(main())
