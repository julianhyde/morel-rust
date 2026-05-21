#!/usr/bin/env python3
"""Build two concatenated benchmark .smli files for issue #34.

* tests/script/bench-built-in-rust.smli — rust's built-in scripts.
  License headers and validate/evaluate sections stripped, datalog
  skipped (path-sensitive / rust-only), `Sys.clearEnv ()` injected
  between files, and `Sys.plan ()` / `Sys.planEx ...;` calls dropped
  (their output contains compiler-internal fresh-variable counters
  that are not stable across duplications).
* tests/script/bench-built-in-java.smli — same idea, from java's
  src/test/resources/script/built-in/*.smli.

If `DUPLICATIONS > 1`, the per-file body is repeated that many times.
"""
import os
import re

RUST_IN  = "/Users/jhyde/dev/morel-rust.3/tests/script/built-in"
JAVA_IN  = "/Users/jhyde/dev/morel.0/src/test/resources/script/built-in"
RUST_OUT = "/Users/jhyde/dev/morel-rust.3/tests/script/bench-built-in-rust.smli"
JAVA_OUT = "/Users/jhyde/dev/morel-rust.3/tests/script/bench-built-in-java.smli"

DUPLICATIONS = 6

SKIP_FILES = {"datalog.smli"}


def strip_license(text):
    lines = text.splitlines(keepends=True)
    if not lines or not lines[0].startswith("(*"):
        return text
    depth = 0
    end_idx = 0
    for i, ln in enumerate(lines):
        depth += ln.count("(*") - ln.count("*)")
        if depth == 0:
            end_idx = i + 1
            break
    return "".join(lines[end_idx:])


_PAT_START = re.compile(r'^\s*(?:Sys\.)?set\s*\(\s*"mode"\s*,\s*"validate"')
_PAT_END   = re.compile(r'^\s*(?:Sys\.)?set\s*\(\s*"mode"\s*,\s*"evaluate"')
_PAT_UNIT  = re.compile(r'^>\s*val it = \(\) : unit\s*$')


def strip_validate_sections(text):
    out = []
    inside = False
    drop_next_unit = False
    for ln in text.splitlines(keepends=True):
        if drop_next_unit:
            drop_next_unit = False
            if _PAT_UNIT.match(ln):
                continue
        if not inside and _PAT_START.match(ln):
            inside = True
            continue
        if inside:
            if _PAT_END.match(ln):
                inside = False
                drop_next_unit = True
                continue
            continue
        out.append(ln)
    return "".join(out)


_PAT_PLAN = re.compile(r'^\s*Sys\.(?:plan|planEx)\b')


def strip_plan_calls(text):
    """Drop `Sys.plan ()` / `Sys.planEx ...;` statements and any
    immediately-following `> ...` expected-output lines, because their
    output embeds compiler-internal counters that drift across
    duplicated copies of the same script.
    """
    out = []
    drop_output = False
    for ln in text.splitlines(keepends=True):
        if drop_output:
            if ln.startswith(">"):
                continue
            drop_output = False
        if _PAT_PLAN.match(ln):
            drop_output = True
            continue
        out.append(ln)
    return "".join(out)


def build(in_dir, out_path, strip_validate):
    files = sorted(f for f in os.listdir(in_dir)
                   if f.endswith(".smli") and f not in SKIP_FILES)
    per_file = []
    for f in files:
        with open(os.path.join(in_dir, f)) as fh:
            text = fh.read()
        text = strip_license(text)
        if strip_validate:
            text = strip_validate_sections(text)
        text = strip_plan_calls(text)
        text = text.lstrip("\n").rstrip() + "\n"
        per_file.append((f, text))
    chunks = []
    for rep in range(DUPLICATIONS):
        for f, text in per_file:
            tag = f"{f} (copy {rep + 1}/{DUPLICATIONS})" if DUPLICATIONS > 1 else f
            chunks.append(
                f"(*) Begin {tag} *)\n"
                f"Sys.clearEnv ();\n> val it = () : unit\n"
                f"{text}"
                f"(*) End {tag} *)\n\n"
            )
    body = "".join(chunks)
    with open(out_path, "w") as fh:
        fh.write(body)
    print(f"  {out_path}: {len(body):>9d} bytes, {body.count(chr(10)):>6d} lines, "
          f"{len(files)} files × {DUPLICATIONS}")


def main():
    print("Building benchmarks…")
    build(RUST_IN, RUST_OUT, strip_validate=True)
    build(JAVA_IN, JAVA_OUT, strip_validate=False)


if __name__ == "__main__":
    main()
