#!/usr/bin/env python3
"""
analyze_disabled.py - Maps disabled .smli test regions in morel-rust.1 to
morel-java (morel.3) commits, producing tables for a migration plan.

A region is "disabled" if it is:
  1. Inside a block comment (* ... *), OR
  2. Preceded by set("mode","validate") with no intervening set("mode","evaluate")

Note: (*) is treated as an empty one-line comment (does not open a block comment).

Usage:
  python3 scripts/analyze_disabled.py
  python3 scripts/analyze_disabled.py --file relational.smli
"""
from __future__ import annotations

import argparse
import datetime
import re
import subprocess
import sys
from pathlib import Path

RUST_SCRIPT_DIR = Path("/Users/jhyde/dev/morel-rust.1/tests/script")
JAVA_SCRIPT_DIR = Path("/Users/jhyde/dev/morel.3/src/test/resources/script")
JAVA_REPO = "/Users/jhyde/dev/morel.3"


# ---------------------------------------------------------------------------
# Parsing morel-rust.1 .smli files
# ---------------------------------------------------------------------------

def classify_lines(filepath: Path) -> list[tuple[int, str, str]]:
    """
    Returns [(line_no, raw_line, state), ...] where state is one of:
      'enabled'   – normal evaluate mode
      'validate'  – in validate mode (type-checked but not run)
      'commented' – inside a (* ... *) block comment
    Line numbers are 1-based.

    Rules:
    - Default mode is 'evaluate'.
    - set("mode","validate") / set("mode","evaluate") switches modes.
      The set() line itself is classified 'enabled'.
    - (* immediately followed by ) on the same token is an empty comment
      and does NOT change state.
    - (* followed by anything else opens a block comment until matching *).
    - Block comments can be nested.
    - Mode-switch lines inside block comments are ignored.
    """
    text = filepath.read_text(encoding='utf-8')
    raw_lines = text.splitlines(keepends=True)

    mode = 'evaluate'
    comment_depth = 0
    results = []

    for line_idx, raw_line in enumerate(raw_lines):
        line_no = line_idx + 1
        line = raw_line.rstrip('\n')

        # Determine the state at the START of this line
        if comment_depth > 0:
            line_start_state = 'commented'
        elif mode == 'validate':
            line_start_state = 'validate'
        else:
            line_start_state = 'enabled'

        # Scan the line to update comment depth and detect mode switches.
        # We only act on mode switches when comment_depth == 0.
        i = 0
        chars = line
        found_mode_switch = None

        while i < len(chars):
            if comment_depth == 0:
                # Check for (*) — empty comment, skip 3 chars, no depth change
                if chars[i:i+3] == '(*)':
                    i += 3
                    continue
                # Check for (* opening a block comment
                if chars[i:i+2] == '(*':
                    comment_depth += 1
                    i += 2
                    continue
                # Check for string literal — skip contents so (* inside strings
                # don't confuse us
                if chars[i] == '"':
                    i += 1
                    while i < len(chars) and chars[i] != '"':
                        if chars[i] == '\\':
                            i += 1
                        i += 1
                    i += 1
                    continue
                # Check for mode-switch calls
                rest = chars[i:]
                for pat, new_mode in [
                    ('set("mode", "validate")', 'validate'),
                    ('set("mode","validate")', 'validate'),
                    ('set("mode", "evaluate")', 'evaluate'),
                    ('set("mode","evaluate")', 'evaluate'),
                ]:
                    if rest.startswith(pat):
                        found_mode_switch = new_mode
                        i += len(pat)
                        break
                else:
                    i += 1
                    continue
            else:
                # Inside a block comment: look for nested (* or *)
                # Check for (*) first — it is an empty comment, not a nested opener
                if chars[i:i+3] == '(*)':
                    i += 3
                    continue
                if chars[i:i+2] == '(*':
                    comment_depth += 1
                    i += 2
                    continue
                if chars[i:i+2] == '*)':
                    comment_depth -= 1
                    i += 2
                    continue
                i += 1

        # Apply the mode switch (takes effect for NEXT line)
        if found_mode_switch is not None:
            # The set() line is always 'enabled' regardless of current mode
            line_start_state = 'enabled'
            mode = found_mode_switch

        results.append((line_no, line, line_start_state))

    return results


_LICENSE_WORDS = ('Licensed to Julian Hyde', 'Apache License', 'http://www.apache.org')


def _is_license_header(lines: list[tuple[int, str]]) -> bool:
    """True if the region looks like an Apache licence header block."""
    text = ' '.join(ln for _, ln in lines[:10])
    return any(w in text for w in _LICENSE_WORDS)


def extract_disabled_regions(
    classified: list[tuple[int, str, str]]
) -> list[dict]:
    """
    Group consecutive disabled lines into regions.
    Returns list of dicts with keys: start, end, state, lines.

    All non-enabled states (validate OR commented) are merged into a single
    disabled region — this avoids artificially splitting regions that alternate
    between a validate block and inline block-comments within it.

    Filtering applied:
      - Apache licence header blocks are dropped.
      - Regions with no substantive content are dropped.
    """
    regions = []
    cur_start = None
    cur_state = None   # dominant state of the region (first non-enabled state seen)
    cur_lines: list[tuple[int, str]] = []

    def flush():
        if cur_start is None or not cur_lines:
            return
        if _is_license_header(cur_lines):
            return
        if any(_is_substantive(ln) for _, ln in cur_lines):
            regions.append({
                'start': cur_start,
                'end': cur_lines[-1][0],
                'state': cur_state,
                'lines': cur_lines,
            })

    for line_no, line, state in classified:
        if state == 'enabled':
            flush()
            cur_start = None
            cur_state = None
            cur_lines = []
        else:
            if cur_state is None:
                cur_start = line_no
                cur_state = state
                cur_lines = [(line_no, line)]
            else:
                # Keep growing the region regardless of validate vs commented
                cur_lines.append((line_no, line))

    flush()
    return regions


def _is_substantive(line: str) -> bool:
    """True if the line contains real code (not blank, output, or doc comment)."""
    s = line.strip()
    return bool(s) and not s.startswith('>') and not s.startswith('(*)')


def _first_statement(region: dict) -> str | None:
    """Return the first real statement line of a region (for use as description)."""
    for _, line in region['lines']:
        s = line.strip()
        if (s and not s.startswith('>')
                and not s.startswith('(*)')
                and not s.startswith('(*')
                and 'set("mode"' not in s):
            return s
    return None


# ---------------------------------------------------------------------------
# git blame on morel-java files
# ---------------------------------------------------------------------------

def _git_blame(java_rel_path: str) -> dict[int, dict]:
    """
    Run `git blame --line-porcelain` on a file relative to JAVA_REPO.
    Returns {line_no: {sha, date, summary, content}}.
    """
    try:
        proc = subprocess.run(
            ['git', '-C', JAVA_REPO, 'blame', '--line-porcelain', java_rel_path],
            capture_output=True, text=True, check=True,
        )
    except subprocess.CalledProcessError as e:
        print(f"  [warn] git blame failed for {java_rel_path}: {e}", file=sys.stderr)
        return {}

    blame: dict[int, dict] = {}
    commit_meta: dict[str, dict] = {}
    cur_sha = None
    cur_final_line = None

    for raw in proc.stdout.splitlines():
        m = re.match(r'^([0-9a-f]{40}) \d+ (\d+)', raw)
        if m:
            cur_sha = m.group(1)
            cur_final_line = int(m.group(2))
            if cur_sha not in commit_meta:
                commit_meta[cur_sha] = {}
            continue
        if raw.startswith('summary ') and cur_sha is not None:
            commit_meta[cur_sha]['summary'] = raw[8:]
            continue
        if raw.startswith('author-time ') and cur_sha is not None:
            ts = int(raw[12:])
            dt = datetime.datetime.fromtimestamp(ts, tz=datetime.timezone.utc)
            commit_meta[cur_sha]['date'] = dt.strftime('%Y-%m-%d')
            continue
        if raw.startswith('\t') and cur_sha is not None and cur_final_line is not None:
            meta = commit_meta.get(cur_sha, {})
            blame[cur_final_line] = {
                'sha': cur_sha[:8],
                'full_sha': cur_sha,
                'date': meta.get('date', ''),
                'summary': meta.get('summary', ''),
                'content': raw[1:],
            }
            cur_final_line = None

    return blame


# ---------------------------------------------------------------------------
# Matching rust lines to java lines
# ---------------------------------------------------------------------------

def _build_java_index(
    java_lines: list[str],
    java_states: list[tuple[int, str, str]],
) -> dict[str, list[int]]:
    """
    Build an index from stripped line content → list of 1-based line numbers,
    but ONLY for lines that are in 'enabled' state in the morel-java file.
    This lets us detect when content is disabled in both repos (not a gap).
    """
    enabled_nos = {line_no for line_no, _, state in java_states if state == 'enabled'}
    idx: dict[str, list[int]] = {}
    for i, line in enumerate(java_lines):
        line_no = i + 1
        if line_no not in enabled_nos:
            continue
        s = line.strip()
        if s:
            idx.setdefault(s, []).append(line_no)
    return idx


def find_commit_for_region(
    region: dict,
    java_index: dict[str, list[int]],
    blame: dict[int, dict],
) -> dict | None:
    """
    Try to find the morel-java commit that introduced the content in region.
    Tries the first few substantive lines; returns the commit info dict or None.
    Returns None if no matching ENABLED line is found in morel-java (meaning the
    content is equally disabled in both repos and is not a gap to fix).
    """
    candidates = [
        line.strip()
        for _, line in region['lines']
        if _is_substantive(line)
    ][:8]

    for candidate in candidates:
        for java_line_no in java_index.get(candidate, []):
            info = blame.get(java_line_no)
            if info:
                return info
    return None


# ---------------------------------------------------------------------------
# Main analysis
# ---------------------------------------------------------------------------

def analyze(files: list[str] | None = None) -> None:
    if files:
        rust_files = [RUST_SCRIPT_DIR / f for f in files]
    else:
        rust_files = sorted(RUST_SCRIPT_DIR.glob('*.smli'))

    # Skip dummy.smli
    rust_files = [f for f in rust_files if f.name != 'dummy.smli']

    # Also report files that are entirely missing from morel-rust.1
    # (exclude dummy.smli which exists in both but is intentionally skipped above)
    _skip = {'dummy.smli'}
    java_names = {f.name for f in JAVA_SCRIPT_DIR.glob('*.smli')} - _skip
    rust_names = {f.name for f in rust_files}
    missing = sorted(java_names - rust_names)

    all_records: list[dict] = []          # per-region records
    commit_order: list[str] = []          # full SHAs in first-seen order
    commit_map: dict[str, dict] = {}      # full_sha → commit info

    for rust_file in rust_files:
        java_file = JAVA_SCRIPT_DIR / rust_file.name

        classified = classify_lines(rust_file)
        regions = extract_disabled_regions(classified)

        if not regions:
            continue  # File has no disabled content

        # Load java counterpart (if it exists)
        blame: dict[int, dict] = {}
        java_index: dict[str, list[int]] = {}
        if java_file.exists():
            java_lines = java_file.read_text(encoding='utf-8').splitlines()
            java_states = classify_lines(java_file)
            print(f"  blaming {rust_file.name} ...", file=sys.stderr)
            blame = _git_blame(f'src/test/resources/script/{rust_file.name}')
            java_index = _build_java_index(java_lines, java_states)

        for region in regions:
            commit = find_commit_for_region(region, java_index, blame)
            # Skip regions that have no matching ENABLED content in morel-java
            # (they're equally disabled in both repos — not a gap to fix).
            if commit is None:
                continue
            desc = _first_statement(region) or ''

            # Register commit
            sha = commit['full_sha']
            if sha not in commit_map:
                commit_map[sha] = commit
                commit_order.append(sha)

            all_records.append({
                'file': rust_file.name,
                'start': region['start'],
                'end': region['end'],
                'state': region['state'],
                'desc': desc[:70],
                'commit': commit,
            })

    # -----------------------------------------------------------------------
    # Output
    # -----------------------------------------------------------------------

    # Sort commits chronologically
    commit_order_sorted = sorted(
        commit_order,
        key=lambda sha: commit_map[sha].get('date', ''),
    )
    commit_ordinal: dict[str, str] = {
        sha: f'C{i+1:02d}' for i, sha in enumerate(commit_order_sorted)
    }

    print("\n## Table A: morel-java Commits Referenced by Disabled Regions\n")
    print(f"| {'#':<4} | {'SHA':<10} | {'Date':<12} | Message |")
    print(f"|{'-'*5}|{'-'*11}|{'-'*13}|{'-'*60}|")
    for sha in commit_order_sorted:
        c = commit_map[sha]
        ordinal = commit_ordinal[sha]
        print(f"| {ordinal:<4} | {c['sha']:<10} | {c['date']:<12} | {c['summary']} |")

    print()
    print("## Table B: Disabled Sections in morel-rust.1\n")
    print(f"| {'File':<22} | {'Lines':<10} | {'State':<9} | {'Description':<55} | {'Commit':<6} |")
    print(f"|{'-'*23}|{'-'*11}|{'-'*10}|{'-'*56}|{'-'*7}|")
    for r in all_records:
        commit_ref = '?'
        if r['commit']:
            commit_ref = commit_ordinal.get(r['commit']['full_sha'], '?')
        print(
            f"| {r['file']:<22} | "
            f"{r['start']}-{r['end']:<6} | "
            f"{r['state']:<9} | "
            f"{r['desc']:<55} | "
            f"{commit_ref:<6} |"
        )

    if missing:
        print()
        print("## Files Missing from morel-rust.1 (present only in morel-java)\n")
        for name in missing:
            # Find the commit that created the file
            try:
                proc = subprocess.run(
                    ['git', '-C', JAVA_REPO, 'log', '--diff-filter=A',
                     '--format=%h %as %s',
                     f'src/test/resources/script/{name}'],
                    capture_output=True, text=True, check=True,
                )
                creation = proc.stdout.strip().split('\n')[0] if proc.stdout.strip() else 'unknown'
            except subprocess.CalledProcessError:
                creation = 'unknown'
            line = f"- **{name}**: `{creation}`"
            # Fold bullet lines that exceed 80 chars at a word boundary.
            if len(line) > 80:
                # Find a space to break at, before column 80
                break_at = line.rfind(' ', 0, 80)
                if break_at > 0:
                    line = line[:break_at] + '\n  ' + line[break_at + 1:]
            print(line)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        '--file', metavar='NAME', action='append',
        help='Analyse only this .smli file (can repeat). Default: all files.',
    )
    args = parser.parse_args()
    analyze(args.file)
