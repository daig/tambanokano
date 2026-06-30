#!/usr/bin/env python3
"""Wrap-robust differential extractor for strategy (`srewrite`/`dsrewrite`) output.

Maude (and our REPL, which mirrors it byte-for-byte) line-wraps stdout at a fixed
width: long command echoes AND long result values break across indented
continuation lines. A naive line-by-line parser (`awk '/^result/{...}'`) silently
mis-reads such output — the bug that kept tripping up ad-hoc differential checks.

This extractor is wrap-insensitive: it ignores command echoes entirely and joins
each `result <Type>: <value>` across its continuation lines (everything up to the
next `Solution` / `rewrites:` / blank / `No more` / `No solution` marker). It emits
one normalized `value[count]` token per solution (whitespace-collapsed), so the
solution *sequence* (value + per-solution cumulative rewrite count) can be diffed
across the whole input regardless of where the wrapper happened to break lines.

Usage:
    maude   ... file.maude | strat_diff.py     > ref.txt
    tnk-repl    file.maude | strat_diff.py     > mine.txt
    diff ref.txt mine.txt
Or compare two files directly:
    strat_diff.py ref_output.txt mine_output.txt   # exits 1 on any difference
"""
import re
import sys

_MARKER = re.compile(r"^(Solution\b|rewrites:|No more solutions|No solution|=====|[a-z]*rewrite in\b|\s*$)")


def extract(text):
    """Return the list of `value[count]` solution tokens from one tool's output."""
    out = []
    lines = text.splitlines()
    i = 0
    count = None
    while i < len(lines):
        line = lines[i]
        m = re.match(r"\s*rewrites:\s+(\d+)", line)
        if m:
            count = m.group(1)
            i += 1
            continue
        if line.startswith("No solution"):
            out.append("(no solution)")
            i += 1
            continue
        m = re.match(r"result [^:]*:\s*(.*)", line)
        if m:
            parts = [m.group(1)]
            j = i + 1
            while j < len(lines) and not _MARKER.match(lines[j]):
                parts.append(lines[j].strip())
                j += 1
            value = re.sub(r"\s+", " ", " ".join(p for p in parts if p).strip())
            out.append(f"{value}[{count}]")
            i = j
            continue
        i += 1
    return out


def main():
    if len(sys.argv) == 3:
        a = extract(open(sys.argv[1]).read())
        b = extract(open(sys.argv[2]).read())
        if a == b:
            print(f"IDENTICAL: {len(a)} solution lines")
            return 0
        print(f"DIFFER: ref={len(a)} mine={len(b)}")
        for k in range(max(len(a), len(b))):
            x = a[k] if k < len(a) else "<missing>"
            y = b[k] if k < len(b) else "<missing>"
            if x != y:
                print(f"  [{k}] ref:  {x}\n      mine: {y}")
        return 1
    # filter mode: stdin → one token per line
    for tok in extract(sys.stdin.read()):
        print(tok)
    return 0


if __name__ == "__main__":
    sys.exit(main())
