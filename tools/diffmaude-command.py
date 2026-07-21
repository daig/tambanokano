#!/usr/bin/env python3
"""Run diffmaude on one source-order substantive command from a mixed fixture."""

from __future__ import annotations

import argparse
import re
import subprocess
import tempfile
from pathlib import Path

COMMAND_START = re.compile(
    r"^\s*(?:(?:\{[^}\n]+\}\s+)?f?vu-narrow|reduce|red|rewrite|rew|frewrite|frew|"
    r"erewrite|erew|search|match|xmatch|unify|(?:irred|irredundant)\s+unify|"
    r"get\s+(?:irredundant\s+)?variants|filtered\s+variant\s+unify|variant\s+(?:unify|match))\b"
)


def command_ends(line: str) -> bool:
    """Whether a source line ends a command, ignoring strings and line comments."""
    quoted = False
    escaped = False
    visible: list[str] = []
    i = 0
    while i < len(line):
        ch = line[i]
        if quoted:
            visible.append(ch)
            if escaped:
                escaped = False
            elif ch == "\\":
                escaped = True
            elif ch == '"':
                quoted = False
            i += 1
            continue
        if ch == '"':
            quoted = True
            visible.append(ch)
            i += 1
            continue
        if line.startswith("***", i) or line.startswith("---", i):
            break
        visible.append(ch)
        i += 1
    return "".join(visible).rstrip().endswith(".")


def command_spans(lines: list[str]) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    start: int | None = None
    for i, line in enumerate(lines):
        if start is None:
            if COMMAND_START.match(line):
                start = i
                if command_ends(line):
                    spans.append((start, i))
                    start = None
        elif command_ends(line):
            spans.append((start, i))
            start = None
    if start is not None:
        raise ValueError(f"unterminated command starting at line {start + 1}")
    return spans


def isolate(path: Path, ordinal: int) -> tuple[str, tuple[int, int], int]:
    lines = path.read_text().splitlines(keepends=True)
    spans = command_spans(lines)
    if ordinal < 1 or ordinal > len(spans):
        raise ValueError(f"command ordinal must be 1..{len(spans)}, got {ordinal}")
    selected = spans[ordinal - 1]
    remove = {line for start, end in spans[: ordinal - 1] for line in range(start, end + 1)}
    isolated = ["\n" if i in remove else line for i, line in enumerate(lines[: selected[1] + 1])]
    return "".join(isolated), selected, len(spans)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Isolate one substantive Maude command and compare it with the pinned oracle."
    )
    parser.add_argument("fixture", type=Path)
    parser.add_argument("ordinal", type=int, help="1-based substantive command ordinal")
    parser.add_argument("--emit", type=Path, help="write the isolated fixture instead of running it")
    parser.add_argument("-v", "--verbose", action="store_true")
    args = parser.parse_args()

    fixture = args.fixture.resolve()
    source, (start, end), count = isolate(fixture, args.ordinal)
    print(
        f"{fixture.name}: command {args.ordinal}/{count}, source lines {start + 1}-{end + 1}",
        flush=True,
    )
    if args.emit:
        args.emit.write_text(source)
        return 0

    root = Path(__file__).resolve().parent.parent
    with tempfile.TemporaryDirectory(prefix=".diffmaude-command.", dir=fixture.parent) as temp:
        isolated = Path(temp) / fixture.name
        isolated.write_text(source)
        command = [str(root / "tools" / "diffmaude.sh"), str(isolated)]
        if args.verbose:
            command.append("-v")
        return subprocess.run(command, cwd=root, check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())
