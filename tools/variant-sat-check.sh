#!/usr/bin/env bash
# Verify the native variant-satisfiability facade against its pinned value-and-sort contract.
# Reflective presentation details are intentionally outside this check.
set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
fixture=${1:-$ROOT/conformance/subsystems/T11-variant-satisfiability.maude}
expected=${2:-$ROOT/conformance/subsystems/T11-variant-satisfiability.expected}
TNK_BIN=${TNK_BIN:-$ROOT/target/release/tnk-repl}
TNK_SHARE_LIB=${TNK_SHARE_LIB:-$ROOT/share/maude-gpl:$ROOT/share/tnk}
ORACLE_LIB=${ORACLE_LIB:-${MAUDE_LIB:-}}
TIMEOUT_SECS=${TIMEOUT_SECS:-60}

[ -f "$fixture" ] || { echo "error: fixture not found: $fixture" >&2; exit 2; }
[ -f "$expected" ] || { echo "error: expected contract not found: $expected" >&2; exit 2; }
[ -x "$TNK_BIN" ] || { echo "error: tnk binary not found: $TNK_BIN" >&2; exit 2; }
[ -n "$ORACLE_LIB" ] || { echo "error: set ORACLE_LIB or MAUDE_LIB to the Maude library path" >&2; exit 2; }

tmp=$(mktemp -d "${TMPDIR:-/tmp}/tnk-var-sat.XXXXXX") || exit 2
trap 'rm -rf "$tmp"' EXIT

fixdir=$(cd "$(dirname "$fixture")" && pwd)
(
  cd "$fixdir" || exit 2
  MAUDE_LIB="$TNK_SHARE_LIB:$ORACLE_LIB" timeout "$TIMEOUT_SECS" \
    "$TNK_BIN" -no-banner "$fixture" </dev/null
) >"$tmp/output" 2>&1
rc=$?
if [ $rc -eq 124 ]; then
  echo "tnk variant-satisfiability contract timed out" >&2
  exit 4
elif [ $rc -ne 0 ]; then
  cat "$tmp/output" >&2
  exit 2
fi

awk '/^result Bool: (true|false)$/ { print $3 }' "$tmp/output" >"$tmp/actual"
awk '!/^#/ && NF { print $1 }' "$expected" >"$tmp/expected"

expected_count=$(wc -l <"$tmp/expected" | tr -d ' ')
actual_count=$(wc -l <"$tmp/actual" | tr -d ' ')
if [ "$actual_count" -ne "$expected_count" ]; then
  echo "variant-satisfiability result-count mismatch: expected $expected_count, got $actual_count" >&2
  cat "$tmp/output" >&2
  exit 1
fi

diff -u "$tmp/expected" "$tmp/actual" || exit 1
echo "VAR-SAT NATIVE $actual_count/$expected_count PASS"
