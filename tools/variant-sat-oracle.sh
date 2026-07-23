#!/usr/bin/env bash
# Re-run the T6 semantic contract through the untouched official Maude-2.7 prototype.
# The archive is external reference material: this script verifies it, extracts it only to a
# temporary directory, and never copies prototype source into the repository.
set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
ARCHIVE=${1:-${VAR_SAT_ARCHIVE:-}}
fixture=${2:-$ROOT/conformance/subsystems/T11-variant-satisfiability.maude}
expected=${3:-$ROOT/conformance/subsystems/T11-variant-satisfiability.expected}
TIMEOUT_SECS=${TIMEOUT_SECS:-60}
PINNED_SHA256=03f8f91362d90295ca9ae8497dd7dc7af3bc1d704ee7dce1679aa566983fce47

[ -n "$ARCHIVE" ] || {
  echo "usage: $0 <var-sat-rel3.tgz> [fixture.maude] [expected]" >&2
  exit 2
}
[ -f "$ARCHIVE" ] || { echo "error: archive not found: $ARCHIVE" >&2; exit 2; }
[ -f "$fixture" ] || { echo "error: fixture not found: $fixture" >&2; exit 2; }
[ -f "$expected" ] || { echo "error: expected contract not found: $expected" >&2; exit 2; }

if command -v sha256sum >/dev/null 2>&1; then
  actual_sha=$(sha256sum "$ARCHIVE" | awk '{print $1}')
else
  actual_sha=$(shasum -a 256 "$ARCHIVE" | awk '{print $1}')
fi
[ "$actual_sha" = "$PINNED_SHA256" ] || {
  echo "error: archive checksum mismatch: $actual_sha" >&2
  exit 2
}

tmp=$(mktemp -d "${TMPDIR:-/tmp}/tnk-var-sat-oracle.XXXXXX") || exit 2
trap 'rm -rf "$tmp"' EXIT
tar -xzf "$ARCHIVE" -C "$tmp" || exit 2
package=$tmp/var-sat-rel
[ -x "$package/maude" ] || { echo "error: bundled oracle binary missing" >&2; exit 2; }

# The package's nested relative loads require its examples directory. Replace only the facade load;
# the remaining source is exactly the repository contract fixture.
driver=$package/examples/tnk-T11-contract.maude
awk 'NR == 2 { print "load examples.maude"; next } { print }' "$fixture" >"$driver"
(
  cd "$package/examples" || exit 2
  MAUDE_LIB="$package" timeout "$TIMEOUT_SECS" \
    "$package/maude" -no-banner "$(basename "$driver")" </dev/null
) >"$tmp/output" 2>&1
rc=$?
if [ $rc -eq 124 ]; then
  echo "Maude-2.7 variant-satisfiability oracle timed out" >&2
  exit 3
elif [ $rc -ne 0 ]; then
  cat "$tmp/output" >&2
  exit 2
fi

awk '/^result Bool: (true|false)$/ { print $3 }' "$tmp/output" >"$tmp/actual"
awk '!/^#/ && NF { print $2 }' "$expected" >"$tmp/expected"
expected_count=$(wc -l <"$tmp/expected" | tr -d ' ')
actual_count=$(wc -l <"$tmp/actual" | tr -d ' ')
if [ "$actual_count" -ne "$expected_count" ]; then
  echo "oracle result-count mismatch: expected $expected_count, got $actual_count" >&2
  cat "$tmp/output" >&2
  exit 1
fi

diff -u "$tmp/expected" "$tmp/actual" || exit 1
if [ "${VAR_SAT_ORACLE_VERBOSE:-0}" = "1" ]; then
  cat "$tmp/output"
fi
echo "VAR-SAT ORACLE $actual_count/$expected_count PASS"
