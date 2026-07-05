#!/usr/bin/env bash
# tools/diffmaude.sh — oracle-diff harness (docs/migration/correctness-goal.md §1.1).
#
# Usage: tools/diffmaude.sh <fixture.maude> [-v]
#   -v            print the normalized diff even when identical (verbose PASS)
#
# Exit codes:
#   0  normalized outputs identical (PASS)
#   1  outputs differ (unified diff on stdout)
#   3  oracle timed out (60s)
#   4  tnk timed out (60s)
#   2  usage / setup error
#
# Oracle:  MAUDE_LIB=$ORACLE_LIB maude -no-banner -no-advise <fixture> </dev/null
# tnk:     target/release/tnk-repl
#   Post-C6c (TNK_STANDING_PRELUDE=1, the default since the C6c fix landed):
#   tnk is invoked directly with MAUDE_LIB=$ORACLE_LIB -no-banner; fixtures
#   WITHOUT the `*** PRELUDE` marker get -no-prelude (self-contained), marker'd
#   fixtures run on the standing prelude — symmetrical with the oracle.
#   Pre-C6c (TNK_STANDING_PRELUDE=0, kept for archaeology): a marker'd fixture
#   gets $ORACLE_LIB/prelude.maude concatenated in front on the tnk side.
#
# Normalization (exact; §1.1 — NOTHING else may be stripped):
#   - `====…` separator lines
#   - the tnk banner line, `Bye.`, `Maude>` prompts
#   - the timing tail of `rewrites: N in …` / `states: N  rewrites: M in …`
#     lines (the counts stay)
#   - `Warning:` / `Advisory:` blocks (first line + continuations up to the
#     next recognizable output line) — oracle diagnostics; phase E, not this goal
#   - `error:` / `parse error:` / `error in module` blocks — tnk diagnostics,
#     symmetric rationale (includes the pre-C6c LEXICAL/LOOP-MODE build errors)
#   Everything else — echoes, result/Solution lines, sorts, counts, bindings,
#   traces — compares byte-exact.

set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
ORACLE_LIB=${ORACLE_LIB:-$HOME/code/maude-lang/maude/src/Main}
ORACLE_BIN=${ORACLE_BIN:-maude}
TNK_BIN=${TNK_BIN:-$ROOT/target/release/tnk-repl}
TNK_STANDING_PRELUDE=${TNK_STANDING_PRELUDE:-1}
TIMEOUT_SECS=${TIMEOUT_SECS:-60}

fixture=${1:-}
verbose=${2:-}
if [ -z "$fixture" ] || [ ! -f "$fixture" ]; then
  echo "usage: $0 <fixture.maude> [-v]" >&2
  exit 2
fi
fixture=$(cd "$(dirname "$fixture")" && pwd)/$(basename "$fixture")
fixdir=$(dirname "$fixture")

if [ ! -x "$TNK_BIN" ]; then
  echo "error: tnk binary not found at $TNK_BIN (cargo build --release first)" >&2
  exit 2
fi
if [ ! -f "$ORACLE_LIB/prelude.maude" ]; then
  echo "error: oracle prelude not found at $ORACLE_LIB/prelude.maude" >&2
  exit 2
fi

tmpdir=$(mktemp -d "${TMPDIR:-/tmp}/diffmaude.XXXXXX") || exit 2
trap 'rm -rf "$tmpdir"' EXIT

normalize() {
  awk '
  {
    # strip interactive prompts (any run of them at line start)
    while (sub(/^Maude> /, "")) { }

    # diagnostic-block openers (both sides; symmetric)
    if ($0 ~ /^(Warning:|Advisory:|error:|parse error:|error in module)/) {
      inblock = 1
      next
    }

    if (inblock) {
      # a block runs until the next recognizable real-output line
      if ($0 ~ /^=+$/ || $0 ~ /^Bye\.$/ ||
          $0 ~ /^(reduce|rewrite|frewrite|erewrite|search|match|xmatch|srewrite|dsrewrite|continue|parse|unify|variant) / ||
          $0 ~ /^(rewrites:|states:|result |Solution |No solution|No more solutions|No match|empty substitution)/ ||
          $0 ~ /^(state [0-9]|arc [0-9])/ || $0 ~ /^\*\*\*\*/ ||
          $0 ~ /^(fmod |mod |fth |th |smod |omod |oth |view |tambanokano REPL )/) {
        inblock = 0
      } else {
        next
      }
    }

    # separators / banner / Bye.
    if ($0 ~ /^=+$/) next
    if ($0 ~ /^tambanokano REPL /) next
    if ($0 ~ /^Bye\.$/) next

    # timing tails (counts stay)
    if ($0 ~ /^rewrites: [0-9]+ in /) { sub(/ in .*/, "") }
    else if ($0 ~ /^states: [0-9]+ +rewrites: [0-9]+ in /) { sub(/ in .*/, "") }

    print
  }'
}

# ---- oracle side -----------------------------------------------------------
# BOTH_NO_PRELUDE=1: run BOTH binaries prelude-free (the legacy prelude-* fixtures define their
# own copies of prelude modules from scratch — with a standing prelude the oracle refuses to
# redefine its protected modules, so the designed comparison is prelude-free on both sides).
oracle_flags=()
[ "${BOTH_NO_PRELUDE:-0}" = "1" ] && oracle_flags+=(-no-prelude)
( cd "$fixdir" && MAUDE_LIB="$ORACLE_LIB" timeout "$TIMEOUT_SECS" \
    "$ORACLE_BIN" -no-banner -no-advise ${oracle_flags[@]+"${oracle_flags[@]}"} "$fixture" </dev/null ) \
    >"$tmpdir/oracle.raw" 2>&1
rc=$?
if [ $rc -eq 124 ]; then
  echo "TIMEOUT(oracle) $fixture"
  exit 3
fi

# ---- tnk side --------------------------------------------------------------
tnk_input=$fixture
tnk_flags=()
if [ "${BOTH_NO_PRELUDE:-0}" = "1" ]; then
  tnk_flags+=(-no-prelude)
elif [ "$TNK_STANDING_PRELUDE" = "1" ]; then
  # TNK_ASSUME_PRELUDE=1: treat every fixture as prelude-dependent (the legacy-corpus sweep —
  # those fixtures predate the marker convention; the oracle always has its prelude standing).
  if [ "${TNK_ASSUME_PRELUDE:-0}" != "1" ] && ! grep -q '^\*\*\* PRELUDE' "$fixture"; then
    tnk_flags+=(-no-prelude)
  fi
else
  if grep -q '^\*\*\* PRELUDE' "$fixture"; then
    cat "$ORACLE_LIB/prelude.maude" "$fixture" >"$tmpdir/tnk-input.maude"
    tnk_input=$tmpdir/tnk-input.maude
  fi
fi
( cd "$fixdir" && MAUDE_LIB="$ORACLE_LIB" timeout "$TIMEOUT_SECS" \
    "$TNK_BIN" -no-banner ${tnk_flags[@]+"${tnk_flags[@]}"} "$tnk_input" </dev/null ) \
    >"$tmpdir/tnk.raw" 2>&1
rc=$?
if [ $rc -eq 124 ]; then
  echo "TIMEOUT(tnk) $fixture"
  exit 4
fi

# ---- compare ---------------------------------------------------------------
normalize <"$tmpdir/oracle.raw" >"$tmpdir/oracle.norm"
normalize <"$tmpdir/tnk.raw"    >"$tmpdir/tnk.norm"

if diff -u --label oracle --label tnk "$tmpdir/oracle.norm" "$tmpdir/tnk.norm"; then
  [ "$verbose" = "-v" ] && cat "$tmpdir/oracle.norm"
  exit 0
else
  exit 1
fi
