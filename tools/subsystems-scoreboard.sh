#!/usr/bin/env bash
# tools/subsystems-scoreboard.sh — the subsystems-goal progress metric
# (docs/migration/subsystems-goal.md §1.2).
#
# Runs every fixture in conformance/subsystems/*.maude through tools/diffmaude.sh
# (same harness and normalization as the audit scoreboard; per-fixture 60s timeout
# on each side, a timeout is a FAIL attributed to whichever side hung), prints one
# PASS/FAIL line per fixture and a final
#   SUBSYSTEMS <n>/<m> PASS
# Exit 0 iff n = m. ID prefixes: U* unification, V* variants, N* narrowing,
# T* SMT, M* model checker, I* meta-interpreters (local mode).
#
# Options:
#   -d    also print the diff for each failing fixture

set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
show_diffs=0
[ "${1:-}" = "-d" ] && show_diffs=1

pass=0
total=0
for f in "$ROOT"/conformance/subsystems/*.maude; do
  [ -e "$f" ] || { echo "no fixtures found in conformance/subsystems/" >&2; exit 2; }
  id=$(basename "$f" .maude)
  total=$((total + 1))
  out=$("$ROOT"/tools/diffmaude.sh "$f" 2>&1)
  rc=$?
  case $rc in
    0) echo "PASS $id"; pass=$((pass + 1)) ;;
    3) echo "FAIL $id (oracle timeout)" ;;
    4) echo "FAIL $id (tnk timeout)" ;;
    2) echo "FAIL $id (harness error)"; [ -n "$out" ] && echo "$out" | sed 's/^/    /' ;;
    *) echo "FAIL $id"
       if [ $show_diffs -eq 1 ] && [ -n "$out" ]; then
         echo "$out" | sed 's/^/    /'
       fi ;;
  esac
done

echo "SUBSYSTEMS $pass/$total PASS"
[ "$pass" -eq "$total" ]
