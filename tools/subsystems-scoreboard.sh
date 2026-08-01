#!/usr/bin/env bash
# tools/subsystems-scoreboard.sh — run conformance/subsystems/*.maude through diffmaude.
#
# Runs ordinary fixtures through tools/diffmaude.sh. T11 instead uses its dedicated native
# value/sort checker: the pinned TNK regression contract is independent of historical
# differential baselines.
# Prints one PASS/FAIL line per fixture and a final
#   SUBSYSTEMS <n>/<m> PASS
# Exit 0 iff n = m. ID prefixes: U* unification, V* variants, N* narrowing,
# T* SMT, M* model checker, I* meta-interpreters (local mode).
#
# Options:
#   -d           also print the diff for each failing fixture
#   -p PREFIX    run only fixture IDs beginning with PREFIX (for example, `-p U`)
set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
show_diffs=0
prefix=
while [ "$#" -gt 0 ]; do
  case "$1" in
    -d) show_diffs=1; shift ;;
    -p)
      [ "$#" -ge 2 ] || { echo "usage: $0 [-d] [-p PREFIX]" >&2; exit 2; }
      prefix=$2
      shift 2
      ;;
    *) echo "usage: $0 [-d] [-p PREFIX]" >&2; exit 2 ;;
  esac
done
case "$prefix" in *[!A-Za-z0-9_-]*) echo "error: invalid fixture prefix '$prefix'" >&2; exit 2 ;; esac

pass=0
total=0
for f in "$ROOT"/conformance/subsystems/"$prefix"*.maude; do
  [ -e "$f" ] || { echo "no fixtures found in conformance/subsystems/" >&2; exit 2; }
  id=$(basename "$f" .maude)
  total=$((total + 1))
  if [ "$id" = "T11-variant-satisfiability" ]; then
    out=$("$ROOT"/tools/variant-sat-check.sh "$f" 2>&1)
  else
    out=$("$ROOT"/tools/diffmaude.sh "$f" 2>&1)
  fi
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
