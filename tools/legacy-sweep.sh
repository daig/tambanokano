#!/usr/bin/env bash
# tools/legacy-sweep.sh — every legacy conformance/*.maude fixture harness-clean
# against the live oracle, modulo ONLY the enumerated accepted divergences.
# Prints one line per fixture and a final
#   LEGACY <n>/<m> CLEAN
# Exit 0 iff n = m.
#
# Per-class handling (each documented at its site):
#   - prelude-*.maude        BOTH_NO_PRELUDE=1: these bootstrap fixtures define their own copies
#                            of prelude modules; a standing oracle prelude refuses to redefine
#                            its protected modules, so the designed comparison is prelude-free
#                            on both sides (tnk -no-prelude + maude -no-prelude).
#   - everything else        TNK_ASSUME_PRELUDE=1 (legacy fixtures predate the marker).
#   - accepted divergences   a fixture with a recorded diff in conformance/accepted-diffs/<id>.diff
#                            is CLEAN iff its current diff is BYTE-IDENTICAL to the recorded one
#                            (drift beyond the accepted divergence = FAIL). The recordings:
#                              objects.diff    — mixed-symbol ACU argument print order in the
#                                                search-goal echo (accepted divergence #1).
#                              acu-match.diff  — AC match-solution enumeration order; verified
#                                                set-equal (accepted divergence #2).
#   - objects-io.maude       SKIP (documented): its STD-STREAM erewrite needs scripted stdin;
#                            under the harness's </dev/null the ORACLE ITSELF dies with
#                            "Maude internal error", so no oracle diff is definable. The fixture
#                            is fully covered by the cargo pin suite (set_stdin-driven).

set -u
ROOT=$(cd "$(dirname "$0")/.." && pwd)

pass=0
total=0
for f in "$ROOT"/conformance/*.maude; do
  id=$(basename "$f" .maude)
  case "$id" in
    objects-io)
      echo "SKIP $id (oracle needs scripted stdin; covered by cargo pins)"
      continue
      ;;
  esac
  total=$((total + 1))
  env=""
  case "$id" in
    prelude-*) env="BOTH_NO_PRELUDE=1" ;;
    *) env="TNK_ASSUME_PRELUDE=1" ;;
  esac
  accepted="$ROOT/conformance/accepted-diffs/$id.diff"
  diff_out=$(eval "$env" "$ROOT"/tools/diffmaude.sh "$f" 2>&1)
  rc=$?
  if [ $rc -eq 0 ]; then
    echo "CLEAN $id"
    pass=$((pass + 1))
  elif [ -f "$accepted" ] && [ "$diff_out" = "$(cat "$accepted")" ]; then
    echo "CLEAN $id (accepted divergence, recorded)"
    pass=$((pass + 1))
  else
    echo "DIFF $id"
  fi
done

echo "LEGACY $pass/$total CLEAN"
[ "$pass" -eq "$total" ]
