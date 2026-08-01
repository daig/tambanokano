#!/usr/bin/env bash
# tools/conformance-suite.sh — run every top-level conformance/*.maude fixture against the live oracle,
# allowing only the enumerated accepted divergences. Prints one line per fixture and a final
#   CONFORMANCE <n>/<m> CLEAN
# Exit 0 iff n = m.
#
# Per-class handling (each documented at its site):
#   - prelude-*.maude        BOTH_NO_PRELUDE=1: these bootstrap fixtures define their own copies
#                            of prelude modules; a standing oracle prelude refuses to redefine
#                            its protected modules, so the designed comparison is prelude-free
#                            on both sides (tnk -no-prelude + maude -no-prelude).
#   - everything else        TNK_ASSUME_PRELUDE=1: unmarked top-level fixtures require the standard
#                            prelude on both sides.
#   - accepted divergences   a fixture with a recorded diff in conformance/accepted-diffs/<id>.diff
#                            is CLEAN iff its current diff is BYTE-IDENTICAL to the recorded one
#                            (drift beyond the accepted divergence = FAIL). See that directory's
#                            README for the complete allowlist.
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
  accepted="$ROOT/conformance/accepted-diffs/$id.diff"
  case "$id" in
    prelude-*)
      diff_out=$(BOTH_NO_PRELUDE=1 "$ROOT"/tools/diffmaude.sh "$f" 2>&1)
      rc=$?
      ;;
    *)
      diff_out=$(TNK_ASSUME_PRELUDE=1 "$ROOT"/tools/diffmaude.sh "$f" 2>&1)
      rc=$?
      ;;
  esac
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

echo "CONFORMANCE $pass/$total CLEAN"
[ "$pass" -eq "$total" ]
