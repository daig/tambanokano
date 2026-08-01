# Recorded accepted divergences

A legacy fixture with a recorded diff here is CLEAN iff its current diff is
byte-identical to the recording (`tools/legacy-sweep.sh`); any drift beyond the
recording fails the sweep.

- `objects.diff` — mixed-symbol ACU argument print order in the search-goal echo.
- `acu-match.diff` — AC match-solution enumeration order; programmatically
  verified set-equal.
- `strategy.diff`, `prelude-meta.diff` — per-solution rewrite counts only
  (values, solution order, and echoes byte-identical): matchrew/amatchrew
  sub-search interleaving, and indexed `metaSearch` billing where exploration
  order differs from Maude's parallel odometer. Object-level search/srewrite
  counts remain oracle-conformant (fixtures B2a/B2b and the search/strategy
  corpora).

These four records are the ratified, user-visible divergences the legacy sweep
is allowed to ignore. Everything else must match the live oracle under the
harness normalization contract in `tools/diffmaude.sh`.
