# Recorded accepted divergences (criterion 3, correctness-goal.md §1.3)

A legacy fixture with a recorded diff here is CLEAN iff its current diff is byte-identical to
the recording (tools/legacy-sweep.sh); any drift beyond the recording fails the sweep.

- `objects.diff` — mixed-symbol ACU argument print order in the search-goal echo.
  Accepted divergence #1 (enumerated in the goal contract).
- `acu-match.diff` — AC match-solution enumeration order; programmatically verified set-equal.
  Accepted divergence #2 (enumerated in the goal contract).
- `strategy.diff`, `prelude-meta.diff` — per-solution REWRITE COUNTS only (values, solution
  order, and echoes byte-identical): the matchrew/amatchrew sub-search interleaving and the
  search exploration schedule for indexed solutions (fable-audit.md §3.3 [D]: "values, order,
  reachability faithful … the faithful mechanism is Maude's parallel SubtermTask/rewriteTask
  odometer — a scheduler change, not a counting tweak"; the lazy-vs-frontier note under =>!).
  These were NOT in the goal's four enumerated accepted divergences — they are audit-documented,
  deliberately unfixtured (the manifest pinned this class only where dsrewrite coincides), and
  recording them here was flagged as a criterion-3 amendment and RATIFIED by the user 2026-07-05. Object-level
  search/srewrite counts are oracle-conformant (fixtures B2a/B2b, the search/strategy corpora);
  the residual is confined to (i) matchrew per-solution cumulative counts and (ii) metaSearch
  indexed-solution billing where the meta-down rule order interacts with lazy exploration.
