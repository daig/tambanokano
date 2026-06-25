# Known gaps from the reference (within the built engine)

Where our **built** functional engine differs from, simplifies, or defers something Maude does. (Not-yet-built
*features* are in `roadmap.md`; this is about the parts that already exist.) Three kinds: **accepted
divergences** (won't fix), **deferred optimizations** (correct now, faithful-when-ported), and **deferred
sub-features / robustness**. Everything here was found by differential testing; none affects a well-formed
spec's value / sort / rewrite count / termination unless noted.

## 1. Accepted divergences — output-only, won't fix

These reproduce a semantically-empty Maude-internal artifact; the differential harness absorbs them
(set-comparison for orderings; no fixture asserts the divergent surface).

- **ACU print / match-solution order.** Our kernel orders AC arguments by `SymbolId`; Maude orders by
  `Symbol::orderInt`. Same multiset → identical equality / normal forms / sorts / counts; only the printed
  argument order (`5 + x` vs `x + 5`) and the AC **match-solution enumeration** order (Maude's Diophantine
  order) differ. Match solutions are **set-compared** in the conformance harness. Hits `nat`, `acu-*` — the
  most common cosmetic delta.
- **Multi-top component sort-index order.** Maude's `ConnectedComponent` "sort index" (a DFS-topological
  numbering, `Core/sort.cc`) leaks into two outputs: the **kind label** order (`[B,D,A]` vs our declaration-
  order `[A,B,D]`, only for a kind-level term in a multi-maximal component) and the **incomparable-membership
  tiebreak** (`sortConstraintLt`, only a *contradictory* spec). Proven load-bearing for **no** computed
  result (least-sort is down-set intersection + op-decl-order tiebreak, not index comparison). The ~40-line
  port recipe (per-component DFS numbering) is recorded if byte-parity is ever needed, but reproducing it
  would be over-indexing on an implementation detail.
- **REPL-vs-batch framing.** The piped reference prints `====` separators between command results, a startup
  banner, and `Bye.` on exit; our REPL omits these. Structural, not term-rendering — the echo / result /
  count / trace content matches byte-for-byte (incl. line-wrapping).

## 2. Deferred optimizations — correct now, perf-only, port when it matters

Faithful results today via a simpler mechanism; porting Maude's optimized version is a throughput step, not a
correctness fix.

- **AC / AU / CUI matcher.** We match modulo the axioms by **naive backtracking enumeration** (greedy
  smallest-first for reduce, full enumeration for `match`), not Maude's optimized **bipartite + Diophantine**
  solver. Correct (reduce counts conform; match sets conform) but un-optimized; the optimized matcher is a
  prerequisite for heavy AC `search`.
- **Sort computation.** Least sorts come from direct `findMinSortIndex`-style iteration (down-set GLB), not
  Maude's precompiled **flattened sort-decision diagram**. Same result; the diagram is a per-application
  speedup.
- **Throughput headroom generally.** fib runs ~6–8 M rw/s (session-noisy); Maude is faster on compiled
  matching. The gap is matcher/sort-table compilation, not the reduce loop or GC, which are already iterative
  and bounded. (One deliberate cost: C7's `nf` field adds ~6% to no-sharing reductions like fib — accepted
  for the structure-sharing count fidelity it buys.)

## 3. Deferred sub-features (within built areas) + robustness

- **Operator attributes `frozen` / `memo`.** Parsed-area attributes not yet wired into reduction (`ctor` and
  `strat` are). `frozen` blocks reduction of listed args; `memo` caches results. Add with the rule machinery
  (`frozen` matters most for rewriting) / as a perf cache.
- **Cross-kind ad-hoc overloading.** Overload resolution handles single-kind (subsort) overloading; cross-kind
  ad-hoc overloading (arg-sort-driven kind selection) is `debug_assert`-guarded, not implemented. Idiomatic
  signatures don't need it; the prelude may.
- **Diagnostics sink.** Maude warns on non-preregular signatures, collapse-prone membership patterns, etc. We
  compute the preregularity bit but emit no warning (no diagnostics surface yet). Results are unaffected; the
  user-facing advisory text is missing.
- **Membership collapse matching.** A membership lhs that collapses under an identity (`mb a L : Lst` with
  `[id: nil]`) — Maude applies it to the collapsed sub-element too (and warns on such patterns); we don't.
  Pre-existing edge, affects ill-formed-ish patterns only.
- **Interruptibility.** Maude's Ctrl-C aborts a runaway reduce; our REPL can't yet interrupt an in-progress
  reduction (a signal-checked reduce loop — the real concern once `rew`/`search` can diverge). Note: this is
  *not* the rejected F-1 "no-op rewrite guard" — Maude itself loops on `eq a = a`, and we match that; adding a
  guard would *introduce* a divergence.

## Resolved (here for cross-reference; detail in git history)

The Phase-1.5 sweep closed: eager→lazy membership timing (C1), cross-theory alien-subterm matching (C8/C5),
the engine-global condition-reduce GC root set (C6/F-2), structure sharing (C7), the frontend-fidelity cluster
(float/glued-minus/rational/echo, C9–C11), the deep-chain pretty-printer overflow (C12), and long-output
line-wrapping (C13). The F-3 (ExtensionInfo) / F-4 (`Subst` unbind) matcher-seam gaps were closed in B1.
