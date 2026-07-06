# T0 — SMT spike: D7 gate + the oracle's missing solver (early derisk report)

Run 2026-07-05/06, ahead of phase T by user decision (derisk-the-spikes pass, together with the
D9/D10/D11 + criterion-3 ratifications and the early D12 record). Two deliverables: the **D7 binding
resolution** (z3 crate confirmed) and a **repaired oracle** (the local reference binary had no SMT
solver linked at all). Spike code: `spikes/smt-spike/` (standalone crate, not a workspace member).

## 1. Finding: the oracle had no SMT solver

The `maude` on PATH is the locally-built `Opt-buddy-bison` binary, configured `--with-yices2=no
--with-cvc4=no`: every SMT command answered `Warning: No SMT solver linked at compile time. …
undecided`. Phase T could not have been oracle-diffed against it.

**Repair (user-approved):** a sibling build `Opt-buddy-bison-yices2` configured `--with-yices2=yes`
against the brew-installed Yices2 (same LDFLAGS/CPPFLAGS as the original; brew keg-only bison ≥ 3 on
PATH — the Apple `/usr/bin/bison` 2.3 fails on `surface.yy`). Validation:

- `tests/Misc/smtTest.maude` through the new binary matches upstream's checked-in
  `smtTest.expected` **exactly on all non-warning lines** — all 61 `Result from sat solver is:`
  verdicts identical; the only diffs are warning *placement* (upstream's file was generated via
  stdin), and the conformance harness strips warning blocks anyway.
- Baseline neutrality: F1 (audit scoreboard) and F2 (legacy sweep) re-run with `ORACLE_BIN`
  pointing at the new binary — both green, so switching the standing oracle changes nothing
  outside SMT surfaces. The `~/.local/bin/maude` wrapper now execs the Yices2-enabled build.

## 2. Why solver identity cannot leak into fixture bytes (3.5.1)

Verified across the C++ source, the manual (ch. 16), and the reference tests:

- `check` prints exactly one solver-derived token: `sat` / `unsat` / `undecided`
  (`Mixfix/execute.cc`).
- `smt-search` solutions print the state term, the substitution, and the accumulated **symbolic**
  constraint (`where -2 < 0`) — all engine-rendered; solver models are never printed.
- 3.5.1 has no `metaSmtCheck` (no meta surface returns satisfying assignments).

So any two correct solvers over the decidable QF_LIA/QF_LRA fragments produce byte-identical Maude
output: tnk-on-z3 vs oracle-on-Yices2 is safe by construction, and the D6-style cross-library
order-fidelity problem has no analogue here.

## 3. The D7 gate probes (all green)

`spikes/smt-spike/` against brew `libz3` (z3 crate 0.12 / z3-sys 0.8; build needs
`Z3_SYS_Z3_HEADER=/opt/homebrew/include/z3.h` and `-L /opt/homebrew/lib` — the production feature
gate should carry that plumbing):

- **P2 — fixture-shaped verdicts.** The `smtTest` Boolean shapes plus QF_LIA/QF_LRA probes: z3's
  verdicts match `smtTest.expected` AND the Yices2 oracle on every case. (One transcription error in
  the spike's own expected table was caught by the oracle — `X=/=true ∧ X=/=Y ∧ Y=/=false` is `sat`.)
- **P3 — the gate question: incremental push/pop ≡ fresh-solver semantics.** 40 seeded random
  linear-integer constraint trees explored DFS with ONE incremental solver (push on descend, pop on
  backtrack, prune on unsat — the `smt-search` shape) vs a fresh solver per node over the
  accumulated conjunction: **894 nodes, zero verdict divergences, assertion stacks balanced after
  every tree.** This is the property Maude's `smt-search` pruning assumes of its
  `VariableGenerator` (assert/check/push/pop) seam.
- **P4 — Maude value mapping.** 40-digit integer coefficients (bignum numerals via string), exact
  rational `Real` semantics (r+r+r=1 forces r=1/3), and Int→Real coercion (`toReal`) all behave.

## 4. D7 resolution deltas

1. **z3 crate confirmed** as the default backend behind `trait SmtEngine` (assert/check/push/pop/
   fresh-var), feature-gated `smt-z3`; default build stays pure Rust. cvc5/yices2 remain recorded
   alternates — unmotivated now that output is proven solver-independent.
2. The trait's incremental contract can mirror Maude's `VariableGenerator` seam directly; no
   semantic adaptation layer is needed (P3).
3. Bignum/rational translation goes through string numerals (P4) — no i64 truncation path.
4. The conformance target for phase T is verdict + engine rendering only; solver models are out of
   scope by construction (§2). If a future Maude version adds a model-printing surface, that is a
   new conformance-boundary decision, not covered here.
