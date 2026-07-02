# Correctness goal — audit-conformance scoreboard (the `/goal` contract)

This document is the **contract for the correctness goal**: the target, the verifiable metric, the frozen
work manifest, the decision defaults, and the completion criteria. Ground truth for every finding referenced
here: **`fable-audit.md`** (repo root; § references below are into it). Plan context: `roadmap.md` phases
0–D. The goal driver re-reads THIS file each session; the scoreboard (below) is the single progress number.

**Goal statement.** Close every in-scope behavioral deviation from Maude 3.5.1 found by the audit —
crashes, silent wrong values, wrong counts, rejections of legal input, extra acceptance, and the AC
availability hang — verified continuously against the live oracle, without regressing anything that
already conforms. Tool-surface (`show`/`set print`/debugger), diagnostics text parity, and new subsystems
(symbolic/SMT/model-checking/meta-interpreters/Full Maude) are explicitly **out of scope** (roadmap E–G).

---

## 1. The metric

### 1.1 Instrument (built and committed as step 0, before any fix)

- **`tools/diffmaude.sh`** — the oracle-diff harness. Oracle: `MAUDE_LIB=~/code/maude-lang/maude/src/Main
  maude -no-banner -no-advise <fixture> </dev/null` (binary `maude` 3.5.1 on PATH). tnk:
  `target/release/tnk-repl` — until fixture C6c lands, preload by concatenating
  `~/code/maude-lang/maude/src/Main/prelude.maude` in front of prelude-dependent fixtures; after C6c,
  invoke the binary directly (standing prelude) with `-no-prelude` for self-contained fixtures.
- **Normalization (exact; nothing else may be stripped):** the `====…` separators, the tnk banner line,
  `Bye.`, `Maude>` prompts; the timing tail of `rewrites: N in …` / `states: N  rewrites: M in …` lines
  (**the counts stay**); oracle `Warning:`/`Advisory:` blocks (first line + indented continuations —
  diagnostics parity is roadmap phase E, not this goal); tnk `error:` / `parse error:` / `error in module`
  blocks (same rationale, symmetric); pre-C6c only: tnk's two LEXICAL/LOOP-MODE build-error lines.
  Everything else — echoes, `result`/`Solution` lines, sorts, counts, bindings, traces — compares
  **byte-exact**. This rule makes every fixture class self-checking: a REJECT fix passes when the missing
  result lines appear; an EXTRA fix passes when tnk's spurious result lines disappear; count fixes compare
  the preserved `rewrites:` numbers.
- **`tools/audit-scoreboard.sh`** — runs every fixture in `conformance/audit/` through the harness
  (per-fixture `timeout 60`; a timeout is a FAIL attributed to whichever side hung), prints one
  `PASS`/`FAIL` line per fixture and a final `SCOREBOARD <n>/<m> PASS`; exit 0 iff n = m. **`n/m` is the
  goal's progress number**; report it after every work unit.

### 1.2 Denominator discipline

The manifest in §2 is the **frozen denominator** (m ≈ 74). Fixtures may be *added* (a fix that uncovers a
new deviation adds a fixture and grows m — that is progress in honesty, not regression); fixtures may
never be removed, weakened, or re-normalized away without an explicit user decision recorded here. Each
fixture is seeded from the audit's minimal repro for that finding.

### 1.3 Completion criteria (all five; then the goal is done)

1. `tools/audit-scoreboard.sh` exits 0 (every manifest fixture PASS).
2. `cargo test --release` fully green.
3. The legacy `conformance/*.maude` corpus is harness-clean against the live oracle, modulo ONLY the
   enumerated accepted divergences: mixed-symbol ACU argument print order, AC match-solution enumeration
   order (set-equal), meta-module echo grouping/element order, multi-top kind-label order (§3.7). Any
   other legacy diff = regression = FAIL.
4. Stock library files load through the tnk binary error-free (modulo stripped advisories):
   `term-order.maude`, `machine-int.maude`, `linear.maude` from `~/code/maude-lang/maude/src/Main/`.
5. `fable-audit.md` is updated as the ledger: every closed finding annotated `RESOLVED (<commit>)` in
   place; §3.9 constraints re-verified where touched.

## 2. Fixture manifest (the frozen work list)

One fixture per line: `conformance/audit/<ID>.maude`. Pass criterion is §1.1 harness-clean unless noted.
Fix guidance lives in `roadmap.md` under the matching phase letter; **read the cited §3.9 items BEFORE
touching that area.**

### Tier A — panics and silent wrong values

| ID | Audit | Fixture content / pass note |
|---|---|---|
| A1a-iter-nonlinear | §3.1 | `eq f(X, s X) = z` over `[iter]`; `reduce f(z, s z)` → `z`, no panic |
| A1b-opdecl-arity | §3.1 | `op _+_ : A A A -> A .` loads (op disabled), use yields oracle-equal output, session survives |
| A1c-unbound-rhs | §3.1 | `eq wrap(A:S) = B:S`; `reduce wrap(x)` → unreduced, session survives; incl. via parameterized instance |
| A2a-neg-shifts | §3.2 | `-8 >> 1`→`-4`, `-1 >> 100`→`-1`, `-5 << 2`→`-20`, `-1 >> 10^26`→`-1` |
| A2b-nan-gating | §3.2 | `Infinity - Infinity` etc. all stay unreduced; sqrt(-1.0)/x/0.0 family still unreduced |
| A2c-escapes-lex | §3.2 | `"\101\102\103"`→`"ABC"`; `\a\b\f\r\v` preserved |
| A2d-escapes-print | §3.2 | `char(0)/(7)/(13)/(127)` print `\000 \a \r \177` |
| A2e-divides-zero | §3.2 | `0 divides 5` / `0 divides 0` stay at `[Bool]` |
| A2f-char-domain | §3.2 | `char(256)` unreduced |
| A2g-float-accept | §3.2 | `float("NaN"/"nan"/"inf"/"5")` unreduced; `float("Infinity")` still works |
| A2h-negzero-eq | §3.2 | `- 0.0 == 0.0` → `true` |
| A2i-qid-norm | §3.2 | `string(qid("a b"))` → `"a`b"`; qid("a b") == qid("a`b") |
| A2j-string-bytes | §3.2 | byte semantics: `length("héllo")`→6, `substr("héllo",1,1)`→`"\303"`, `ascii("é")` unreduced |
| A3a-rewrite-frozen | §3.2 | `rew g(a)` with `g [frozen]` → 0 rewrites; partial `frozen (2)`; §3.9.2: eqs still reduce |
| A3b-import-order | §3.2 | local-statements-first: rule pair, eq pair, 3-level search order — **land with the META `up*` suffix change; roadmap risk 1** |
| A3c-id-only | §3.2 | `[id: e]` without assoc/comm applies (`a o e`→`a`; compound case) |
| A3d-idem-only | §3.2 | `[idem]` without comm applies (`a o a`→`a`) |
| A4a-mixfix-rename | §3.2 | `M * (op _+_ to _plus_)`: `x plus y` parses; renamed module WITH a `_+_` statement builds |
| A4b-view-mixfix | §3.2 | op→op views across the {prefix,mixfix}² matrix compute (`op _#_ to _+_` instance reduces) |
| A4c-redef-invalidate | §3.2 | redefine imported module / view → dependent recomputes with the new definition |
| A4d-fake-param-sort | §3.2 | `X$Foo` (Foo ∉ theory) survives instantiation unrenamed |
| A4e-param-rename-shield | §3.4 | renaming a parameter-theory sort is ignored; module builds |
| A5a-downterm-flat | §3.2 | `downTerm('_+_[a,b,c], 99)` → `9` (assoc-aware meta resolution) |
| A5b-metareduce-flat | §3.2 | `metaReduce(['NAT], flat 3-arg)` computes |
| A5c-meta-strat-attr | §3.2 | meta-module carrying a `strat (…)` op attribute down-translates; metaReduce computes |
| A5d-metanormalize | §3.2 | user equations NOT applied; AC structural reorder still normalizes |
| A5e-upmodule-params | §3.2 | `upModule('LIST, false)` → `fmod 'LIST{'X :: 'TRIV}` with ditto-expanded attrs on all `'__` overloads |
| A5f-metaxapply-hole | §3.3 | AC hole context residue-first (`'_+_['b.S, []]`) |

### Tier B — counts and enumeration (separable from D2)

| ID | Audit | Fixture content / pass note |
|---|---|---|
| B1a-collapse-values | §3.2 | `eq a + X = c` `[assoc comm id: e]`: `red a`→`c`; `red a + b`→`b + c`; AU + CUI analogs. **§3.9.4 one-shot** |
| B1b-collapse-counts | §3.2 | `makeSet` family 2/4/6; `red e`=1, `red f`=2 (`ac-matcher-plan.md` §3.2 targets) |
| B2a-suchthat-counts | §3.3 | per-solution 4/12/20 incl. condition rewrites |
| B2b-bang-snapshot | §3.3 | `=>!` first-solution `states: 5 rewrites: 4`; metaSearch `'!` 6 |
| B3-mb-extension | §3.3 | `mb (a | a) : Special` on `a | a | a` → 1 rewrite; cmb 3 |
| B4-noparse-position | §3.3 | `metaParse` of `'a 'b` → `noParse(1)` |
| B5-graph-arcs | §3.3 | same-successor rules merge into one arc; rule text prints `f(2)` |

### Tier C — input acceptance and hygiene

| ID | Audit | Fixture content / pass note |
|---|---|---|
| C1a-rational-glued | §3.4 | `1/6`, `2/4`→`1/2` (1 rw), `-7/3`, `1/6 + 1/6`, `probe(1/6)` |
| C1b-bignum-literals | §3.4 | `18446744073709551616` parses; `2 ^ 100` output re-reads |
| C1c-float-forms | §3.4 | `1.` `.5` `1.e3` `.5e2` `1e3` `Infinity` accepted; `1.5e`/lone `.` still rejected |
| C1d-iter-input | §3.4 | `s_^10(z)`; `s_^k` bignum k; `s_^2(s_^k(z))` folds; NAT `s_^k(0)` |
| C2a-eq-labels | §3.4 | `eq [l] :` / `ceq [l] :` / `mb [m] :` / `cmb [m] :` all parse and fire |
| C2b-stmt-recovery | §3.4 | one bad statement dropped, module + later commands compute |
| C2c-bracket-lhs | §3.4 | `rl [N] => [N + 1]` over `op [_]` |
| C2d-junk-recovery | §3.4 | trailing junk tokens skipped, following module runs; comment before `select`/`show` |
| C2e-one-sided-id | §3.4 | `left id:` / `right id:` parse; basic AU collapse behavior matches |
| C2f-kind-brackets | §3.4 | `[A,B]` in op/var declarations |
| C2g-id-forward-ref | §3.4 | `id:` constant declared after the op |
| C2h-frew-gas | §3.4 | `frew [6, 2]` → oracle result/count |
| C2i-matchrew-pipe | §3.4 | bare `|` inside matchrew/amatchrew pattern |
| C2j-nonground-reduce | §3.4 | `red X:A .`, `red g(X, a) .` reduce open terms; declared-var print parity |
| C2k-two-commands | §3.4 | `red a . red b .` on one line → both rejected (as oracle) |
| C3a-renamed-inst | §3.4 | `protecting (M * (sort S to T)){V}` builds and computes |
| C3b-arity-rename | §3.4 | `op f : A B -> C to g` renaming |
| C3c-label-rename | §3.4 | `label l to m` |
| C3d-opterm-views | §3.4 | `op lt(A, B) to term A < B` (variable-argument op→term) |
| C3e-oo-rename-views | §3.4 | `class`/`attr`/`msg to` renaming + view items desugar |
| C3f-pconst | §3.4 | `[pconst]` accepted; enclosing theory + instantiation behave as oracle |
| C3g-decl-attrs | §3.4 | `generated-by` declarations + `rpo` attribute accepted as oracle |
| C4a-theory-import | §3.6 | theory imported into fmod → module unusable, axioms never execute (sentinel probes) |
| C4b-free-param-import | §3.6 | importing a free-parameter module rejected |
| C4c-self-import | §3.6 | `protecting M` inside M rejected |
| C4d-dotted-sorts | §3.6 | `sort A.B .` rejected |
| C4e-zero-bounds | §3.6 | `rew [0]` / `search [0]` rejected at parse |
| C4f-print-attr-check | §3.6 | malformed `[print …]` drops the statement (effective ruleset = oracle's) |
| C5-ambiguity-pick | §3.4 | `f a g` → `(f a) g` computed; non-assoc `a + b + c` → `(a + b) + c`. **Must match the oracle's pick on these cases — if the implementation cannot, STOP and escalate (decision D9)** |
| C6a-implicit-bool | §3.4 | module without explicit BOOL import uses `==`/`if_then_else_fi`/`and`; `set include BOOL off` honored |
| C6b-load-cmd | §3.4 | `load <relative file>` + `sload`; loaded module usable |
| C6c-standing-prelude | §3.4 | plain `tnk-repl file.maude` has NAT/BOOL (auto-prelude); `-no-prelude` + `-no-banner` flags work |

### Tier D — architecture-backed items

| ID | Audit | Fixture content / pass note |
|---|---|---|
| D1a-import-reparse | §3.4 | X-capture EXT builds; op-collision B2 builds; `protecting CONVERSION + META-LEVEL` module builds (home-grammar point-fix; **full rework needs user decision D10**) |
| D2a-ac-hang | §3.5 | 30-element `SET{Nat}` cardinality completes with oracle result inside the 60s harness timeout |
| D2b-xmatch-sets | §3.3 | AU-with-id `X Y <=? a b c` = 10 matchers; `xmatch X:Nat <=? 3` = 3; AU bare-var = 3 |
| D2c-infix-fold | §3.3 | `2 + 3 + 4` = 2 rewrites (prefix `gcd(12,18,8)` stays 1 — §3.9.3); `upTerm(2+3+4)` count 3; trace shows two steps |
| D2d-metaparse-nested | §3.2 | `metaParse` returns the nested surface parse |
| D3-large-term | §3.5 | 2000-element flat AC sum: parse+reduce+print completes within timeout, oracle-equal |

### Exclusions (in the audit, deliberately NOT in the denominator)

- Rewrite-condition infinite recursion (§3.1d): after the iterative fix both engines spin forever —
  verify manually (`timeout` both sides; tnk must not stack-overflow); not oracle-diffable.
- The collapse case where Maude itself loops (`eq X Y = c` over `[assoc id: nil]`, `reduce nil`, §3.2):
  faithful behavior is nontermination; manual bounded check only.
- `upModule` of a strategy module emitting `strat`/`sd` (§3.2): requires the strategy-meta up-translation
  (roadmap G1) — out of scope.
- `metaMeta` degenerate result and `upImports`-on-broken-module (§3.2): medium-confidence /
  needs unusable-module tracking (phase E) — out of scope; note findings if touched.
- Everything in §3.7 (cosmetic/diagnostic), the timing display, search tracing, garbage-term parse cap:
  phases E/F.

## 3. Decision defaults (provisional — record in `03-open-decisions.md` when adopted, flag for user review)

- **D9 (ambiguity):** warn-and-pick. The pick must match the oracle on the C5 fixture cases; if it
  structurally cannot, stop and ask the user rather than shipping a divergent pick.
- **D10 (statement representation):** home-grammar point-fix ONLY. The full compiled module algebra is a
  user decision; do not start it.
- **D11 (REPL identity):** standing prelude on by default, `set include BOOL on` semantics after prelude
  load, `load`/`sload` with a `MAUDE_LIB`-style search path, `-no-prelude`/`-no-banner` flags. The engine
  library stays prelude-free; this is REPL-layer only (consistent with D5).

## 4. Working rules

- **Fixtures first**: a fix lands in the same commit as its now-passing fixture(s); run the scoreboard +
  `cargo test` before every commit; never pin tnk output as expected.
- **§3.9 gate**: before working any area, re-read the matching `fable-audit.md` §3.9 item; they encode the
  known wrong-fix traps (no-op guard, frozen scope, pairwise-fold, one-shot collapse, `nf` field, flat-mode
  `special` inversion).
- **Order**: tiers in sequence (A → B → C → D); within a tier, any order — items are independent except
  A3b's coupling (land with the `up*` suffix change) and B1 before D2 (its fixtures become D2's
  regression net).
- **Subagents/workflows**: fan out mechanical breadth (fixture authoring from the audit repros, per-item
  differential verification, C++-reference reading) to opus subagents; keep every fix's design decision
  and the final oracle verification in the main loop. The AC port (D2) follows `ac-matcher-plan.md`'s own
  phasing with the naive matcher as live cross-check oracle.
- **Ledger**: on closing a finding, annotate it in `fable-audit.md` (`RESOLVED (<commit>)`); the audit
  stays the definitive record.
- No implementation-time estimates anywhere (project rule); progress is the scoreboard number.
