# Roadmap — migration completion (rewritten 2026-07-01, post-audit)

Ground truth for current state: **`fable-audit.md`** (repo root) — the 2026-07-01 differential audit
against Maude 3.5.1. This roadmap sequences the remaining work; every "§" reference below is into the
audit. The build history that used to live here (Phases 0–2, all landed) is in git history.

**Ordering principle: correctness before new feature surface.** Nothing new gets built on top of a layer
with known wrong values. Concretely: first make every *accepted* input compute what Maude computes and
every panic impossible (A, B); then make tnk *accept* what Maude accepts (C); then the two architecture
reworks that block classes of fidelity (D); then diagnostics and the tool surface (E, F); only then the
genuinely new subsystems (G). Within each phase, items are independent unless a coupling hazard is noted.

Per project rule, no implementation-time estimates — each item instead notes what the work touches and
where it is fragile.

---

## 0. Verification method (cross-cutting; institute before phase A)

- **Oracle-in-the-loop CI.** Adopt the audit's `diffmaude.sh` discipline as a checked-in harness: run
  every `conformance/*.maude` through the live `maude` 3.5.1 (prelude pinned via `MAUDE_LIB` to
  `~/code/maude-lang/maude/src/Main`) and the tnk binary, normalize only the cosmetic set (`====`, banner,
  `Bye.`, timing tails), and diff. This kills the pin-drift class the audit found (§4.7: several pins are
  tnk's own divergent output and invisible to the in-repo suite). Where a divergence is *accepted*, encode
  the normalization explicitly in the harness, never in the pin.
- **Fixture policy.** Every fix in phases A–F lands with the audit's minimal repro as a fixture, diffed
  against the live oracle — including fixtures that only a warning line distinguishes (they activate when
  phase E lands).
- **Progress metric.** The C++ suite (`~/code/maude-lang/maude/tests`, 231 tests) is the external KPI:
  8 clean passes at audit time, ~100 gated on phase-G subsystems. Track the clean-pass count per phase;
  phase C+E should move `ResolvedBugs`/`Corner`/`Misc` en masse.

## A. Panics and silent wrong values — localized fixes (§3.1, §3.2)

The highest-severity, mostly-independent repairs. Target behavior in every case is what the oracle does;
where Maude's behavior is warn-and-degrade, the minimal A-phase form is degrade-without-the-warning-text
(the text arrives with phase E).

- **A1. Kill the panic classes (§3.1).** (a) non-linear iter patterns (`s.rs:222` assert → implement the
  pre-bound-count subproblem, or fail the match cleanly); (b) op-decl hole/arity mismatch
  (`engine.rs:1385`, `grammar/build.rs:170` → validate at declaration, disable the op as Maude does);
  (c) unbound RHS/condition variables (`term.rs:371` → reject/disable the statement at build; reachable
  via parameterized instantiation, so the check must run wherever statements are built); (d) the
  rewrite-condition recursion stack overflow → iterative, same transform as the A1/C12 reducer work.
  Fragility: low; each is a guard or a small state machine at a known site.
- **A2. Builtin value bugs (§3.2).** Negative `>>`/`<<` (arithmetic shift, `mpz_fdiv_q_2exp` semantics);
  never produce NaN (gate every float op on `!isNaN(result)` — `floatOpSymbol.cc:398` is the reference);
  string escape lexing (`\a\b\f\r\v` + octal `\ooo`) and printing (escape control/high bytes, octal form);
  `0 divides _` stays unreduced; `char(n > 255)` stays unreduced; `float(String)` acceptance =
  `looksLikeFloat`, not Rust `from_str`; `-0.0 == 0.0` → true; `qid(String)` normalizes specials the way
  `Token` does (`"a b"` ⇒ `` 'a`b ``). Fragility: low; all in `builtin.rs`/`build_term.rs`/`pretty.rs`
  with the C++ reference cited per item in the audit.
- **A3. Engine semantics (§3.2).** (a) `rewrite` honors `frozen` — copy `frewrite_pass`'s check into
  `rewrite_step` (`engine.rs:2420`); remember §3.9.2: frozen blocks *rules only*, never equational
  reduction. (b) **Import statement-application order** — Maude applies the importing module's statements
  first; tnk applies imported-first. The flatten's statement order must flip to local-then-imported.
  **Coupling hazard:** the META `up*` family reads a module's *own* statements as the suffix of the
  flattened trace vectors — flipping the order breaks that suffix assumption, and trace/statement ids
  shift; land the flatten change and the `up*` indexing change together, then re-diff the whole suite
  (no current fixture exercises cross-module statement overlap, so green fixtures do NOT prove this fix —
  add ones that do). (c) `id:`-only and `idem`-only ops classify as CUI, not Free
  (`symbol.rs:482-490`), so their axioms actually apply.
- **A4. Module-algebra wrong values (§3.2).** (a) The mixfix rename family: `rename.rs:77-89` keeps only
  the first literal fragment of a single-token mixfix name — fix the renamed op's syntax record so
  `op _+_ to _plus_` yields a mixfix `_plus_`; the same root breaks op→op views involving mixfix (only
  prefix→prefix works today) — fix in the shared symbol-substitution path, and add the rename/view ×
  {prefix,mixfix}² matrix as fixtures. (b) Redefinition invalidation: redefining a module or view must
  dirty its transitive dependents (re-flatten on next use — the Rc/dirty-set cache design from
  `01-architecture-map.md` §4.5 that was never built). (c) Fake parameter sorts: only substitute `X$s`
  when `s` is declared by the parameter's theory. (d) Renaming items that touch a parameter-theory sort
  are ignored-with-advisory, not applied. Fragility: (a) is the delicate one — the bubble re-writer and
  the decl path must agree on the new spelling.
- **A5. Meta reader/up-translator wrong values (§3.2).** (a) Flat (≥3-arg) assoc meta-terms must
  down-translate: resolution by (name, arity) (`meta.rs:1490,1596`, `descent.rs:74`) needs an
  assoc-aware arm (arity ≥ 2 folds onto the binary symbol) — fixes silent `downTerm` fallbacks and inert
  `metaReduce` on standard metaprogram input. (b) Accept the `strat (…)` op attribute in down-translated
  meta-modules. (c) `metaNormalize` must normalize modulo structural axioms only — split it from
  `meta_reduce` (`meta.rs:94`). (d) `upModule` emits the parameter list of a parameterized module and
  expands `ditto` to full per-decl attribute sets. (e) `metaXapply` AC hole-context argument order
  (residue-first). Fragility: low-to-medium; (d) touches how PreModule parameters are represented at
  up-translation and partially depends on D1's decision.

## B. Counts and enumeration — the separable ones (§3.3)

Count fidelity that does *not* ride the AC rework (that part is D2):

- **B1. Collapse-at-top under `id:`/CUI** — pull `ac-matcher-plan.md` Phase 4 forward (it is explicitly
  separable): unique/multiway collapse matching including the `identity == subject` branch. The
  termination discipline is the trap (§3.9.4: one-shot — `red e` = exactly 1 rewrite; fixpoint hangs,
  skipping undercounts; captured numeric targets in the plan §3.2). This converts the audit's
  wrong-*value* collapse cases (§3.2 [D↑]) into conformance, not just counts. Highest-fragility item in
  this phase — differential-test heavily, watch for loops.
- **B2. `such that` condition rewrites count** (search per-solution counts, §3.3) and the **`=>!`
  solution-snapshot accounting** (snapshot at normal-form confirmation, not state discovery —
  `search.rs:218`; also fixes the metaSearch `'!` delta). Fragility: low; accounting placement.
- **B3. AC memberships through extension** (mb/cmb against sub-multisets). Small matcher-seam addition;
  results already agree, only counts move.
- **B4. `metaParse` failure position** (`noParse(n)` with the real token index).
- Deferred to D2 (do NOT attempt locally): infix builtin-fold counts, xmatch solution *sets* (AU-id
  over-enumeration, iter/AU-bare-var under-enumeration), match-solution order. §3.9.3 explains why the
  fold count is unfixable on the flat representation.

## C. Input acceptance — accept what Maude accepts (§3.4, §3.6)

- **C1. Literal/token classes (§4.6).** Glued rationals (`1/6` — a Rational token class + grammar
  terminal), numerals > 2^64−1 (`build_term.rs:85,210` — bignum literals; the S-count is already bignum),
  float forms (`1.`, `.5`, `1.e3`, `1e3`, `Infinity` — match `looksLikeFloat`; fix the lexer unit tests
  that encode the wrong oracle model, `lex.rs:626`), iter input `s_^k(t)` (wire the deferred
  `Nt::Iter`/`MakeIter`). Closes every prints-what-it-can't-read asymmetry. Fragility: low, lexer-local;
  re-run the full suite for token-classification regressions.
- **C2. Statement syntax + recovery.** Leading bracketed labels on `eq`/`ceq`/`mb`/`cmb` (parser.rs — the
  rl/crl peel generalized); a bad statement drops the *statement*, not the module (and later commands must
  not see a half-module); `[_]`-headed LHS terms; top-level junk-token recovery (warn-and-skip
  token-by-token, consistent across contexts — also fixes the comment-before-`select` desync); `left id:`/
  `right id:`; `[A,B]` multi-sort kind brackets; `id:` forward references (resolve identities after the
  whole op block, constants-first pass); `frewrite [n, gas]`; bare `|` in matchrew patterns; non-ground
  `reduce`/`rewrite` terms (`build_term.rs:234` — build open terms; variables print per Maude's
  declared-vs-on-the-fly rule).
- **C3. Module-expression forms.** `(M * (renaming)){Args}` (stock `linear.maude`); arity-disambiguated
  op renaming (stock `machine-int.maude`); `label l to m`; op→term views with variable arguments; OO
  renaming/view items (`class`/`attr`/`msg to` desugar to sort/op maps); `pconst`.
- **C4. Hygiene enforcement (§3.6 — tnk currently accepts what Maude rejects).** Theories import only as
  parameters (and their axioms must not execute in modules); no importing free-parameter modules; no
  self/circular imports; reject dotted sort names; validate `[print …]` contents; reject `[0]` bounds.
  Fragility: low; each is a check at build/flatten with a clear oracle behavior.
- **C5. Ambiguity policy — decision needed (record as D9 in `03-open-decisions.md`).** Maude warns and
  deterministically takes its first parse; tnk hard-errors (§3.4), which already breaks a stock library
  file through the D1 reparse amplification. Options: (a) reproduce MSCP's pick order (faithful, but an
  MSCP internal — investigate before committing), (b) warn-and-pick tnk's own deterministic first parse
  (documented divergence: same acceptance, possibly different tree on genuinely ambiguous input),
  (c) keep the error (documented stricter divergence). Default recommendation: (b) with the warning,
  revisit (a) if differential testing surfaces real-world inputs where the pick differs.
- **C6. REPL identity — decision needed (record as D11).** To run real `.maude` files: implicit-import
  machinery (`set include <MOD> on/off`, BOOL on by default post-prelude — prelude.maude:31/3233),
  `load`/`sload`/`in` with a search path (`MAUDE_LIB` analog), a standing prelude by default with a
  `-no-prelude` opt-out, and the core CLI flags (`-no-banner`, `-no-prelude`, `-batch`,
  `-random-seed`, `-no-advise`). This intentionally revises the "no standing prelude" stance for the
  *tool*; the embedding/engine layer stays prelude-free (consistent with D5).

**Milestone M-accept:** stock `term-order.maude` (needs D1's point-fix below), `machine-int.maude`,
`linear.maude` load; the C++ suite's REJECT-class diffs disappear; unpatched real-world specs parse.

## D. The two architecture reworks (§4.1, §4.2, §3.5)

- **D1. Import-stable statements — decision needed (record as D10).** Today imports re-parse imported
  statement bubbles in the importer's grammar, making module validity context-dependent (§3.4 fundamental;
  breaks META-MODULE+RAT coexistence, i.e. stock `term-order.maude`). Two tiers:
  - *Point-fix (do first, unconditionally):* parse each imported bubble against its **home module's**
    grammar/var-scope, installing the resulting term into the flattened module. Removes the breakage class
    without restructuring; sibling-var scoping already works this way, so this closes the
    importer-signature × imported-statement exposure.
  - *Full rework (the D10 decision):* compiled, import-stable statement representation (Maude's semantic
    module algebra). Unlocks: build-time typechecking of parameterized modules (not at-instance),
    source-form `show module`, faithful `upModule` parameters (with A5d), and is the natural foundation
    for Full Maude (G7). Decide scope after the point-fix lands and phase F's `show` work quantifies how
    much fidelity the PreModule representation can still deliver.
  Fragility: the point-fix touches flatten's hottest path; the full rework is the largest single item on
  this roadmap — that is *why* it is a recorded decision, not a default.
- **D2. AC matcher port + surface-preserving representation** — execute `ac-matcher-plan.md` (already
  updated with audit targets). Audit-driven re-prioritization: the throughput payoff is no longer
  "forward-looking" — a 30-element set hangs (§3.5), so the Diophantine core is a live correctness-of-
  availability fix. The plan's Phase 6 (surface-preserving representation) now owns three fidelity
  targets, not one: infix fold counts, `metaParse` parse-tree values, and trace shape (§3.2, §3.9.3).
  Phase 5 (extension/residue) owns the xmatch solution-set corners (§3.3), including the S-theory/iter and
  AU-bare-variable under-enumeration the audit added. B1 (collapse) will already have landed — keep its
  fixtures as the Phase-4 regression net.
- **D3. Front-end scaling (§3.5).** The ~cubic parse/build of large well-formed terms (5000-element AC
  sum: >60s vs oracle 30ms) — profile the Earley + term-build path on flat-chain input; likely a
  representation/algorithmic fix in the forest→term walk, independent of D2. Plus the documented
  garbage-term Earley blowup: add a parse-effort cap with a clean error. Fragility: medium — measure
  first, the audit only bounded the exponent, not the site.

## E. Diagnostics surface (§2, §4.4)

One warning/advisory sink (line-numbered, module-attributed, suppressible — `-no-advise`/
`set show advisories`) threaded through lexer, parser, build, flatten, and runtime. Then the specific
classes the audit hit: preregularity, collapse-at-top, ambiguity (per C5), import hygiene (per C4),
statement drops/"discarding module", op-decl mismatches (per A1b), unbound-variable statements (per A1c),
"unusable module" tracking (which also fixes `upImports`-on-broken-module, §3.2). This phase is wide but
shallow; it converts a large fraction of the C++ suite's residual byte-diffs (Corner/ResolvedBugs) and
makes real Maude workflows legible. The warning *texts* should be byte-matched to the oracle where
fixtures assert them.

## F. Tool surface (§2)

Existing-Maude commands, in impact order:

- **F1. `set print` family** — actually wire the flags (`flat`, `with parentheses`, `number`, `rat`,
  `graph`, `conceal`, `attribute` incl. statement `[print …]` execution, `format` off, color). The
  renderer hooks exist (`print_pretty`); this is plumbing plus per-flag conformance fixtures.
- **F2. `show` family** — source-form module rendering (imports as imports, own decls with full
  attributes, `special (…)` hooks, correct module keyword, `endfm`) — fidelity ceiling depends on D1's
  tier; plus `show sorts/kinds/ops/vars/mbs/eqs/rls/strats/sds/summary/components/all/desugared`,
  `show modules`/`views` in Maude's format, `show path labels/states`.
- **F3. `parse` command; `search`/`continue` wording parity; timing display** (real cpu/real/rew-per-sec
  in the `rewrites:` line); **Ctrl-C interruptibility** (signal-checked safe points in reduce/rewrite/
  search — the audit's only way to survive runaway input interactively).
- **F4. Trace completeness** — trace inside `search` and rewrite-condition sub-searches (verified gap),
  `set trace select/exclude`, `break select` + the debugger loop (`debug`/`step`/`where`/`resume`/
  `abort`), profiling (`set profile`, `show profile`).
- **F5. The remaining REPL affordances** — `pwd`/`cd`/`ls`, `popd`-family, `eof`, `do clear memo`,
  `set clear …` semantics, `memo` attribute actually caching (with `set clear memo`).

## G. Remaining subsystems — new feature surface (last)

Ordered by (dependency, size); references are the kept deep-dives.

- **G1. Strategy-meta tail** (`upStratDecls`/`upSds`/`metaParseStrategy`/`metaPrettyPrintStrategy`,
  `metaSrewrite`). Prerequisites are structural, not incidental (§3.9.8): meta-constructor resolution by
  result sort, and preserving the un-desugared surface strategy form through resolution. Also fixes the
  §3.2 `upModule`-of-`smod` wrong result (SModule/strat-decl omission). Still open. Its former “do first”
  ordering was superseded by the newer `subsystems-goal.md` contract; it does not block T or M, but remains
  a prerequisite for faithful strategy reflection and should precede G7.
- **G2. Symbolic — complete (2026-07-21):** S0 (BDD/AllSat spike), S1 (order-sorted unification modulo
  free/S/CUI/AC/ACU/A/AU), S2 (folding variants and variant unification/matching), and S3 (v3
  variant-based narrowing, folding/filtering/history, paths/continuations, and all in-scope
  `metaNarrow*` surfaces). Durable gates: S1 is 27/27 fixtures and 676 byte-exact commands; S2 is
  21/21 and 289; the live S3 gate is 16/16 (15 completion fixtures plus one post-close regression),
  with all 169 primary commands passing independently. The implementation record and binding decisions
  are in `remaining-plans/03-narrowing.md`.
- **G3. SMT — next:** T0 bound D7 on `z3` 0.20.2; T0a must now seed/freeze the non-debug
  `smtTest` + manual fixture manifest before production code. T1–T5 deliver the 25 hooks, exact SMT
  number leaves, shipped `smt.maude`, `check`, root-only constraint-bearing `smt-search`, and mandatory
  `metaCheck`/`metaSmtSearch`. z3 is feature-gated; the default build remains pure Rust and
  parse/load/degrades the surface. T6 is independent of the solver core and uses completed G2: the
  official 2016 variant-satisfiability package is now checksum-pinned as an executable oracle, while
  production is a new native Rust constructor-variant/OS-compact decision procedure behind a thin
  `VAR-SAT-TOOL` Maude facade. No unlicensed prototype source is copied, and T6 does not wait on z3
  or model checking. Contract: `subsystems-goal.md` §2; implementation plan:
  `remaining-plans/04-smt.md`.
- **G4. Model checking — planned after G3 (independent, so parallel-safe):** M0 first seeds/freeze the
  reference/manual manifest. Then port the exact Gastin–Oddoux automata + nested DFS, refactor the
  conformance-verified rewrite successor core into a shared `StateGraph`, bind
  `SatSolverSymbol`/`ModelCheckerSymbol`, and finish byte-exact counterexample lassos plus
  `satSolve`/`tautCheck` prime implicants. Plan: `remaining-plans/05-model-checking.md`; reference:
  `reports/A8-symbolic-smt-ltl.md`.
- **G5. Meta-interpreters** (`metaInterpreter.maude`): separate `Engine` instances communicating by
  term translation, per **D1**. Reference: `reports/A7`.
- **G6. Prelude tail + IO stance.** The `LEXICAL` `printTokens`/`tokenize` hooks are implemented; remaining
  here is `LOOP-MODE` (`LoopSymbol`) so the prelude finally loads whole. External IO stays host-owned per
  revised **D5**: design the minimal embedding API when embedding is taken up; the shelved in-engine reactor
  plan lives in `objects-io-plan.md` §§2.5–2.9/4-C,D if that stance ever reverses.
- **G7. Full Maude** as a meta-level `.maude` library — gated on A5 + D1 + G1 (it metaprograms
  parameterized modules; the audit's meta-fidelity items are exactly its substrate).

**Milestone M-parity:** Maude 3.5.1 manual parity modulo the recorded accepted divergences; C++ suite
clean-pass limited only by deliberate drops (LaTeX/XML buffers, `FullCompiler`, dead narrowing
generations — the drop list in `01-architecture-map.md` §5 stands).

## Decision points to record in `03-open-decisions.md` when taken

- **D9 — ambiguity policy** (C5): reproduce MSCP's pick / warn-and-pick-ours / keep-error.
- **D10 — statement representation** (D1): PreModule + home-grammar parse vs compiled module algebra.
- **D11 — REPL identity** (C6): standing prelude + implicit imports + file commands by default, engine
  stays pure; flag surface.

## Risk register

1. **Import-order fix ↔ META `up*` suffix coupling** (A3b) — land together, add cross-module-overlap
   fixtures; green existing fixtures prove nothing here.
2. **Collapse one-shot termination** (B1) — the known hang/undercount knife-edge; instrument Maude first.
3. **AC enumeration order** (D2) — fixes downstream search/xmatch/strategy counts; port the Diophantine
   sequence exactly and keep the naive matcher as the live cross-check oracle.
4. **D1 full-rework blast radius** — every layer reads flattened modules; hence point-fix first, decision
   second.
5. **Ambiguity-policy faithfulness** (C5/D9) — MSCP's pick order may be impractical to reproduce; decide
   with evidence, not aspiration.
6. **BDD backend maturity — resolved for S0/S1.** The D6 spike selected `biodivine-lib-bdd`; the production
   `SortBdds`/AllSat path is covered by S1.
7. **Incompleteness propagation — resolved through S3.** AU produces the flag; unification, variants,
   narrowing object results, and the corresponding meta result constructors preserve it end to end.
8. **Fresh-variable families — resolved and centralized.** `tnk-core/src/fresh.rs` owns
   `#n`/`%n`/`@n`; variants and narrowing share it, including the byte-visible family alternation.
9. **Search/state-graph memory — resolved for S3.** Retained states own `RootGuard`s; descendant
   eviction and session/cache teardown release those roots under the existing arena-GC discipline.

## Conformance strategy (unchanged in spirit, upgraded in mechanism)

Every claim is validated against the C++ binary, never from memory — now continuously (phase 0's CI
harness), with the audit's severity taxonomy (CRASH / WRONG-RESULT / WRONG-COUNT / REJECT / EXTRA /
COSMETIC / DIAGNOSTIC) as the triage vocabulary and `fable-audit.md` as the ledger to update as items
close. Seed new fixtures from the audit's minimal repros, the C++ `tests/` suite, and the manual's worked
examples.
