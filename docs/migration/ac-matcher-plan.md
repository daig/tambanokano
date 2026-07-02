# AC/ACU matcher rework — implementation plan

A self-contained plan for a **dedicated implementation session**: port Maude's optimized AC/ACU matcher
(bipartite graph + Diophantine system, Eker 2002) alongside the current naive backtracking matcher, then
migrate onto it. Written after a C++ investigation (this doc cites both codebases by `file:line`) so the
implementation session can start cold.

Reference sources: C++ at `~/code/maude-lang/Maude/src/{ACU_Theory,AU_Theory,Utility}`; binary oracle at
`~/Downloads/Maude-3/maude`. Architecture backgrounder: `reports/A2-theories-matching.md`. Manual: §4.4.1
(theories), §4.8 (flattening/extension), §20.3.6–20.3.7 (collapse).

---

## 0. Honest scope (read first)

The current naive matcher **already conforms on reduce — values AND rewrite counts** (verified: `a;a;a;a`
under `eq X;X=X` = 3 rewrites = Maude; the whole prelude + 315 tests pass). So this is **not** a "fix the
broken matcher" job. Porting the Diophantine matcher buys, in decreasing certainty of payoff:

1. **Throughput / feasibility for heavy AC `search`** — the real reason to port. The naive matcher is
   exponential in the multiset split; Maude's is optimized. *No current fixture hangs*, so this payoff is
   forward-looking — there is no live failing case yet.
2. **`xmatch`-with-extension solution-set fidelity** — the naive matcher over-enumerates residue splits
   (a wrong solution *set* for the `xmatch` command; reduce/search unaffected). This the port fixes.
3. **Collapse-under-identity count** (a *live* divergence — see §3.2) — but this is **separable** and does
   **not** require the Diophantine port; it is a collapse-completeness fix in the current matcher.
4. **Multi-operand number-fold count** (a *live* divergence — see §3.3) — a **representation** issue, only
   loosely coupled to the matcher.

The decision (2026-07-01) was to do the **full port** regardless. This plan therefore covers the whole
port, but flags where the cheaper separable fixes (3, 4) could be lifted out if scope needs to shrink.

**Guiding discipline — differential cross-check.** Build the new matcher *beside* the naive one; keep the
naive one as a runtime oracle. For every reduce, both matchers must yield the same result/count; the naive
matcher's conformance is the regression backstop. Only retire it (or demote to a debug cross-check) once the
new path is byte-conformant on the whole suite + differential fuzzing.

---

## 1. Current tnk implementation (what we're replacing)

Theory kernel: `crates/tnk-core/`. Enum-dispatched theories `Theory { Free, Acu, Au, Cui, S, Na }`.

- **AC representation — flat multiset.** `dag.rs:51-59` — `NodeTerm::Acu { symbol, args: Vec<(DagId, u32)> }`
  = `(element, multiplicity)` pairs. Canonical form: equal elements merged, identity dropped, nested same-symbol
  flattened, sorted by `dag_compare` (arity-first — Maude's `orderInt`), invariant ≥2 total args. **Flattening
  is eager + total** (`acu.rs:81-110`, stack splice `Term::Op{ s==symbol } => stack.extend(args)`): no surface
  nesting survives — this is the root of the number-fold count divergence (§3.3).
- **Naive matcher.** `acu.rs`:
  - `AcuLhs::compile` (`:81`) partitions the flat pattern into **grounds** (structurally-equal consumption),
    **aliens** (non-ground non-variable, each with its own sub-automaton), and **variables** (by index + a
    Diophantine coefficient = multiplicity).
  - `AcuLhs::match_` (`:120-195`) → `Option<AcuSubproblem>` (resumable). First phase (immutable): ground
    consumption + residue extraction. Collapse-subject handling at `:127-138` (non-ACU subject → singleton
    `(subject,1)` with `ext=false`; identity constant → empty multiset).
  - `AcuSubproblem::next` (`:402`) drives enumeration. No-alien path pre-computes candidates via
    `enumerate_distributions` (`:229-280`) — **minimal-matched-size-first**, **skip the all-identity/size-0
    no-op** (`out.sort_by_key(|c| c.matched)`). Alien path (`:491-562`, `rec_alien`) lazy greedy-first.
    Non-linear vars deep-equal-checked against prior bindings.
  - `build_result` / `residue` (`:655-667`) splice the RHS with the leftover multiset (extension).
- **AU / CUI / S.** `au.rs` (ordered sequence + collapse at `:94-108`), `cui.rs` (**collapse unimplemented**,
  `:56-60` `_ => return None`), `s.rs` (iter successors).
- **Drive seams.** Reduce: `engine.rs:2185-2198` (two passes — equations `ext=false`, then rules `ext=true`).
  Universal enumeration envelope: `engine.rs:2275-2281` `while sp.next(...) { … }` (theory-agnostic).
  match/xmatch command: `engine.rs:3880-3945` (`extension` bool). search: `search.rs:154-268`.

**Divergence origins (file:line):**
| Divergence | Origin | Effect |
|---|---|---|
| Number-fold count | `builtin.rs:348-389` `reduce_acu_number_op` folds *all* numeric operands of the flat node in one rewrite | `2+3+4` = 1 rw, Maude 2 (value always right) |
| Collapse-under-identity count | `acu.rs:229-280` — an empty multiset gives a mult>1 var no element to bind; the all-identity solution is skipped | one-low per collapsed identity |
| xmatch extension over-enum | `acu.rs` residue enumeration (all valid splits) + AU | wrong `xmatch` solution *set* |
| CUI collapse | `cui.rs:56-60` `_ => None` | unexercised today |

---

## 2. Reference algorithm (Maude, `file:line`)

Theory plug-in pattern over virtual bases (`Interface/`): `LhsAutomaton::match()` → bool + optional residual
`Subproblem*`; `Subproblem::solve(findFirst, ctx)` lazily enumerates the rest on backtracking;
`ExtensionInfo` records the matched portion. **Two-phase**: cheap deterministic `match()` does forced work
and returns a residual `Subproblem` whose `solve()` does the multi-solution search. Patterns compiled once
(`Term::compileLhs` → per-theory automaton).

### 2.1 ACU match strategy — `ACU_LhsAutomaton.hh:36-75`, `ACU_Matcher.cc`
`enum MatchStrategy { GROUND_OUT, LONE_VARIABLE, ALIENS_ONLY, GREEDY, FULL }`. The FULL path
(`ACU_Matcher.cc:307-413` `fullMatch`):
1. **Eliminate forced work** (`:342-346`): `multiplicityChecks`, `eliminateGroundAliens` (binary search,
   `:70`), `eliminateBoundVariables` (`:78-103`), `eliminateGroundedOutAliens` (`:106-141`).
2. **Special no-extension cases** (`:348-382`): all aliens exhausted → `ALIENS_ONLY` or a forced lone var.
3. **Extension upper bound** (`:388-390`): if extending, cap so ≥2 real subterms are matched (not all in ext).
4. **Greedy attempt** (`:392-408`, `ACU_GreedyMatcher.cc`): return on definite success/failure.
5. **FULL fallback** (`:412`): `buildBipartiteGraph`.

### 2.2 Bipartite graph + Diophantine system — `ACU_Subproblem.{hh,cc}`, `ACU_Matcher.cc:579-676`
`buildBipartiteGraph` (`ACU_Matcher.cc:579-676`): for each non-ground alien, add a **pattern node**; add an
**edge** to each subject arg it can match (`currentMultiplicity[j] >= m && alien->match(...)`), carrying the
local binding + sub-subproblem. Zero edges → fail; unique edge → force it (eliminate, decrement multiplicity).
The residual **variable** multiplicities become a **Diophantine system** (`extractDiophantineSystem`,
`ACU_Subproblem.cc:400-518`): one **row** per unbound top variable (`insertRow(coeff=multiplicity, minSize,
maxSize)`), one **column** per subject arg with remaining multiplicity (`insertColumn(afterMultiplicity[i])`);
an extra row `insertRow(1, 0, extUpperBound)` for the extension variable when extending.

`solve` (`ACU_Subproblem.cc:140-153`) — the **enumeration order** that fixes conformance:
```
bool solve(findFirst, sol) {
  if (!findFirst && solveVariables(false, sol)) return true;  // next Diophantine sol for current patterns
  for (;;) {
    if (!solvePatterns(findFirst, sol)) return false;         // next pattern-edge assignment (backtrack)
    if (solveVariables(true, sol)) return true;               // first Diophantine sol for it
    findFirst = false;
  }
}
```
i.e. **patterns outer, Diophantine inner**: all Diophantine solutions for pattern-assignment 0, then backtrack
to pattern-assignment 1, etc. `solvePatterns` (`:156-177`) tries edges in the order added (left-to-right
subject args). `fillOutExtensionInfo` (`:562-582`) after a variable solution: the extension row's per-column
multiplicities become the residue (`setUnmatched(subjectMap[i], t)`); all-zero ⇒ `setMatchedWhole(true)`.

### 2.3 The Diophantine solver — `Utility/diophantineSystem.{hh,cc}` (Eker 2002, JAR 28(1))
Solve `R * M = C`: `R` = n-vector of positive variable coefficients, `C` = m-vector of positive subject
values, find the n×m natural-number matrix `M` with `R*M = C` (`M[i,j]` = multiplicity of subject `j` given
to variable `i`). AC wants every row sum non-zero (all but one — the extension row — may be zero). Rows carry
`(coeff, minSize, maxSize)` bounds on the row sum (`diophantineSystem.hh:96-99`).

- **API**: `insertRow(coeff,minSize,maxSize)`, `insertColumn(value)`, `solve()` (first + successive),
  `solution(row,col)` (`:98-101`).
- **Approach** (`.hh:64-80`): sort `R` **descending**; solve one row at a time, backtracking. Per row treat
  `C` as a multiset, compute the usable sub-multiset, try selections **smallest first**.
- **Simple vs complex** (`.hh:70-80`): **simple** iff some `R_i = 1` with `maxSize ≥` the largest column
  value ⇒ any natural number is a linear combination of any final segment of the sorted `R` ⇒ no dead-end
  from the tail. Otherwise **complex** ⇒ maintain a **solubility vector** (`struct Soluble{min,max}`,
  `.hh:119-123`; `buildSolubilityVectors`) to prune partial solutions early.
- **Per-row selection**: `Row::multisetSelect` (simple) / `Row::multisetComplex` (complex)
  (`.hh:132-135`). `Select{base, extra, maxExtra}` (`.hh:104-109`) is the per-column state; solution =
  `base + extra` (`.hh:180-181`).
- **The enumeration order is load-bearing**: it fixes the AC solution order, which fixes downstream
  `search`/`xmatch` counts. This must be ported *exactly* (rows descending by coeff; per row, sizes ascending
  and within a size selections by increasing column index; last row takes the remainder). **Port
  `diophantineSystem.cc` close to line-for-line** and unit-test the emitted solution sequence.

### 2.4 Collapse matching — `ACU_CollapseMatcher.cc` (READ IN FULL; the subtle, count-critical part)
Applies when the ACU top symbol collapses (`id:`/`idem`): a pattern can match a subject **not built with the
op** (manual §20.3.6/7). `collapseMatch` (`:234`) dispatches:
- **`uniqueCollapseMatch`** (`:27-75`): exactly one subterm can't take identity ⇒ collapse to it; every other
  top variable must be bound-to / bindable-to identity; then match the unique subterm's automaton. **1 sol.**
- **`multiwayCollapseMatch`** (`:92-232`): classify top vars — bound-to-non-identity (`matchingVariable`, at
  most one, mult 1), unbound+mult-1 (`viable`), unbound+mult>1 (bind to identity, `:125`). Then:
  - one `matchingVariable` ⇒ it matches the subject, others → identity (`:128-143`).
  - **`identity->equal(subject)`** (`:148-161`) ⇒ **succeed**: bind all to identity, `setMatchedWhole(true)`.
    ← **this is the branch tnk skips** (§3.2).
  - `nrViableVariables==0` && subject≠identity (`:162-179`) ⇒ succeed only with extension (subject *contains*
    identity): match an identity-bound var against subject with extension.
  - `nrViableVariables==1` (`:180-196`) ⇒ the lone viable var matches the subject.
  - **general (>1 viable)** (`:197-231`) ⇒ **disjunction**: for each unbound var, copy solution, bind the
    others to identity, match this var vs subject; first option unconstrained, later options add
    `EqualitySubproblem(identity, tv.index, false)` (var ≠ identity) to dedupe. **One sol per viable var**,
    in var-index order.

### 2.5 Extension / residue — `ACU_ExtensionInfo.{hh,cc}`
Residue = the unmatched sub-multiset (`Vector<int> unmatchedMultiplicity` per subject arg, `.hh:54-122`).
`fillOutExtensionInfo` writes it from the Diophantine extension row (`ACU_Subproblem.cc:562-582`). This is the
faithful model that avoids the naive matcher's residue over-enumeration.

### 2.6 AU (assoc, non-comm) — `AU_Theory/`
Subject is an **ordered sequence**, not a multiset. `AU_LhsAutomaton` (`.hh:105-300`): a **rigid** part
(fixed-order endpoints/ground-aliens/bound-vars) + a **flex** part (ordered vars/aliens that shift within
bounds), grouped into **rigid blocks** once vars bind. Match rigid ends first, determine blocks, enumerate
position shifts **leftmost-first**, recurse into flex vars. Extension via `AU_ExtensionInfo`. Port parity here
only if AU `search`/`xmatch` needs it (the current AU matcher conforms on reduce).

---

## 3. Conformance-critical behaviors + captured targets

Verification oracle: `~/Downloads/Maude-3/maude -no-banner <f> </dev/null` vs `./target/debug/tnk-repl <f>`.
tnk needs the prelude prepended for `NAT`/`META-LEVEL` (see the `prelude.pre` = first 3168 lines of
`conformance/prelude-meta.maude` trick used elsewhere this project).

### 3.1 Diophantine enumeration order (drives solution order → search/xmatch counts)
No single fixture; validate by unit tests on `DiophantineSystem` (hand-derive small cases + diff the emitted
sequence against instrumented Maude) and by the `search`/`xmatch`/`strategy` suites end-to-end.

### 3.2 Collapse-under-identity count — **LIVE**, captured
`conformance/instantiation-list-and-set.maude` (has `eq (S ; S) = S`, `id: empty`):

| reduce | Maude | tnk (now) |
|---|---|---|
| `makeSet(nil)` | 2 | 1 |
| `makeSet(0 (s(0) nil))` | 4 | 3 |
| `makeSet(0 (s(0) (0 nil)))` | 6 | 5 |

Minimal reproducer (no params) + the **termination fact** (critical): with
`op _;_ : St St -> St [assoc comm id: e]`, `eq (S ; S) = S`, `eq f = e`:
- `red e .` → **1 rewrite** (`(S;S)=S` collapse-matches `e`, `S=e`, fires `e→e` **once**, then stops).
- `red f .` → **2 rewrites** (`f=e`, then the collapse on `e`).

So the collapse rewrite is **one-shot** — it fires once on an identity subject and terminates, even though
`e→e` is a no-op. (Maude *does* loop on `eq a=a` for a free constant — so the one-shot behavior is specific to
the collapse path.) **Reproducing this exactly is a hard requirement**: skipping it is today's undercount;
naively "apply until fixpoint" would hang. The mechanism (Maude's reduced-flag / redex bookkeeping around
`ACU_Symbol::eqRewrite` + the collapse result being the already-reduced identity ctor) is a **study item for
the implementation session** — instrument Maude and match it. Maude also emits a **warning** on such patterns
(*"collapse at top of … may cause it to match more than you expect"*) — our diagnostics sink is currently
silent (a follow-on, `fable-audit.md`).

### 3.3 Multi-operand number-fold count — **LIVE**, captured
`red 2 + 3 + 4 .` → Maude **2**, tnk **1** (value 9 both). `red 2 + 3 + 4 + 5 .` → Maude **3**, tnk **1**.
Root: eager flatten (`+(2,3,4)`) + all-at-once builtin fold (`builtin.rs:348-389`). Maude keeps the surface
parse nested (`2+(3+4)`) and folds pairwise = k−1. **Note the trap** (`fable-audit.md`): a *prefix* N-ary AC fold
(e.g. `gcd(a,b,c)`) folds to **1** in *both* — so a flat node cannot be folded pairwise unconditionally; the
faithful count needs the **surface-preserving representation** (know how many binary nodes the surface had).
`user`-equation AC reduction is already correct (`a;a;a;a` = 3 both), so only the builtin fold is affected.

### 3.4 xmatch extension over-enumeration
`fable-audit.md §2`: `xmatch` with extension over a multi-element AU subject reports residue splits Maude doesn't.
Build fixtures from the manual's `xmatch` examples (§4.8 gives a 12-solution case) — pin the exact solution
*set*.

---

## 4. Proposed Rust layout (adapt `reports/A2` §5, fit current `tnk-core`)

Keep enum-dispatch (closed theory set). Add under `crates/tnk-core/src/`:
```
diophantine.rs        DiophantineSystem: insert_row/insert_col/solve()/solution(); Row{multiset_select,
                      multiset_complex}; simple/complex + solubility vectors. Standalone, unit-tested.
acu/ (or grow acu.rs) subproblem.rs   bipartite graph + Diophantine driver (solve = patterns⊗variables)
                      strategy.rs      MatchStrategy selection + eliminate/greedy fast paths
                      collapse.rs      unique_collapse_match / multiway_collapse_match (+ identity case)
                      extension.rs     residue model (replaces build_result's naive residue)
```
Reuse the existing `theory::LhsAutomaton` / `Subproblem` seam and the `sp.next()` envelope
(`engine.rs:2275`). Model `solve(find_first)` as a resumable iterator / explicit state enum (not the C++
`findFirst` bool) per A2 §3. Substitution sharing (A2 §4 risk) → arena indices + `pub(crate)` fields or a
`LocalBinding`-style owned diff, not `&mut` threading through subproblem trees.

---

## 5. Phasing (each phase independently verifiable; suite stays green throughout)

**Phase 0 — cross-check harness.** Add a debug mode (env var / cfg) that, on every ACU match during reduce,
runs BOTH the naive and new matchers and asserts identical solution streams (order + bindings). This makes the
naive matcher a live oracle and catches enumeration-order drift immediately. Also add a small differential
fuzzer (random AC patterns/subjects) comparing counts vs Maude.

**Phase 1 — `DiophantineSystem` (standalone).** Port `diophantineSystem.cc` faithfully. Unit-test the emitted
solution *sequence* on hand-derived cases and against instrumented Maude. No engine dependency — pure integer
solver. **This is the foundation; get the enumeration order exact here.**

**Phase 2 — `ACU_Subproblem` (bipartite + driver).** Build the bipartite graph over the pattern's aliens
(reusing the engine's alien sub-matching), extract the Diophantine system, wire `solve = patterns⊗variables`.
Cross-check vs naive on the reduce path (Phase 0 harness) — same results/counts on the whole suite.

**Phase 3 — strategy selection + fast paths.** `MatchStrategy` (GROUND_OUT/LONE_VARIABLE/ALIENS_ONLY/GREEDY)
+ the eliminate-forced-work prologue + FULL fallback. Purely a throughput layer over Phase 2 — must not change
results (Phase 0 harness guards this).

**Phase 4 — collapse matching.** `unique_collapse_match` + `multiway_collapse_match`, including the
`identity == subject` branch (§3.2) and the one-shot termination. Verify `instantiation-list-and-set` and the
minimal reproducer hit Maude's counts exactly (2/4/6, `red e`=1, `red f`=2). **Highest-risk phase** — heavy
differential testing; watch for loops. (This phase alone closes the live collapse count gap and could be
lifted out early if desired.)

**Phase 5 — extension / residue.** Replace the naive residue with the Diophantine extension-row model; verify
`xmatch`-with-extension solution *sets* against the manual's examples. Fixes §3.4.

**Phase 6 — number-fold representation.** The surface-preserving AC representation so the builtin fold counts
k−1 for infix but 1 for prefix N-ary (§3.3). Assess whether to preserve surface nesting only for the builtin
fold path or generally. Lowest ROI — do last or defer (count-only, unexercised by fixtures).

**Phase 7 — AU parity + CUI collapse.** Port AU rigid/flex if AU `search`/`xmatch` needs it; wire CUI collapse
(`cui.rs:56-60`) if any comm-with-identity op appears. Both currently unexercised.

**Phase 8 — retire the naive matcher** (or keep behind the Phase-0 debug cross-check). Full suite + Maude
differential must be byte-conformant. Update `fable-audit.md` (§3.2 collapse values, §3.3 counts/xmatch
enumeration, §3.5 AC-matching hang, §3.9 items 3–4).

---

## 6. Risks (from `reports/A2` §4 + this investigation)

1. **Enumeration-order fidelity** — the Diophantine + patterns⊗variables order fixes downstream
   `search`/`xmatch`/`strategy` counts. A subtle drift silently breaks counts the naive matcher gets right.
   Mitigate: Phase-0 cross-check + unit-test the Diophantine sequence.
2. **Collapse termination (§3.2)** — must fire once and stop (loop risk). Study Maude's reduced-flag
   mechanism; test the minimal reproducer.
3. **Borrow checker vs. shared-mutable substitution** — `solve()` mutates a shared substitution while
   subproblems hold references. Use arena indices / owned diffs, not `&mut` threading (A2 §4).
4. **Number-fold representation entanglement** (§3.3) — can't fold a flat node pairwise unconditionally.
5. **Regression on 315 passing tests** — the whole prelude + META + strategy + objects lean on AC matching.
   The Phase-0 oracle + running the full suite each phase is the backstop.
6. **Scope creep** — the full port is large and its headline payoff (throughput) has no live failing case.
   Phases 4/5 (collapse, xmatch) carry the real correctness wins; if scope must shrink, land those on the
   *existing* matcher and defer the Diophantine core.

---

## 7. Open questions for the implementation session

- Maude's exact one-shot/termination mechanism for the collapse no-op (§3.2) — instrument `ACU_Symbol::eqRewrite`.
- Whether to preserve surface nesting generally or only for the builtin number fold (§3.3, §6 Phase 6).
- Tree representation (`ACU_TreeDagNode`, `CONVERT_THRESHOLD=8`): needed for parity, or does the flat
  `Vec<(DagId,u32)>` suffice at our scales? (Defer unless a large-AC case demands it.)
- Diophantine "simple vs complex" — port both paths, or start simple-only and add complex solubility later?
- Retire the naive matcher (Phase 8) or keep it permanently as a `debug_assert` cross-check?

---

## 8. Quick-start for the implementation session

1. Re-read this doc + `reports/A2-theories-matching.md`.
2. Read firsthand: `Utility/diophantineSystem.{hh,cc}`, `ACU_Theory/{ACU_Subproblem,ACU_Matcher,
   ACU_CollapseMatcher,ACU_ExtensionInfo}.{cc,hh}`, `ACU_LhsAutomaton.hh`.
3. Read tnk: `crates/tnk-core/src/{acu.rs,dag.rs,builtin.rs:348-389,engine.rs:2185-2286}`.
4. Build the Phase-0 cross-check harness *first* — it is the safety net for everything after.
5. Phase 1 (Diophantine) → unit tests → Phase 2 …, running the full suite + Maude differential each phase.

Captured verification targets (this session): §3.2 (collapse 2/4/6; `red e`=1, `red f`=2), §3.3 (`2+3+4`=2,
`2+3+4+5`=3), and the invariant that user-equation AC reduction already conforms (`a;a;a;a`=3).
