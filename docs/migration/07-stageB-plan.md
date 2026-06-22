# Phase 1 Stage B — plan & the as-built foundation it builds on

**Read this first when starting Stage B** (the breadth work — the real functional engine). Stage A (the
foundation reshape, review Tier 2) is **complete and adversarially reviewed**; this doc records the
*seams it produced* — the internal API Stage B plugs into — and the ordered **B1–B5** agenda. It
supersedes `06-phase1-plan.md` §3–§4 for the breadth work (`06` remains the Phase-1 overview; its §3
Stage A is now done).

> **STATUS (2026-06-21) — STAGE B2 COMPLETE. NEXT: B3.** B1 (structural theories) and B2 (the
> order-sorted / membership / conditional / attribute layer) are both **done on `main`**, every lock
> conformance-verified vs the reference binary (**79 tests**, clippy `-D warnings` clean, `fib(22) =
> 186579` and ~7.5 M rw/s intact throughout). §1 (as-built seams) and §2 B1/B2 below are refreshed to the
> as-built state; §2 B3–B5 are the **unchanged forward plan** (the seams they plug into did not move).
> Commit trail `23d6fd4..7d09469` (F-A guard + B2.1…B2.4). **Audit findings:** F-3/F-4 closed in B1; F-A
> (below) closed by a loud guard; **F-1** (no-op rewrite guard) still genuinely unimplemented — moot for
> the locked theories, revisit if a self-rewriting `eq a = a` becomes reachable; **F-2** (nested-reduce GC
> root set) is now **mitigated** (GC disabled during condition eval, B2.3) but **not fully closed** — the
> engine-global active-frame root set is still required before release-mode safe-point GC runs with
> conditions (§4).
>
> **History — post-B1 audit (2026-06-20):** re-ran every `conformance/*.maude` lock against the binary
> (all TRUE) and read the full kernel; found one *new* gap — **F-A**: a theory-rooted (ACU/AU/CUI)
> subterm under a *free* operator (or a theory ground subterm under a theory op) *silently* failed to
> match, leaving its equation quietly dead — the asymmetric twin of the loud alien-under-AC assert.
> **Closed with a loud guard** (`Term::is_free_matchable`, enforced in `LhsAutomaton::compile` + the
> ACU/AU/CUI compilers); the cross-theory `Sequence` composition itself stays deferred (§2 B1). The
> Stage-A audit verdict was GO (F-3 ExtensionInfo / F-4 `Subst` unbind closed in B1; S and NA deferred to
> B3 — they need bignums / built-in data).

---

## 0. Re-acquire context (start of the Stage B session)

**Reference trees (outside this repo) — unchanged from `06` §0:**
- C++ ground truth: `/Users/dai/code/maude-lang/Maude/src`
- Maude 3.1 manual: `/Users/dai/Downloads/Maude-3/book/extracted_manual/manual.md`
- Reference `maude` binary for conformance: `~/Downloads/Maude-3/maude -no-banner <file>.maude < /dev/null`
- Prelude (the .maude library to port/conform against): `/Users/dai/Downloads/Maude-3/prelude.maude`

**Docs read order:** `01-architecture-map.md` (esp. layers **L1/L2/L3/L5/L6** and cross-cutting
decisions #2/#3/#4/#5/#6/#7) → `02-migration-plan.md` §2 (phases) + §3 (PORT/RETHINK/DROP) →
**this doc** → then the per-milestone deep-dive *as each B item starts*: `reports/A2` (B1 theories/
matching), `A3` (B2 sorts/membership/attrs), `A7` (B3 built-in data — §1/§2 *BuiltIn seam* part only;
the meta half is Phase 3), `A4` (B4 parser), `A5` (B5 modules+REPL — *non-parameterized* part only;
parameterization is Phase 2). Decisions: `03-open-decisions.md` (D1–D8; **D2 resolved** = 4-byte
release handle; D4 `malachite`).

**The code:** `crates/tnk-core` (Stage A + B1 theories + B2 sorts/memberships/conditions/attrs as-built).
Sanity check before starting:
- `cargo test -p tnk-core` → **79 pass** (post-B2); `cargo clippy --all-targets -- -D warnings` → clean.
- `cargo run --release --example peano` → `fib(20)` ≈ **7.5 M rewrites/s** (free theory; B2's sort path is
  fast-pathed for single-declaration ops so the free hot path is unregressed), GC mark ≈ 270–350 M nodes/s.
- `cargo run --release --example peano 22 1 100` → `fib(22) = 17711 (186579 rewrites)` == reference.
- Conformance: `conformance/{acu-match,acu-reduce,au,cui}.maude` (B1) + `{overload,membership,conditional,
  owise,cmb,match-cond,strat}.maude` (B2) == reference binary.

**The memory:** `maude-rust-migration.md` (status, the Stage-A commit map, this agenda in brief).

---

## 1. Stage A as-built — the seams Stage B plugs into

**Do not re-derive these; build on them.** Stage A reshaped the kernel *precisely so that the theories,
conditions, built-ins, and parser are additive*. The internal API:

### 1.1 Engine = `Signature` (immutable during reduction) + `Runtime` (mutable) — A4 (`6e1b8da`)
`engine.rs`: `pub struct Engine { sig: Signature, rt: Runtime }` is a thin facade re-exposing the
public API. Internals:
- `Signature { sorts: Sorts, symbols: Arena<Symbol>, equations: HashMap<SymbolId, Vec<CompiledEquation>>, eq_epoch: u32 }`
- `Runtime { dags: Arena<DagNode>, rewrite_count, roots, gc_interval, allocs_since_gc }`
- The reduction/matching methods are `impl Runtime` taking `&Signature` (`reduce`, `try_rewrite_top`,
  `make_free`, `compute_free_sort`, `match_pattern`, `instantiate`); `deep_equal` is runtime-only.

**Why B needs it:** a rewrite holds `&sig.equations` (the matched `&eq.rhs`) while `&mut`-borrowing the
runtime to build nodes — *no clone*. **This is the borrow home for B2's conditional equations**: the
condition is reduced via `&mut Runtime` while the equation table stays borrowed through `&Signature`.
AC residue-node construction (B1) gets `&mut Runtime` the same way.

### 1.2 Matcher seam: `LhsAutomaton` / `Subproblem` + solution-stream driver — A3 (`12d60c2`), extended in B1
`theory.rs` (crate-private, closed enums — decision D3). **As-built after B1:**
- `enum LhsAutomaton { Free(Term), Acu(AcuLhs), Au(AuLhs), Cui(CuiLhs) }`; `compile(lhs: Term, &Signature)`
  picks the arm from the top symbol's `theory()`. (Add `S`/`Na` arms at B3.)
- `match_(&self, &Runtime, &Signature, subject, &mut Subst, ext_allowed: bool) -> Option<Subproblem>` —
  two-phase: bind the forced/deterministic part, return a residual enumerator. **`ext_allowed`** enables
  matching a *sub-part* of the subject and leaving a residue (true for ACU/AU; the audit-**F-3**
  ExtensionInfo channel — false for free/CUI which always match the whole node).
- `enum Subproblem { FreeOnce{..}, Acu(..), Au(..), Cui(..) }`, with
  `next(&mut self, &mut Runtime, &Signature, &mut Subst) -> bool` (resumable; **`&mut Runtime`** so an
  arm can build binding/residue nodes between solutions — the F-4 widening, now done) and
  `build_result(&self, &mut Runtime, &Signature, rhs) -> DagId` (splice the rhs into the matched
  position — whole → `rhs`; ACU → `rhs ⊎ residue`; AU → ordered `prefix ++ rhs ++ suffix`; Maude's
  `partialConstruct`). `build_result` **replaced** the old `matched_whole()/residue()` reads in the driver.
- The driver `Runtime::try_rewrite_top`: `ext_allowed = theory ∈ {Acu, Au}`; for each eq,
  `match_` then `while sp.next(..) { return Some(sp.build_result(.., instantiate(&eq.rhs, ..))) }`
  (`#[allow(clippy::never_loop)]`: unconditional eqs return the first solution; B2 conditions will
  `continue` to the next on condition failure).

**Matcher strategy (B1, correctness-first — `src/{acu,au,cui}.rs`).** Own *complete* enumerators (own
Diophantine by backtracking), **not** Maude's optimized bipartite/Diophantine solver (a perf follow-up).
Two ordering rules reproduce the binary's behaviour, both *forced by the reference* (not assumed):
a **lone linear variable absorbs the whole remainder** (Maude's collector/LONE_VARIABLE — `eq a+X=b` on
`a+c+c` is `b`, not `b+c`; a *correctness* rule, since that system is non-confluent under extension), and
otherwise **minimal-matched-size first** with the **matched-size-0 identity no-op skipped** (so `X+X=X`
on `a+a+a+a` is 3 rewrites and identity bindings never loop). CUI canonicalizes/collapses at construction
(`f(a,a)`/`f(a,e)` → element) and enumerates the two commutative pairings.

**How B2 extends it:** the `while sp.next(..)` body becomes
`if condition_holds(sig, rt, subst) { accept } else { continue }` — backtrack into the next solution on
condition failure; `condition_holds` reduces fragments via `rt.reduce(sig, ..)` (the A4 borrow home).
**That nested `reduce` is the audit-F-2 hazard:** its safe-point GC must see the *outer* reduction's
roots + the matcher's in-flight `Subst`/residue, which the current *per-`reduce`-call local* root set
does not (§4 — fix before release-mode safe-point GC + conditions). The free-theory discrimination net
stays a later perf step behind this seam (it changes how `match_` finds candidate eqs, not the driver).

### 1.3 Child traversal visitor — A5 (`13219cf`)
`dag.rs`: `DagNode::children(&self) -> impl Iterator<Item = DagId>` and
`for_each_child(&self, impl FnMut(DagId))` replace the old `&[DagId]` slice. GC (`mark_reachable` via
`children().extend`), `reduce` (`new_reduce_frame` via `children().collect`), and `deep_equal` (via
`symbol()` + pairwise `children()`) are all theory-agnostic.

**Why B needs it / contract for B reps (B1 done; S/Na at B3).** A new `NodeTerm` arm implements
`children()`/`for_each_child` and is a *pure addition* — GC/reduce/equality untouched. B1 added
`Acu{(DagId,mult)}`, `Au{Vec<DagId>}`, `Cui{[x,y] canonical}`; `children()` is now a small `ChildIter`
enum (the ACU arm expands multiplicities, the rest reuse the slice iterator). **Contracts the reps honour:**
- For `deep_equal` — and `dag_compare`, the **new total order on nodes** consistent with it — to be
  correct, `children()` must yield the **full, canonically-ordered child sequence** (ACU: flattened
  multiset with repeats; AU: ordered sequence; CUI: sorted pair). `make_*` keep nodes canonical, so
  pairwise comparison *is* equality. **`dag_compare` is the key the ACU/CUI canonicalizers sort by.**
- A theory whose node carries **scalar payload that is not a child id** (the **S-theory's successor
  `count`** — B3) needs **theory-specific equality/compare**, not the generic `deep_equal`/`dag_compare`.
  (Documented on `deep_equal`.) Add the dispatch when S lands.

### 1.4 Arena safety: generational handles + RootGuard + safe-point GC — A2 (`f8b1c0d`)
`id.rs`/`arena.rs`/`root.rs`/`engine.rs`: debug-gated `(generation, arena_id)` on `Id` (bare `u32` in
release — **D2 resolved**); `RootGuard` (RAII, `Rc<RefCell<RootRegistry>>`, does not borrow the engine);
`gc(extra_roots)` always marks the registry; opt-in `set_gc_interval` runs GC at the reduce loop head
rooting `walk(stack) ∪ child_result ∪ registry`.

**Conformance discipline for B:** any `DagId` a caller holds across a later reduction/allocation — incl.
a prior reduction's result, or terms held by the (future) module DB / REPL / meta — **must be pinned
with `Engine::root`** if `gc_interval` is set. New theory reps are new `NodeTerm` arms the arena/GC
already trace via the visitor; nothing in A2 needs changing for B.

### 1.5 Iterative reducer — A1 (`7f8df37`)
`engine.rs`: `reduce` is an explicit `ReduceFrame` work-stack (no subject-depth native recursion);
`deep_equal` is a pair-stack. `match_pattern`/`instantiate` stay recursive (bounded by *pattern/rhs*
depth, author-controlled — superseded by B1's compiled automata for the hot path). B reductions inherit
this loop unchanged.

### 1.6 Placeholders Stage B replaces — B1/B2 status
| Placeholder (Stage A) | Replaced by | Status |
|---|---|---|
| `Engine::compute_free_sort` (sort = op `range`, else kind error sort) | **B2.1** least sort under overloading — `Signature::compute_sort` (`findMinSortIndex`: down-set GLB + earliest-decl tie-break) | **DONE** (the flattened sort-*diagram* decision table is a deferred perf step — correctness-first iteration for now) |
| `Symbol { name, domain, range }` — *one* declaration | **B2.1** `Symbol { decls: Vec<OpDeclaration{domain,range,ctor}>, …, strategy }` + `add_op_decl` | **DONE** (no "diagram handle" — the down-set method needs none) |
| `Equation { lhs, rhs, nr_vars }` (unconditional) | **B2.2/B2.3** memberships `mb`/`cmb`; conditional `ceq` + `owise`; **B2.4** op attributes (`ctor`/`strat`) | **DONE** (rewrite `=>` conditions → Phase 2; `frozen`/`memo` deferred) |
| `NodeTerm { Free, Acu, Au, Cui }` (B1 done) | **B3** adds `S`/`Na` arms + a built-in/number arm | B3 |
| no built-ins | **B3** `enum SpecialOp` bound from `special(id-hook …)`; `malachite` bignums | B3 |
| hand-built modules in tests | **B4** parser + **B5** module system load `.maude` text | B4/B5 |

---

## 2. The ordered agenda — B1 → B5

Each item: **goal · plugs into · what's new · done-when (conformance) · refs · risks.** Keep building
hand-constructed test modules (as Stage A did) for B1–B3; the parser (B4) is what makes the *end
milestone* "load `.maude` text" possible. Conformance is always against the reference binary.

### B1 — Equational theories  *(the largest single piece)* — **ACU / AU / CUI DONE; S / NA → B3**
- **Goal:** matching & rewriting **modulo** `assoc`/`comm`/`id:`/`idem`. ✅ for the structural theories.
- **Plugs into:** §1.2 matcher seam (`LhsAutomaton`/`Subproblem` arms, multi-solution `next`,
  `build_result`), §1.3 visitor (`NodeTerm` arms yielding canonical children), §1.1 `&mut Runtime` for
  residue nodes.
- **DONE (on `main`, `c10bf0e..e4ea879`):** **ACU** (`assoc comm [id:]`), **AU** (`assoc [id:]`, ordered),
  **CUI** (`comm [idem] [id:]`). `Symbol{axioms,identity}` + the `Theory` enum + `add_op_{ac,au,cui}`; flat
  reps `NodeTerm::{Acu(Vec<(DagId,u32)>), Au(Vec<DagId>), Cui([x,y])}` + `make_{acu,au,cui}`
  canonicalizers + the `dag_compare` total order; **correctness-first** own enumerators
  (`src/{acu,au,cui}.rs`) with the lone-variable-collector + minimal-first/skip-no-op strategy (§1.2).
  Every lock differentially verified vs the binary (`conformance/{acu-match,acu-reduce,au,cui}.maude`).
- **Deferred follow-ups (none block B2):** **S** (stacked-successor `iter` numbers — needs bignum) and
  **NA** (atomic built-in constants — needs built-in data) **→ B3**; the red-black `ACU_TreeDagNode`
  (flat `Vec` only — a perf step at `CONVERT_THRESHOLD`≈8); the **optimized bipartite + Diophantine**
  matcher + lazy subproblems (own backtracking enumerator for now); the persistent-structure crate
  (`rpds`/`im` — only the tree rep needs it); **cross-theory composition** (the `Sequence` arm — a
  theory subterm under a free op, a theory ground subterm under a theory op, or a non-ground/non-var
  alien under AC/AU): all **loud-guarded** now (`Term::is_free_matchable` + the alien `assert`), never
  silent (audit F-A). **Non-linear variables** *work* under **AC** (Diophantine coefficients — `X+X=X`
  reduces correctly) but are a **loud `assert`** under **AU**; CUI **collapse-matching** `f(X,Y) <=? a`; collapse on a
  single-element ACU subject; exact solution-**order** for non-confluent systems + bounded `match[n]`.
- **Done-when (met for ACU/AU/CUI):** matching/reduce modulo the axioms conforms to the binary — match
  solution-sets *and* reduce rewrite-counts (the suite was built from the manual's `xmatch`/`match`
  examples + captured reduce counts *before* any optimization).
- **Refs:** `A2` (the whole report); arch-map L2 + decision #3.
- **Risks (mostly retired):** AC collapse correctness, multi-solution completeness, lone-var/order
  fidelity — all locked by differential tests. Remaining: flat↔tree switch + persistent-structure/GC
  interplay (deferred); S/NA's bignum + built-in coupling (handled in B3).

### B2 — Order-sorted least sorts + memberships + conditional logic + operator attributes — **DONE**
- **Goal:** correct least sorts under overloading; conditional equations/memberships; op attributes. ✅
- **Plugs into:** §1.1 (`reduce` evaluates conditions while the eq table stays borrowed); §1.2 (the
  `while sp.next` condition-check + backtrack); replaced §1.6 `compute_free_sort`.
- **DONE (on `main`, `f83bf7d..7d09469`), per sub-step:**
  - **B2.1 overloading** (`f83bf7d`): `Symbol{decls: Vec<OpDeclaration>}` + `add_op_decl`;
    `Signature::compute_sort` = Maude's `findMinSortIndex` (the **minimum of applicable declarations'
    ranges via down-set intersection**, `Sorts::leqs` inverted from `geq` at `close()`, with the
    **earliest-declaration** tie-break for non-preregular ops); theory nodes fold the binary `compute_sort`
    over their element sorts. *Deviation from "sort decision diagram":* correctness-first **direct
    iteration**, not the flattened decision table (a perf follow-up); the `unique`/preregularity bit is
    computed but the user-facing **warning is deferred** (no diagnostics sink yet). Single-kind overloading
    only (cross-kind ad-hoc → arg-driven kind selection is a follow-up, `debug_assert`-guarded).
  - **B2.2 memberships `mb`** (`f43e158`): per-symbol `SortConstraint` table (smallest-target-sort first);
    `constrain_to_smaller_sort` lowers a node's least sort at construction to a fixpoint, **each
    application counted as a rewrite** (Maude accounting). Gated by `memberships.is_empty()` so the free
    hot path is untouched.
  - **B2.3 conditional logic** (`b90447d` ceq / `f36dfc5` owise / `3bfed04` cmb / `99d2bd8` `:=`):
    `CompiledEquation`/`SortConstraint` gain a condition; a recursive **backtracking `solve_condition`**
    (Maude `solveCondition`) over fragment kinds **equality / sort-test / matching `:=`** (the `:=` pattern
    compiles to an `LhsAutomaton`, binds fresh vars, backtracks); `owise` via a two-phase `try_equations`
    (non-owise first); `cmb` reuses the condition machinery. *Condition reductions are re-entrant and
    count* (`max(2,1)` = 5 rewrites — the failed first condition is re-reduced for the second equation).
    **Rewrite `=>` condition → Phase 2 (rules).**
  - **B2.4 attributes** (`7d09469`): **`ctor`** wired (`OpDeclaration.ctor` + `is_constructor`) — metadata,
    inert for functional reduce (verified). **`strat`** (evaluation strategy): the reduce frame was
    redesigned to `orig`+`args`+`cursor` querying `Signature::strat_position` per step — the **standard
    path is identical** (fib + all locks intact), a custom strat leaves unlisted args unreduced (lazy
    `if_then_else_fi`). **`frozen`** (blocks *rule* rewriting — inert for functional reduce) and **`memo`**
    (pure perf cache) are deferred; the general (non-`(args… 0)`) strategy form is loud-asserted.
- **Done-when (met):** overloaded/subsorted modules get the binary's `result <Sort>:`; conditional /
  `owise` / `cmb` / `:=` modules reduce with the binary's exact rewrite counts; `strat` is lazy per the
  manual. Locked by `conformance/{overload,membership,conditional,owise,cmb,match-cond,strat}.maude`.
- **Refs:** `A3` (whole report); arch-map L1 + decision #2/#3.
- **Carried-forward follow-ups (none block B3):** the flattened sort-diagram + preregularity *warning*;
  cross-kind ad-hoc overloading; `leq`/down-sets `BTreeSet` → `fixedbitset` (R3 M2 — B2 stayed `BTreeSet`);
  **F-2** the engine-global condition-reduce GC root set (mitigated, §4); `frozen`/`memo`; rewrite `=>`
  conditions (Phase 2); `special` (→ B3, with the built-in seam).

### B3 — Built-in data types + bignums  *(now also hosts the **S** and **NA** theories — deferred from B1)*
- **Goal:** `BOOL`, `NAT`, `INT`, `RAT`, `FLOAT`, `STRING`, `QID` working — **plus the S (`iter`
  successor) and NA (atomic constant) theories**, deferred from B1 because they need bignums / built-in
  data respectively.
- **Plugs into:** the §1.2 matcher seam + §1.3 visitor (new `NodeTerm::{S, Na}` arms — additive, exactly
  as ACU/AU/CUI were); the symbol-reduction path; **B2's attribute infrastructure** (`OpDeclaration` +
  `Symbol.strategy` + the condition machinery — `special`/`iter` parsing itself is B3's own work, deferred
  here with the built-in seam). The **lazy `strat` reduce frame from B2.4 is already the mechanism
  `if_then_else_fi` needs** — B3 adds only the BOOL built-in + the operator's `strat (…)` declaration.
- **What's new:**
  - **S theory** (`iter`): `NodeTerm::S { symbol, count, arg }` — `s^count(arg)` stored compactly with a
    **bignum** `count` (so `s^(10^9) 0` is O(1)); extension matching (`s^k` matches `s^n` for `k ≤ n`,
    residue `s^(n−k)`); **theory-specific equality/compare** (the scalar `count` is not a child id — the
    §1.3/§4 dispatch). Ties succ/`iter` to NAT.
  - **NA theory:** the trivial atomic case — a built-in constant matches only itself (numbers / strings /
    quoted-ids); per-type equality.
  - parse `special (id-hook …)` into a typed **`enum SpecialOp`** at module-build time (resolving op/term
    hooks to symbol ids) — decision #6; built-in reduction becomes an arm of symbol reduction (not a
    fn-pointer); arithmetic on **`malachite`** behind `tnk-core::num` (D4); the predefined numeric/string
    modules. `NumberOp`/`Equality`/`Branch`/string/float per `A7` §2.
- **Done-when:** the predefined numeric/string prelude modules reduce and conform (numeric results,
  rewrite counts, `if_then_else_fi`, equality); `s^n 0` / `iter` numerals and NA constants conform.
- **Refs:** `A7` §1/§2 (BuiltIn seam — *not* the meta half), `A2` (the S/NA theories), decision #6/#7
  (D4); arch-map L2 (S/NA) + L3 (built-ins).
- **Risks:** RAT/FLOAT edge cases; conformance of conversions; the **S-theory equality dispatch** (§1.3)
  + its bignum `count`; tying succ/`iter` to NAT.

### B4 — Frontend: lexer + mixfix parser + pretty-printer
- **Goal:** parse `.maude` *functional* modules to the same terms the hand-built fixtures produce; round-trip via pretty-print.
- **Plugs into:** B2 sorts/components feed grammar build; `build_term` returns kernel arena terms
  (§1.1/§1.5); B5 consumes the parsed `PreModule`.
- **What's new:** hand-written (or `logos`) lexer incl. tokens/**bubbles** (replace the flex/bison global
  handshake with an explicit API — decision #4); recursive-descent/Pratt **surface** parser; the
  user-extensible **per-module mixfix grammar** built from the signature (prec/gather/format, OBJ3
  defaults); the **Earley + Leo (DRP)** CF parser (port the algorithm; no crate does prec/gather/Leo);
  the pretty-printer (the inverse). New crate `tnk-frontend` (per `02` §1).
- **Done-when:** a `.maude` functional module parses to the same terms as the fixtures; pretty-print
  round-trips; **differential-test the parser on the whole prelude before trusting it**.
- **Refs:** `A4` (whole report); arch-map L5 + decision #4.
- **Risks (high):** Leo DRP + prec/gather interaction (trickiest, least-documented C++); **ambiguity
  *ordering* is observable** (Maude takes the first of two parses — preserve forest-extraction order);
  bubble boundaries need grammar context (clean API without globals is the key design call).

### B5 — Module system (non-parameterized) + REPL  *(the Phase-1 end milestone)*
- **Goal:** load real functional prelude modules from text and `reduce`/`match` them.
- **Plugs into:** B4 (parsed `PreModule`), B1–B3 (the engine they flatten into), §1.4 (root module-DB
  terms if safe-point GC is on).
- **What's new:** module database; `protecting`/`extending`/`including` import + **flatten** (as a *pure
  function* producing fresh arena terms — decision #5, not C++ "donation"); summation `+`; renaming
  `*(...)`; a REPL (`rustyline`) with `reduce`/`red`/`match`/`trace`/`show` + `set` options.
  **Parameterized programming (theories/views/parameterized modules) is Phase 2 — keep B5 to
  non-parameterized modules.** New crates `tnk-modules`, `tnk-repl`.
- **Done-when (the milestone):** load the non-parameterized functional prelude fragments from `.maude`
  text and `reduce`/`match`, differential-tested vs the binary — *same canonical forms and rewrite
  counts*. "Write Maude, get answers."
- **Refs:** `A5` (the module half — skip §parameterization for now); arch-map L6 + decision #5.
- **Risks:** flatten/cache coherence (`Rc` + dirty-set vs rebuild); term ownership across modules
  (deep-copy vs shared arena — coordinate with the kernel arena).

---

## 3. Conformance discipline (carry the Phase-0/Stage-A habit forward)
Every "port" is validated against the reference binary, not from memory. Grow `conformance/` (has
`peano.maude`, `fib.maude`) from: the prelude (`/Users/dai/Downloads/Maude-3/prelude.maude`), the
manual's worked examples (esp. **`xmatch`/`match` for B1**, `sort`/`parse` for B2), and
`/Users/dai/code/maude-lang/Maude/tests`. Diff canonical forms **and** rewrite counts. Until the parser
(B4) lands, keep using hand-built modules in Rust tests + the reference binary on the equivalent
`.maude`, as Stage A did (e.g. the `fib(22) = 186579` lock).

## 4. Open decisions / risks specific to Stage B
- **[AUDIT F-2 — MITIGATED in B2.3; full fix still owed before release safe-point GC + conditions]
  Nested-reduce GC root set.** `safe_point_gc` marks only the *current* `reduce` call's frame stack
  (`original` + `args`) + `child_result` + registry. B2.3 evaluates conditions by calling `reduce` *inside*
  the `while sp.next` loop; that nested reduce's safe points can't see the OUTER reduction's frames /
  matcher `Subst` / residue. **Mitigation in place (`b90447d`):** safe-point GC is **disabled during
  condition evaluation** (`condition_holds` saves/clears `gc_interval`), so nothing collects in the
  vulnerable window — a conditional reduce is identical with GC on or off (locked by a test). This is
  *correct under all GC settings* but forfeits bounded-memory condition reduction. **Still owed:** make the
  in-flight root set **engine-global** (the `Runtime` owns a stack of active reduce frames every
  safe-point GC walks) so conditions can reduce under GC — needed before release-mode safe-point GC is
  actually used with conditions.
- **`Subproblem::next` borrow widening to `&mut Runtime`** — **DONE** in B1 (plus `build_result`).
- **Persistent-structure crate** (`rpds` vs `im`) — only the **deferred** red-black `ACU_TreeDagNode`
  needs it; B1 ships the flat `Vec` rep. Pick when the tree rep lands (benchmark vs the GC/arena model;
  it must trace through the §1.3 visitor).
- **Equality/compare dispatch** for the S-theory (scalar `count` ≠ child id) — `deep_equal`/`dag_compare`
  are not enough (§1.3). Add when **S lands in B3**.
- **`leq` representation** (`BTreeSet` → `fixedbitset`) — **still open**; B2 kept `BTreeSet` and added the
  down-set table (`Sorts::leqs`, also `BTreeSet`) for `compute_sort`. Migrate both together with B2's
  larger sort sets (R3 M2) as a perf step.
- **Parser ambiguity ordering** — observable; lock with differential tests (B4).
- **Where built-in constants live** in `NodeTerm` (a `BuiltIn` arm vs per-type arms) — decide at B3.
- **Solution-order fidelity beyond the locked cases** — the correctness-first matchers reproduce the
  binary on the suite (lone-var + minimal-first), but exact order for *non-confluent* AC/AU systems and
  bounded `match[n]` is pinned only once Maude's Diophantine order is ported (a B1 perf follow-up).
- The `gen-checks` release feature (D2) stays deferred unless release-mode safe-point GC is actually used.

## 5. Suggested next moves (B1 + B2 done)
1. Read §0 docs + run the §0 sanity checks (now **79 tests**; B1 + B2 conformance green).
2. **Open B3** — built-in data types + `malachite` bignums, **including the deferred S (`iter`) and NA
   theories** (§2 B3). New `NodeTerm::{S, Na}` arms (additive, as ACU/AU/CUI were) + the `enum SpecialOp`
   built-in seam; the S-theory needs the **theory-specific equality/compare dispatch** (§1.3/§4). The lazy
   `strat` reduce frame (B2.4) and the condition machinery (B2.3) are already in place for `if_then_else_fi`
   / built-in predicates.
3. Then **B4** (parser), **B5** (modules + REPL = the Phase-1 end milestone).
4. *(Cross-cutting follow-ups, any time — see the §2 B1/B2 deferred lists + §4:)* **F-2** the engine-global
   condition-reduce GC root set (before release safe-point GC + conditions); the flattened sort-diagram +
   preregularity warning + cross-kind overloading; `leq`/down-sets → `fixedbitset`; `frozen`/`memo`; the
   red-black ACU tree rep + optimized Diophantine matcher; CUI collapse-matching; rewrite `=>` conditions
   (Phase 2).
