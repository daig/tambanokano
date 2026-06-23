# Phase 1 Stage B — plan & the as-built foundation it builds on

**Read this first when starting Stage B** (the breadth work — the real functional engine). Stage A (the
foundation reshape, review Tier 2) is **complete and adversarially reviewed**; this doc records the
*seams it produced* — the internal API Stage B plugs into — and the ordered **B1–B5** agenda. It
supersedes `06-phase1-plan.md` §3–§4 for the breadth work (`06` remains the Phase-1 overview; its §3
Stage A is now done).

> **STATUS (2026-06-22) — B4.1–B4.4 DONE: the parser MILESTONE is hit.** `tnk-frontend` parses
> `conformance/{iter,bool,nat,int}.maude` from text and reduces them to the reference binary's exact sort +
> rewrite count + value (lexer → surface parser + signature build → mixfix grammar → plain Earley+prec/gather
> [DRP bypassed] → forest → build_term → load/reduce). Commits `b3b5819..01f28a5`; 31 frontend + 100 core
> tests; clippy clean; fib(22)=186579; tnk-core untouched (until B4.6's one read accessor). **B4.6
> (pretty-printer) DONE too** (`76b41ca..e356bc5`): a **raw** round-trip printer (`parse∘print=id`) + a
> Maude-faithful **pretty** printer with ANSI syntax coloring; the uncolored faithful form textually matches
> the binary's printed result on the milestone (exposing one value-identical ACU-print-order divergence =
> a `dag_compare` follow-up). **B4.5a–d DONE** (`0e88496..688af56`): the differential
> harness now covers **15 of ~17** conformance modules text→reduce vs the binary (B4.5a–c: built-in
> literals, the `.`-terminator lexer fix, conditional `ceq`/`cmb`/`owise`/`:=`), and **B4.5d** added the
> **`match`/`xmatch` command** via a new public kernel multi-solution API (`Engine::match_solutions` →
> `Solutions::{advance,binding,matched_portion}`) — `acu-match`+`cui` lit up, solution **sets** verified vs
> the binary (exact ACU *order* = the deferred Diophantine follow-up; CUI order matches). **B4.5e + the
> whole-suite test DONE (`1442fa8`) → B4 COMPLETE.** `__` juxtaposition (`op __ : E E -> E [assoc]`, the
> empty-syntax production `E ::= E E`) turned out to **already work** through the existing machinery — the
> `[assoc]` right-associating gather + the recognizer's prec gate disambiguate the adjacent nonterminals,
> then the AU kernel flattens — so it just needed `au.maude` wired (verbatim vs the binary). The
> **whole-conformance-suite differential test** round-trips (`parse∘print_raw = id`) **all 21** modules and
> immediately earned its keep, surfacing a negative-float round-trip gap (`neg(1.5)` → the literal `-1.5`,
> which the lexer now classifies — optional sign + exponent). **B5 MODULE SYSTEM DONE** (`5d72976`
> frontend / `8aab414` `tnk-modules`): the new `tnk-modules` crate flattens a module's `protecting`/
> `extending`/`including` import closure (+ summation `+` + renaming `* (…)`) as a **pure `PreModule →
> PreModule` transform** (decision #5), feeding the unchanged build pipeline; `import-*.maude` conform vs
> the binary. **B5 REPL DONE → PHASE 1 COMPLETE** (`92b6b4d` frontend / `e7e4e69` `tnk-repl`): the new
> `tnk-repl` crate (lib `Repl::eval` + a `rustyline` binary) enters modules, `reduce`/`match`es against a
> current module, `select`/`show`/`quit`s, and loads a `.maude` file from argv — `tnk-core` untouched.
> "Write Maude, get answers." **102 core + 68 frontend + 10 modules + 9 repl tests; fib(22)=186579.** Next
> is Phase 2 (parameterized programming, rules, the real prelude). See §2 B5 below for as-built detail.
> *(History:)* B1 (structural theories), B2
> (order-sorted / membership / conditional / attribute), and **B3 (built-in data types + bignums + the S
> `iter` and NA atomic theories)** are all **done on `main`**, every lock conformance-verified vs the
> reference binary (**100 tests**, clippy `-D warnings` clean, `fib(22) = 186579` and ~7.2 M rw/s intact
> throughout). B3 = 8 sub-steps `a90f0b3..fe7cd3a` (num/S → BOOL → NAT → INT → NA/STRING/QID → FLOAT →
> RAT); both B3 audit watch-items closed in code (the S-`count` `deep_equal`/`dag_compare` arms; BranchSymbol
> laziness via auto `strat (1 0)`). §2 B3 below is the as-built summary; **§2 B4–B5 are the unchanged forward
> plan.** Earlier commit trail `23d6fd4..7d09469` (F-A guard + B2.1…B2.4). **Audit findings:** F-3/F-4 closed in B1; F-A
> (below) closed by a loud guard; **F-1** (no-op rewrite guard) still genuinely unimplemented — moot for
> the locked theories, revisit if a self-rewriting `eq a = a` becomes reachable; **F-2** (nested-reduce GC
> root set) is now **mitigated** (GC disabled during condition eval, B2.3) but **not fully closed** — the
> engine-global active-frame root set is still required before release-mode safe-point GC runs with
> conditions (§4).
>
> **POST-B2 AUDIT (2026-06-21) — ready for B3 after one fix.** Re-ran all 12 conformance locks on the
> reference binary (all TRUE) + full-kernel re-read. Found & **closed F-B**: an asymmetric overloaded
> declaration on a *commutative* op (the prelude's `_+_ : NzNat Nat -> NzNat`) gave an
> argument-order-dependent **wrong** least sort — a silent *correctness* gap the locks didn't cover (every
> theory op in the suite is single-decl). Fixed by Maude's `commutativeSortCompletion` (§2 B2.1 + B2 below);
> `conformance/acu-overload.maude` added. **B3 watch-items:** the S-theory scalar `count` is the #1 *silent*
> trap (`deep_equal` walks `children()` generically → an `[arg]` S arm makes `s^2(0)==s^3(0)`; §1.3); and the
> real `if_then_else_fi` is a `BranchSymbol special` with `poly`, **not** a user `strat (1 0)`, so B3 must
> actively wire BranchSymbol→lazy and decide `poly`/`Universal` handling (B2.4's lazy frame is the mechanism,
> not an automatic fit).
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
    iteration**, not the flattened decision table (the *table* is a perf follow-up); the `unique`/preregularity
    bit is computed but the user-facing **warning is deferred** (no diagnostics sink yet). Single-kind
    overloading only (cross-kind ad-hoc → arg-driven kind selection is a follow-up, `debug_assert`-guarded).
    **Post-B2 audit fix (F-B):** direct iteration checks declaration applicability *positionally*
    (`leq(arg_sorts[i], decl.domain[i])`), so an **asymmetric overload on a commutative op** (the prelude's
    `_+_ : NzNat Nat -> NzNat`) gave an argument-order-dependent **wrong** least sort — a *correctness* gap,
    not perf. Closed by porting Maude's `BinarySymbol::commutativeSortCompletion`: `commutative_sort_completion`
    adds the swapped `[b,a]->r` declaration for each asymmetric `[a,b]->r` on an ACU/CUI op, so the positional
    check (and the multiset fold = Maude's `argVecComputeBaseSort`) is order-independent. Locked by
    `conformance/acu-overload.maude` + the `{acu,cui}_asymmetric_overload_least_sort_is_commutative` tests.
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
- **Carried-forward follow-ups (none block B3):** the flattened sort-diagram *decision table* (perf only —
  the *correctness* of commutative-overload sorts is now handled by `commutative_sort_completion`, F-B) +
  preregularity *warning*; cross-kind ad-hoc overloading; `leq`/down-sets `BTreeSet` → `fixedbitset` (R3 M2);
  **F-2** the engine-global condition-reduce GC root set (mitigated, §4); `frozen`/`memo`; rewrite `=>`
  conditions (Phase 2); `special` (→ B3, with the built-in seam).

### B3 — Built-in data types + bignums  — **DONE** (`a90f0b3..fe7cd3a`, 2026-06-22)
- **As-built (on `main`):** the S (`iter`) and NA (atomic) theories + the `special (id-hook …)` seam
  (`enum SpecialOp` + public `Engine::set_special`, dispatched at the top of `try_rewrite_top`) + bignums
  (`crate::num` over `malachite`, D4). **BOOL** (EqualitySymbol; lazy BranchSymbol via auto `strat (1 0)`),
  **NAT** (S numerals; ACU_NumberOp folds the multiset w/ multiplicity + residue; NumberOp quo/rem/`^`/cmp),
  **INT** (MinusSymbol; the number machinery lifted `Nat`→`Int`, the `minus` hook gating negatives),
  **NA + STRING + QID** (`NodeTerm::Na{value:NaValue}`, value-compared in deep_equal/dag_compare; StringOp
  concat/length/substr/cmp), **FLOAT** (`NaValue::Float(u64 bits)`; FloatOp), **RAT** (DivisionSymbol
  canonicalises `I/N` — RAT *arithmetic* is equation-defined, a post-parser B5 milestone). The two audit
  watch-items closed: the S-`count` `deep_equal`/`dag_compare` arms (else `s^2(0)==s^3(0)`); BranchSymbol
  laziness wiring. 100 tests, conformance `conformance/{iter,bool,nat,int,string,float,rat}.maude` == binary.
  *Op-coverage follow-ups (same machinery, add on demand):* bit ops/shifts, string find/rfind/case/ascii,
  float rem/floor/trig, INT/RAT gcd/lcm/min/max, NA-constants-in-patterns (`Term::Na`), `poly`/`Universal`.
- **Original goal (met):** `BOOL`, `NAT`, `INT`, `RAT`, `FLOAT`, `STRING`, `QID` working — **plus the S
  (`iter` successor) and NA (atomic constant) theories**, deferred from B1 because they need bignums /
  built-in data respectively.
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

### B4 — Frontend: lexer + mixfix parser + pretty-printer  — **COMPLETE (B4.1–B4.6, all sub-steps); NEXT: B5**
- **As-built (on `main`, `b3b5819..01f28a5`):** the `tnk-frontend` crate. **B4.1** lexer (Maude tokenization
  + op-name `_`-splitting). **B4.2** surface recursive-descent parser (`fmod…endfm` → `PreModule` with raw
  token *bubbles*) + `build_sig` (drives the kernel constructor API, resolves `special (id-hook…)` →
  `SpecialOp`). **B4.3** per-module mixfix grammar — port of `makeComponentProductions`/`makeSymbolProductions`
  + `computePrecAndGather` (`grammar::{prec_gather,build}`); typed `Nt`/`Terminal`/`GSym`/`Action`/`Production`;
  per-*kind* nonterminals (sort/overload resolution stays post-parse, B2); `mayAssoc` sort bias deferred
  (verified no-op on the locked modules). **B4.4a** Earley recognizer (`cfparser::{compile,earley}`) — **plain
  Earley + prec/gather, DRP bypassed** (purely-additive memo; Maude's two gating checks collapse to one
  completer rule `hole-gather-bound >= completed-prec`). **B4.4b** forest extraction (`cfparser::forest`,
  right-to-left `extractFirstSubparse` + ambiguity flag) + `build_term` (the functional `makeTerm` subset —
  `MakeTerm`/assoc-list-flatten/`MakeVariable`/`MakeNatural`/`PassThru`; the kernel folds the uniform `Term`
  into the right theory node at `instantiate`/`rebuild`) + the `reduce` command. **B4.4c = THE MILESTONE**
  (`load::load_source`): unconditional `eq`/`mb` wired, commands tagged to their module; **`conformance/
  {iter,bool,nat,int}.maude` parse→reduce→identical sort + rewrite count + value vs the reference binary**.
  Fix found: `SMALL_NAT` excludes the value-0 numeral (Maude splits `ZERO`/`SMALL_NAT`; `0` is the declared
  constant) so `s s 0` is unambiguous. **31 frontend tests; 100 core tests; clippy `-D warnings` clean; fib(22)
  =186579 and tnk-core untouched throughout B4.** **Deferred to B4.5/B4.6 (below):** punctuation-split op names
  (`<_,_>`), structured sorts, conditional `ceq`/`cmb`/`owise`-conditions + `match` command, large-numeral
  DagId fast-path, the `f^n(t)` iter-token form, `mayAssoc` bias, and the **whole-prelude differential test**.
- **B4.6 DONE (`76b41ca..e356bc5`):** the pretty-printer, both forms. **B4.6a** the one `tnk-core` read accessor
  (`DagNode::repr` → `NodeRepr{App,Iter,Str,Qid,Float}` + `Nat::to_decimal`). **B4.6b** the **raw** round-trip
  printer + the shared core walk — parenthesization is the exact inverse of the Earley prec/gather gate
  (`required_prec < prec` + the `LEFT_BARE`/`RIGHT_BARE` capture cases, ported from `dagNodePrint.cc`),
  resolved prec/gather via `prec_gather::compute`; round-trips all four milestone modules
  (`parse∘build∘print_raw(reduce(t)) == reduce(t)`). **B4.6c** the **Maude-faithful** display printer
  (`s_^n(0)` power form, compact `-3`) + ANSI **syntax-category** coloring (toggle); the uncolored faithful
  form **textually equals the binary's printed result** for every milestone command (a stronger check than
  B4.4's `deep_equal`). **What it exposed (COSMETIC, not a bug):** the residue prints `5 + x` vs the binary's
  `x + 5` — `dag_compare` orders ACU elements by `SymbolId`, Maude by `Symbol::orderInt`. Same multiset →
  identical equality / normal forms / sorts / arithmetic; only the print order differs, and we don't need
  visual parity. The only non-cosmetic leak would be AC matcher solution-order → rewrite *counts* in
  *non-confluent* systems (not results; functional modules are confluent; already the pre-existing "Maude
  Diophantine order" deferral). So aligning it is **optional** (task #7) and costs a full AC count
  re-verification — deliberately NOT done. **40 frontend + 101 core tests; clippy `-D` clean; fib(22)=186579.**
- **B4.5a–d DONE (`0e88496..688af56`) — coverage, broadened to the conformance suite.** Scope correction:
  the "whole-prelude" diff is really the **conformance suite** (only `TRUTH-VALUE` is import-free in the real
  prelude; the rest need B5 imports). **B4.5a–c** (`0e88496` harness + membership-count fix / `e953375`
  built-in literals via `build_dag` + the `.`-terminator lexer fix [Maude's keyword-lookahead, also fixing
  multi-statement lines] / `2af15f3` conditional `ceq`/`cmb`/`owise`/`:=` condition-bubble parse): **13** of
  ~17 modules load+reduce, differentially verified. Three real bugs the wide net surfaced — a reset-after-
  build rewrite-count error, the space-`.` terminator flaw, an `[owise]`-swallowing rhs bubble. **B4.5d**
  (`688af56`) the **`match`/`xmatch` command**: a **new public kernel multi-solution API** —
  `Engine::match_solutions(pattern, nr_vars, subject, extension) -> Solutions<'e>` (holds `&mut Engine`),
  `Solutions::{advance()->bool, binding(idx), matched_portion()->DagId}` — lifts the crate-private
  `LhsAutomaton`/`Subproblem.next` stream (only `match_pattern`'s single yes/no reached it) out for callers.
  `extension` threads `ext_allowed` (true=`xmatch` sub-part+residue, false=plain `match` whole-subject);
  `matched_portion` = `instantiate(pattern, subst)`. Frontend `load.rs::match_command` builds the pattern→
  `Term` (VarIndex names) + subject→ground DAG, drives the stream capturing `DagId`s **while** it borrows the
  engine, renders after it drops (the stream's `&mut Engine` vs the printer's `&BuiltModule` — collect-then-
  render); `render_solution`/`format_matchers` reproduce Maude's `Var --> value` / `Matched portion = …` /
  `empty substitution` / `No match.` layout. **Correctness call:** solutions are compared **as a SET** — the
  correctness-first AC enumerator finds all-and-only the right solutions in *its own* order; Maude's exact
  Diophantine order stays the deferred B1 follow-up (every binding renders byte-identical; CUI's 2 pairings
  even match order). `acu-match`+`cui` now conform (15 of ~17). **102 core + 62 frontend tests; clippy `-D`
  clean; fib(22)=186579; tnk-core += the `match_solutions` API only.**
- **B4.5e + the whole-suite test DONE (`1442fa8`) — B4 COMPLETE.** **`__` juxtaposition already worked.**
  `op __ : E E -> E [assoc]` emits the empty-syntax production `<E> ::= <E> <E>` (two adjacent nonterminals,
  no anchoring terminal). The prior session deferred it as "the hardest grammar case" *without testing it* —
  but it needs no new code: the `[assoc]` right-associating gather `(e E) = [40,41]` disambiguates it. The
  recognizer's prec gate blocks the wrong (left-assoc) split — a prec-41 `__` app can't fill the bound-40
  left hole, so `E → E•E` at that origin is never created — and `find_split`'s prefix check (`existsCall`)
  therefore finds only the right-associative parse, which the AU kernel flattens modulo assoc. `au.maude`
  loads + matches the binary verbatim (the 4 ordered AU matchers incl. `nil` via the identity; `d b c d =>
  d a d`; `a c c => b`). Wired as `au_conforms` (match set-compared + the two reduce locks). **The
  whole-conformance-suite differential test** (`whole_conformance_suite`): a **round-trip** sweep
  (`parse∘print_raw = id`) over **all 21** conformance modules, the explicit list a coverage guard. It
  immediately earned its keep — surfaced a **negative-float round-trip gap**: `neg(1.5)` reduces to the
  literal `-1.5` (Maude prints `-1.5` and re-lexes it as one Float token, since tokens are
  whitespace-delimited — `5.0 - 1.5` stays three), but our `classify` required the integer part to be
  all-digits, so `-1.5` fell through to `Ident`. Fixed in the lexer (`is_float_literal`: optional leading
  sign + optional `[eE][-+]?` exponent; a spaced `-` is untouched = binary minus). **All 21 modules now
  load+reduce (15 value-checked + the full set round-tripped); 102 core + 65 frontend tests; clippy `-D`
  clean; fib(22)=186579.** **Deferred B4.5 items (loud, never silent; none block B5): structured sorts
  (`resolve_sort` errors), the `f^n(t)` iter-token form (`build_dag` errors), large-numeral DagId fast-path
  (perf), `mayAssoc` bias (verified no-op). NEXT: B5 (modules + REPL = the Phase-1 end milestone).**
- **⚠ ORDERING — do B4.6 (pretty-printer) BEFORE B4.5 (coverage).** *(The plan lists them 5-then-6; we
  deliberately swap.)* **Why:** B4.5's strongest deliverable — the **whole-prelude differential test** — needs
  a true *textual* comparison against the reference binary's printed output, which requires the pretty-printer
  (the inverse renderer). The B4.4 conformance instead hand-encodes expected values; that does not scale to the
  prelude. Building the pretty-printer first lets B4.5 validate coverage by **round-trip** (`parse∘pretty = id`
  on reduced terms) and by **textual diff vs the binary**, rather than by hand-transcription. B4.6 is also where
  B4 **first touches `tnk-core`**: it needs a few small *read* accessors (S-node iter `count`, `NaValue`
  rendering, and a public rep discriminator — `NodeTerm`/`NaValue` are `pub(crate)` today, and there is no
  public accessor for the iter count). The B4.5 items that are pure-frontend and *not* gated on the printer
  (punctuation-split op names `<_,_>`, structured sorts, conditional `ceq`/`cmb` + the `match` command) may be
  picked up in either order, but the prelude diff-test lands last, on top of B4.6.
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

### B5 — Module system (non-parameterized) + REPL  *(the Phase-1 end milestone)* — **COMPLETE → PHASE 1 DONE**
- **Goal:** load multi-module functional `.maude` text and `reduce`/`match` it interactively. ✅
- **MODULE SYSTEM DONE (`5d72976` frontend / `8aab414` `tnk-modules`):** the new **`tnk-modules`** crate
  (→ `tnk-frontend` → `tnk-core`). **Flatten is a pure `PreModule → PreModule` transform** (decision #5,
  not C++ donation): resolve the transitive import closure depth-first, **imports-before-importer**
  (Maude's donation order → rewrite counts conform), merge every module's declarations **once** (a
  `visited` set keyed by the canonical module expression dedupes diamonds; sorts/var-names de-duplicated;
  the frontend's `(name,arity)` map folds op overloads), then hand the combined module to the **unchanged**
  `build_loaded_module`. The build pipeline (`build_module`/special-hook + anchor resolution/grammar/
  statements) needed **no change** — it already resolves everything **by name** over the whole `PreModule`.
  Import **modes are invisible to flattening** (confirmed in `importModule.cc`: the donate routines never
  consult the mode — it's a semantic-check annotation), so `protecting`/`extending`/`including` flatten
  identically. **Summation** `A + B` = the union; **renaming** `* (sort A to B, op f to g)` substitutes
  names across declarations + statement bubbles (single-token op names; mixfix/disambiguated op-rename
  loud-deferred). As-built: `tnk-frontend` parses imports + module expressions (`surface::ast::{Import,
  ModuleExpr,RenameItem}`, the `module_expr` recursive-descent, `is_top_level_keyword` += the import kw);
  `tnk-modules::{db::ModuleDb, flatten::flatten, rename::apply_renaming, load::load_program → Program}`.
  **Conformance** (vs the binary): `conformance/import-{protecting,modes,diamond,summation,renaming}.maude`
  — sort + rewrite count + value + a `print_raw` round-trip. **102 core + 68 frontend + 10 modules tests;
  clippy `-D` clean; fib(22)=186579.**
- **REPL DONE (`92b6b4d` frontend / `e7e4e69` `tnk-repl`) → PHASE 1 COMPLETE.** The new **`tnk-repl`** crate
  (lib + bin over `tnk-modules`). **Lib** `Repl`: a terminal-free engine (persistent interner + `ModuleDb` +
  built modules + current module); `eval(input) -> Eval{output,exit}` dispatches REPL meta-commands
  (`quit`/`q`/`exit`, `select`, `show module[s]`, a `set` stub), module definitions (insert → `flatten` →
  `build_loaded_module` → current, silent on success), and `reduce`/`match` against the current module
  (Maude-style `reduce in M : … / rewrites: N / result Sort: value` + `match … <=? … / Matcher N …`, reusing
  `reduce_command`/`match_command`/`format_matchers`/`print_pretty`); `input_complete` is the multi-line
  buffer boundary (a closed module / a top-level `.` / a bare `quit`). **`tnk-core` UNTOUCHED.** **Bin**: a
  `rustyline` driver — load an optional `.maude` from argv, then buffer multi-line input and `eval` it; color
  only on a TTY (`IsTerminal`), Ctrl-C abandons the buffer, Ctrl-D quits. The frontend gained
  `Parser::parse_top_item` (single top-level item — a module or an *untagged* command — so a REPL command
  binds to the persistent current module; `parse_source` loops over it). **9 eval-driven tests** (module entry;
  a command in a later submission; the import-diamond + renaming files reduced *through the REPL* matching the
  binary; match display; select/show/quit; `input_complete`). **102 core + 68 frontend + 10 modules + 9 repl
  tests; clippy `-D` clean; fib(22)=186579.**
- **PHASE 1 IS COMPLETE.** "Write Maude, get answers" — the kernel (B1–B3), the parser + pretty-printer (B4),
  the module system (B5 `tnk-modules`), and the interactive REPL (`tnk-repl`), all conformance-verified vs the
  reference binary. Next is **Phase 2** (parameterized programming: theories/views/`LIST{X}`; rules `rl`/`rew`/
  `search`; the real prelude with `Universal`/`poly`) and the deferred cross-cutting follow-ups (below).
- **FULL MAUDE `trace` DONE (`0ef40cd`..P6, 2026-06-23) — see `docs/migration/08-full-trace-plan.md`.**
  Supersedes the earlier step-trace (`4590e0d`/`97b9aab`). The kernel records a structured
  `Option<Vec<TraceEvent>>` stream (Rewrite/Membership/Trial/Fragment, each tagged with a condition-nesting
  `depth`; zero-cost off; eq/mb get dense ids); the frontend keeps per-statement source `Term`s + var names
  (`BuiltModule::{eq_traces,mb_traces}`); the REPL renders the whole surface — eq/built-in/membership bodies +
  substitution + redex/`--->`/result, the **conditional sub-stream** (`trial`/`solving`/`success`/`failure`),
  and the granular **`set trace <option> on|off`** flags (body/substitution/rewrite/whole/condition/eqs/mbs/
  builtin), incl. **faithful `set trace whole`** (`Old:`/`New:` reconstructed from the reduce frame stack).
  **Byte-identical to the reference binary** (color off) across §1a–1e of `08`; `conformance/trace-*.maude`
  fixtures + 8 repl tests. FIXED follow-ups: command-echo re-spacing (`c0a8827`, Maude `printTokens`) and the
  multi-fragment `:=` backtrack (`trace_deterministic_backtrack` — the recursive solver now emits the
  `re-solving`/`failure` pair when unwinding through a succeeded deterministic fragment; trace-only,
  byte-exact across crossing shapes). **One remaining deviation — a real evaluation-model difference**:
  **eager** sort-constraint application (we apply `mb` at node construction) vs Maude's **lazy**
  (`DagNode::reduce` applies constraints only to equational normal forms). Symptoms: rewrite-count over-count
  on a membership over a *reducible* term (e.g. `eq g(a)=b`+`mb g(a):T`: Maude 1, ours 2), and the omitted
  membership `Whole:`. Result/least-sort always faithful (verified, incl. lazy `strat`); triggered only by
  memberships on reducible terms (well-formed specs use constructor memberships → conformance passes). Fix =
  move `constrain_to_smaller_sort` into the reduce loop (after `try_rewrite_top`→None) with a base/true-sort
  split. (Variable index order MATCHES Maude — lhs→condition→rhs, `equation.cc:74`.)
- **Deferred (loud, never silent):** other `set` options (rule/strategy/select trace are Phase-2-of-project);
  module re-entry cache invalidation (build-on-entry); parameterized programming + rules + the real prelude =
  Phase 2; disambiguated/mixfix op-rename; semantic no-junk/no-confusion checks; flatten caching.
- **Refs:** `A5` (the module half — skip §parameterization); arch-map L6 + decision #5.
- **Risks (retired for the module system):** flatten was made a pure transform (no `Rc`/dirty-set/donation
  coherence problem); term ownership is per-module (fresh engine per flattened module — decision #5).

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
