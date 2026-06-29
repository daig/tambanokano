# Roadmap — what remains (Phase 2 and beyond)

Phase 1 (functional engine) and Phase 1.5 (correctness hardening) are complete. This is the forward plan.
Each phase ends at a runnable, conformance-verified milestone and grows the `conformance/` suite. The C++
subsystem detail behind each item is in `reports/A1–A8`; the foundational tech choices are in
`03-open-decisions.md` (D5/D6/D7 are the still-pending forward decisions).

## Phase 2 — System modules + modularity

The jump from a *functional* engine to a *rewriting* one, plus the module algebra that lets the real
prelude load.

1. **Rules + rewriting (Pillar A) — DONE.** `rl`/`crl` (incl. the `=>` rewrite-condition), `rewrite`
   (rule-fair) / `frewrite` (position-fair, frozen-aware), `search` (`=>1`/`=>+`/`=>*`/`=>!`, `such that`,
   bounds, `show path`/`graph`), `continue` — all byte-conformant (`conformance/{rewrite,frewrite,crl,
   search,rewrite-cond}.maude`). Built on a separate rule table (never read by `reduce`), the shared
   `drive_match` seam, and a lazy hash-consed state-transition graph (`search.rs`). **Still open (Phase 2):**
   object-message-fair `frewrite`/`erewrite` (needs objects, item 5); `frozen`'s lazy-`strat` interaction +
   search/rewrite-condition trace (`gaps.md`). Reference: `reports/A6-operational.md`.
2. **Parameterized programming (Pillar B) — DONE (mechanism + all of "Axis A").** Theories `fth`/`th`,
   views (sort + op→op/op→term maps), parameterized modules (`{X :: T}`, `X$Elt`, structured sorts `List{X}`),
   and instantiation `M{V}` — including every Axis-A corner case: view op-maps (A1), import/target dedup (A3),
   theory/module-declared sorts (A4), and the entangled hard pair **parameterized views + free-vs-bound nested
   instantiation** (A2/A5 — all three C++ argument kinds: module-view, by-parameter, theory-view; incl.
   `LIST{List{Nat}}` nesting, cross-kind ad-hoc overloading with `(t).Sort` disambiguation, and structured-sort
   memberships). The whole layer is a pure `tnk-modules` `PreModule → PreModule` transform — the kernel
   (`build_module`/grammar) is **unchanged** (`List{X}` / `X$Elt` are string-keyed sorts). All byte-conformant
   (`conformance/{theory-*,view-*,param-*,instantiation-*}.maude`). The **chained multi-level instantiation**
   `M{ToTheory}{Arg}` (the SORTABLE-LIST family — `LIST{STRICT-WEAK-ORDER}{X}` renamed to `List{X}`) now
   loads too: the parameter's `$`-sort binds to the final chain level, and chained imports' renaming items
   are parameter-substituted so the chain name collapses level by level (`conformance/instantiation-chained.maude`;
   `SORTABLE-LIST{Nat<}` sorts byte-identically). The one residual (orthogonal, in `gaps.md`):
   identity-collapse rewrite **count** (the AC matcher, reproduces non-parameterized). Reference:
   `reports/A5-modules-parameterization-repl.md`.
3. **The real prelude — `poly`/`Universal` + loading the actual library. ← DONE on the data path; the only
   non-loading modules are objects-gated.** The data library + the **whole META-LEVEL surface** (item (c),
   Stages 1–5) are complete; the remaining prelude modules (`LEXICAL`/`LOOP-MODE`, the `[object]` attribute)
   need objects/IO (Phase 2 item 5), and the symbolic/SMT/strategy *implementations* are Phase 3.2/3.3 /
   item 4. The real
   `BOOL`, `NAT`, `LIST{Nat}`, the container library, **and all the built-in data types** (`INT`/`RAT`/
   `FLOAT`/`STRING`/`QID`/`CONVERSION` + the leaf specials) load and reduce **byte-identically** to the
   reference. **`META-LEVEL` now builds and computes byte-identically across the descent family AND the
   level-shift / query / syntax layer** (item (c), Stages 1–5 — the down/up maps, the whole
   `metaReduce`/`metaRewrite`/`metaApply`/`metaMatch`/`metaSearch`/… family, **the `up*` family**
   (`upModule`/`upImports`/`up{Sorts,SubsortDecls,OpDecls,Mbs,Eqs,Rls}`/`upView`/`upTerm`/`downTerm`), **the
   sort/kind queries** (`sortLeq`/`sameKind`/`leastSort`/`lesserSorts`/`glbSorts`/`completeName`/
   `getKind(s)`/`maximal`/`minimalSorts`/`maximalAritySet`), **`metaParse`/`metaPrettyPrint`/
   `metaPrintToString`**, and **`metaWellFormed*`** — including `format`-attribute display). The
   symbolic/SMT/strategy descent is declared and **reduces inert** (Stage 5 — `descend`'s exhaustive
   `=> None` arm; never misfires) until its backends land. The only prelude modules that still **don't**
   build are the few that import `QID-LIST`/objects (the parameterized-view gap + the `[object]` attribute —
   both off the data path, Phase 2 item 5). `poly-universal-prelude.md` is a record of the gateway. What
   landed:
   - **`poly` / the `Universal` sort** — a `Universal`-typed op (`_==_`/`_=/=_`/`if_then_else_fi`) is expanded
     into one concrete instance **per connected component** (eager per-kind, in `build_sig` after
     `close_sorts`); no new kernel reduction code (the existing `Equality`/`Branch` special ops reduce each
     instance). The `SystemTrue`/`SystemFalse` anchors and bare-boolean conditions came with it. **(M0)**
   - **NAT built-ins** — the `~>` partial arrow + the arithmetic / bitwise / shift codes
     (`xor`/`&`/`|`/`sd`/`modExp`/`>>`/`<<`) over `malachite` bignums. **(M1)**
   - **The container substrate** — module-local variable aliases (the flattener was leaking imported `var`s,
     mistyping `LIST`'s `append`) and **AU identity-collapse matching** (a pattern `E L` matches a singleton
     `c` as `c nil`) — the two things `LIST{Nat}` needed beyond the existing Pillar-B module algebra. **(M2)**

   **Prelude work, in dependency order (all ✅ DONE — the data path loads & runs end-to-end):**
   - **(a) Container library — ✅ DONE (the data structures).** `EXT-BOOL`, `SET{Nat}`, `MAP{Nat,Nat}`,
     `ARRAY{Nat,Nat0}` all load and reduce byte-identically (`conformance/prelude-{set,map,array}.maude`). It
     took the **`[Sort]` kind notation** (`var B : [Bool]`, `op undefined : -> [Y$Elt]` → `error_sort(kind_of
     S)`), **ACU identity-collapse matching** (the AU analog), and three problems they surfaced: **non-linear
     ACU** matching (`E in (E, S)` — the pure path now deep-equal-checks pre-bound vars), the **assoc-list
     separator spacing**, and the **`id:`-attribute parse** bug (`collect_until(["]"])` swallowed `prec`/
     `format`, defaulting the constructor precedence). CUI collapse is unneeded (no comm-only-with-`id:` op).
     The whole **container-view frontend** now loads: parameterized view declarations + structured-sort
     renamings parse, the eq parser handles a `[_]`-list rhs / trailing `[owise]`, and **chained
     instantiation** `M{ToTheory}{Arg}` flattens correctly — so `NAT-LIST`/`QID-LIST`/`QID-SET` build &
     reduce, the `[_]`-list `LIST*`/`SET*` build, and the `SORTABLE-LIST` family loads (`SORTABLE-LIST{Nat<}`
     sorts byte-identically). Coverage: `conformance/{view-parameterized,eq-bracket-rhs,instantiation-chained}.maude`.
   - **(b) The remaining built-in data types — ✅ DONE.** `INT` (`abs`, `~`, signed two's-complement
     bitwise), `RAT`, `FLOAT` (the full op set — `rem`/`^`/`floor`/`ceiling`/`min`/`max`/`exp`/`log`/trig —
     and Maude's **partiality**: `/0` and out-of-domain NaN don't reduce, leaving the term at kind `[Float]`,
     while `log(0.0) = -Infinity` does), `STRING`/`QID` (`ascii`/`char`/`find`/`rfind`/case, the STRING-OPS
     `ctype` predicates + `startsWith`/`endsWith`/`trim`, `string`/`qid`), `CONVERSION` (`float`/`rat` —
     exact float↔rational — `string`/`rat` base conversion, `string`/`float`, `decFloat`); plus the leaf
     special ops `CommutativeDecomposeEqualitySymbol` (INITIAL-EQUALITY-PREDICATE), `RandomOpSymbol`
     (RANDOM — MT19937 seed 0), and `CounterSymbol` (COUNTER — a stateful *rule*-special: inert under
     `reduce`, advancing 0,1,2,… under `rewrite`/`frewrite`, reset per command). All byte-identical to the
     reference (`conformance/prelude-tier2.maude`, 43 reduces; `prelude_tier2_through_repl`). This needed
     four cross-cutting pieces beyond "more codes": the **`in <MODULE> :` command qualifier** (reduce in any
     loaded module — the natural way to exercise the real prelude); a **`Term::Na` literal** (so a float/
     string/qid constant can sit in an equation rhs — `eq pi = 3.14…`); **value-dependent NA sorts**
     (length-1 string → `Char`, finite float → `FiniteFloat`); **`~>` partiality tracking** (a partial op's
     range is its kind); and a **punctuation-aware `split_mixfix`** (so the `_=[_]_` / `<_,_,_>` / `[]` / `{}`
     operators whose names lex with brackets parse and print). Breadth, plus that handful of seams.
   - **(c) The reflective wall — `META-LEVEL`** (META-TERM/MODULE/VIEW/LEVEL + descent functions
     `metaReduce`/`metaApply`/…). A major new subsystem (= Phase 3 item 1), gated on STRING/QID. **✅ DONE —
     Stages 1–5** (`conformance/prelude-meta.maude`, `prelude_meta_through_repl`): the reflection core (the
     descent family), the `up*`/query/parse/wellformed layer (Stage 4), and the inert symbolic/SMT/strategy
     declarations (Stage 5) — the whole implementable surface computes byte-identically; only the
     backend-gated *implementations* (Phase 3.2/3.3, item 4) remain. **Stage
     2 — the reflection core: `metaReduce`/`metaNormalize` compute, byte-identically** (value, sort, and
     rewrite count). The
     descent seam is a `DescentOps` trait + a `MetaCtx` view of the engine, defined in `tnk-core` and
     threaded through `reduce` (kernel-internal callers pass a `NullDescent`); the handler (`tnk-modules`,
     which owns the build pipeline + module db) **down**-translates the meta-module argument into a real
     object module (a reconstructed `PreModule` → the ordinary `flatten`+`build`; `flatten_pre` flattens a
     transient root), down-translates the subject meta-term, reduces in it (folding the object rewrites into
     the command's count, Maude's accounting), and **up**-translates the result `{term, type}` (constants
     `'c.S`, applications `'f[…]`, the iter form `'s_^n[…]`). The meta-rep symbols are resolved from each
     descent op's `op-hook` list by **signature** (name + kinds) into `MetaHooks`. This also needed the
     **`<Qids>` classification** — a `Qid` constant's least sort is text-dependent (`'0.Zero` → Constant,
     `'NzNat` → Sort, `'X:S` → Variable, `'[K]` → Kind), which also makes META-TERM's `getName`/`getType`
     reduce. **Scope of Stage 2:** the module argument is an **import expression** (`[Q]` = `sth Q is
     including Q . … endsth`, the `['NAT]`/`['BOOL]` form); a meta-module with **inline declarations** (what
     `upModule` emits) returned `None` at the time (stayed at kind level) — `down_module`'s declaration
     parsing + the rest of the descent family landed in Stage 3 (below). **Stage 1 — the whole tower parses and loads with no errors**;
     the descent functions are declared via a new `SpecialOp::Meta` (`MetaLevelOpSymbol` → `MetaOp`).
     Getting there closed
     five general parse/flatten gaps the meta-modules are the first to hit (none specific to reflection):
     **grammar-aware mixfix op renaming** (`op _,_ to _;_ [prec 43]` over QID-SET — an operator comma vs an
     argument separator can only be told apart by parsing, so the source module's parser marks the operator
     occurrences; the optional `[…]` overrides the target op's attributes); **two-instantiation constant
     disambiguation** (NAT-LIST + QID-LIST both inline LIST's `nil`, so a bare `nil` is sort-qualified
     `(nil).NatList`/`(nil).QidList` on inline — the constant analogue of the existing variable inlining);
     the **`input_complete` chunker** counting `fmod`/`endfm` only as real delimiters (depth-0, statement-
     leading), not as the meta module-constructor operators' name fragments (`getName(fmod Q is … endfm)`);
     **kind-homogeneous equation parsing** (a bare overloaded `none` rhs parses at the lhs's kind); and the
     module-constructor operators whose names carry `.`/`is`/`endfm` fragments. **Stage 3 — inline
     `down_module` + the rewriting/matching/search family.** The module argument now carries **inline
     declarations** (sorts, subsorts, attributed ops, memberships, equations, rules), not only imports:
     `down_module` reconstructs the full `PreModule` → the ordinary flatten/build, then installs the inline
     statements by down-translating their meta-terms straight into the engine (`down_term_to_term` — the
     `Term`-producing mirror of `down_term`, with indexed variables). On it the whole family computes,
     byte-identically (value + rewrite count): **`metaRewrite`/`metaFrewrite`** (rule-/position-fair →
     `ResultPair`), **`metaMatch`** (→ `Substitution?`), **`metaSearch`** (BFS reachability → `ResultTriple?`
     with the goal substitution), **`metaApply`** (a labelled rule at the top → `ResultTriple?`),
     **`metaXapply`** (a rule at any position, with the hole **context** `'f[[]]` → `Result4Tuple?`),
     **`metaXmatch`** (extension match + context → `MatchPair?`), and **`metaSearchPath`** (the witness
     `Trace` of up-translated rules). New plumbing: `up_substitution`, the hole-`context` up-map +
     `up_pattern`/`up_rule` (the first of the `up*` family), and three general fixes the inline form is the
     first to hit — **`shareWith` hook inheritance** (every descent op but `metaReduce` declares only
     `op-hook shareWith (metaReduce …)`), **parenthesized op-name quoting** (`op (op_:_->_[_].) : …` — the
     outer quoting parens are stripped, fixing both the grammar production and the by-profile hook resolve),
     and **constants-first op ordering** (an `id(c)` identity resolves against an already-declared `c`). The
     **`[]`/`{}` constant pretty-printer** (all name fragments, not just the first) came with the hole.
     **Stage 3.5 — the `format` display layer — DONE.** `print_pretty` now honors the `format (…)` operator
     attribute: one directive word per mixfix **gap** (`d` = the existing default spacing, `s` space, `t`
     tab, `n` newline, `i` indent to the current level, `+`/`-` indent-level — composing as `n++i`/`ni`/`--`),
     applied on both the binary and the assoc-fold print paths (the work-stack gained newline/indent items +
     an indent counter); an op whose format uses an unmodelled directive (`r`/`o`, on some IO/array ops)
     falls back to the default, so a partial model never mis-renders. The whole META descent family now
     renders **byte-identically to the reference — value, rewrite count, *and* layout**: `_<-_`'s
     `format (n++i d d --)` newline-indents each substitution binding (so an `Assignment` / a
     `ResultTriple`-with-substitution / a `MatchPair` break onto continuation lines), `rl_=>_[_].`'s `s`
     directives space `[attrs]`/`.` (so `metaSearchPath`'s up-rule prints `'c.Elt [label('ab)] .`), and
     `__`'s `format (d n d)` newlines each element of a folded list (a two-step `metaSearchPath` `Trace` —
     the same fold path `upModule`'s declaration lists will reuse in Stage 4). The conformance test now
     captures each result's full multi-line value, pinned to the reference's exact bytes. So Stage 4 starts
     on a clean compute surface — its `up*` results conform on display from the first reduce.
     **Stage 4 — the `up*`/query/parse layer — DONE.** The inverse of Stage 3's down maps, plus the lattice
     queries and the syntax ops, all byte-conformant (`conformance/prelude-meta.maude`'s Stage-4 block,
     `prelude_meta_through_repl` — value + sort + count + layout). What landed:
     `upModule`/`upImports`/`up{Sorts,SubsortDecls,OpDecls,Mbs,Eqs,Rls}` decompose a *named* module (resolved
     in the db, flattened + built) back to its meta-rep — mirroring `down_sorts`/`down_subsorts`/`down_ops`/
     `install_{membs,eqs,rules}`. The `Bool` (flat) flag selects the whole import closure vs. the module's own
     declarations (the suffix of the flat build's trace vectors — flatten appends own statements last); empty
     sets render `none`. `up_pattern` gained iter-chain collapse (`s s X` → `'s_^2['X:S]`) + NA literals;
     `up_rule`/the new `up_condition` reconstruct conditional rules/equations. `upTerm`/`downTerm` are the
     term-level wrappers over the **current** module — a new `MetaCtx` name resolver (`resolve_op`/`make_iter`,
     backed by `Signature::resolve_symbol` + a stamped-id `Arena::iter`) is the seam, since they read/build in
     the engine the redex is reducing in (not a down-translated object module). `upView` decomposes a view
     (header + from/to module exprs + sort/op maps) from the view db. `metaParse` reuses the per-module grammar
     (`build_command_dag`'s Earley parse, no reduce) → `ResultPair?`/`noParse`; `metaPrettyPrint`/
     `metaPrintToString` reuse the format-aware `print_pretty` → `QidList`/`String`. The sort/kind queries
     (`sortLeq`/`sameKind`/`leastSort`/`lesserSorts`/`glbSorts`/`completeName`/`getKind(s)`/`maximal`/
     `minimalSorts`/`maximalAritySet`, the last reading per-overload op declarations via a new
     `Engine::symbol_declarations`) read the engine's sort lattice; `metaWellFormed{Module,Term,Substitution}`
     are structural checks (a kind-match walk catches the ill-typed term/binding the kernel builds permissively).
     The Stage-4 boundaries (each its own surface, `gaps.md`): flat-mode `special`/`poly` builtin-hook
     attributes (the inverse of `down_attrs`' boundary — so flat `upModule` over a builtin module stays inert);
     the multi-attribute `ctor`-order ACU divergence; non-`mixfix` print options; own `nonexec`-statement up;
     structured (non-`Named`) module expressions + op→term view maps.
     **Stage 5 — the inert declarations, finalized — DONE.** The symbolic (unify/variant/narrow, Phase 3.2,
     D6 BDD), SMT (Phase 3.3, D7 Z3), and strategy (Phase 2.4) descent — `MetaOp::Deferred` plus the
     strategy-up maps `upStratDecls`/`upSds` — are declared, parse (the tower loads), and **reduce inert** to
     the kind level via a single exhaustive `descend` arm (`Deferred | UpStratDecls | UpSds => None`), so a
     newly-added descent op now forces a dispatch choice at compile time and a deferred op can never misfire.
     `conformance/prelude-meta.maude`'s Stage-5 reduces pin the inert kind-level result (ours, not the
     reference's — that's the point of the boundary). The implementations themselves are the respective later
     phases. **Orthogonal residuals — *not* a subphase; each rides its own subsystem (`gaps.md`).** None
     gates Stage 4 and Stage 4 produces none of them, so forcing them into a stage would misrepresent their
     independence: the descent **condition evaluator** (→ conditional-rule `metaApply` + conditioned
     `metaMatch`) and a non-empty **partial substitution** (→ `metaApply`/`metaXapply`) are reflection compute
     corners; the **AC-residue `metaXmatch` context** rides the AC/Diophantine matcher and the
     **exhausted-search failure count** the search engine. All conform on value + rewrite count today; only
     the corner inputs are unhandled.
   - Residuals, off the reduce path (`gaps.md`): the parameterized **sortable-list views** parse gap
     (`expected 'to', found "{"`); the **`xmatch`-with-extension** over-enumeration; the ≥3-operand-infix
     number-fold rewrite-**count** delta. The **Diophantine solver** stays separable (an AC-matcher throughput
     optimization; the naive matcher already gives correct counts), needed for heavy AC `search`, not to load.
4. **Strategy language** (`srew`/`dsrew`, combinators, `matchrew`, calls, strategy modules). **← IN PROGRESS:
   the parser + core interpreter are done (Phase 2.4 A+B).** `smod`/`sth` modules parse (`strat`/`strats`,
   `sd`/`csd`), the `srewrite`/`dsrewrite … using …` commands run, and the core combinators —
   `idle`/`fail`/`all`/rule-application-by-label/`top`/`one`/`;`/`|`/`*`/`+`/`!`/`?:`(+ `try`/`not`/`test`/
   `or-else`)/`match`/`amatch` — enumerate solutions **byte-identically to the reference** (values + order;
   `conformance/strategy.maude`, `strategy_core_through_repl`). A surface `StratExpr` combinator tree (term
   parts as bubbles) → a resolved `RStrat` (`tnk-frontend::strategy`) → a recursive solution enumerator over
   the engine (iteration cycle-detected by `deep_equal`; rule application reuses match/instantiate/reduce on
   an explicit position walk). **Strategy definitions + calls (Phase C) done too:** `sd` definitions build a
   call table on the module, a `Call` resolves to its (parameterless, unconditional) body, and recursion is
   cycle-detected on `(dag, name)` — so `go := r1 ; r3`, `go2 := go | r2`, and the recursive
   `reach := idle | (… ; reach)` all enumerate byte-identically (`dsrewrite`). **Remaining (D/E):**
   **`matchrew`** + rule **conditions**/application substitutions + `xmatch` + parameterized/`csd` calls (the
   condition machinery); the **fair BFS `srewrite`** order *and* per-solution count (today's eager depth-first
   accounting matches `dsrewrite` exactly — value/sort/reachability always faithful; the BFS snapshot is the
   follow-on, `gaps.md`); and the strategy **meta** ops (`upStratDecls`/`metaParseStrategy`/…). Plan:
   `strategy-plan.md`. Reference: `reports/A6-operational.md`.
5. **Objects / external IO** (configurations, classes/messages, fair object-message rewriting; standard
   streams / files / sockets / processes; Ctrl-C). Brings in the **D5** `mio` reactor + `signal-hook`
   decision. Reference: `reports/A6-operational.md`.

**Milestone:** Core-Maude system-module level; the prelude library loads & runs end-to-end.

## Phase 3 — Reflection, symbolic reasoning, verification (full parity)

1. **Reflection / meta-level.** `META-LEVEL` descent functions (`metaReduce`/`metaRewrite`/`metaApply`/
   `metaMatch`/`metaSearch`/…), up/down maps, meta-interpreters (nested interpreter objects). Per **D1**,
   descent runs as an in-heap sub-context of the same engine; true meta-interpreters are separate engines.
   Reference: `reports/A7-meta-builtins.md`.
2. **Symbolic.** Order-sorted **unification** modulo axioms; **variants** + variant unification; **narrowing**
   (`vu-narrow`/`fvu-narrow`). Brings in the **D6** pure-Rust BDD backend (`biodivine-lib-bdd`) for the
   order-sorted unifier, ACU Diophantine selection, and LTL labels. Reference: `reports/A8-symbolic-smt-ltl.md`.
3. **SMT + verification.** `check`/`smt-search` over the **D7** `z3` trait backend (+ variant satisfiability as
   a `.maude` library); **LTL model checking** (LTL→Büchi via Gastin-Oddoux + nested DFS, counterexamples);
   invariant model checking via search. Reference: `reports/A8-symbolic-smt-ltl.md`.
4. **OO + Full Maude** as a frontend desugaring pass + a `.maude` meta-level library.

**Milestone:** Maude 3 feature parity across the manual; conformance suite green.

## Ports vs. rethink (for the as-yet-unbuilt layers)

**PORT faithfully** (the algorithm is sound and data-oriented): `rewrite`/`frewrite` traversal & fairness;
the AC **bipartite + Diophantine** matcher (currently a naive backtracking stand-in — see `gaps.md`); variant
**folding** (most-general + descendant eviction); narrowing (v3 only); **LTL→Büchi** + nested-DFS model
checking; the parameter/view instantiation algebra; the `.maude` prelude.

**RETHINK** (the C++ idiom does not survive Rust): backtracking via pointers/`goto` → iterators / resumable
state machines; module donation + manual module-GC → the pure flatten transform already in `tnk-modules`;
the meta descent fn-ptr table → an enum/registry; SMT build-time backend pick → the **D7** runtime trait;
the global poll-reactor + signal plumbing → the **D5** `mio` reactor.

**DROP** (no parity-v1 obligation): `FullCompiler` (experimental C++ codegen); the dead narrowing
generations (keep v3); `freePreNet` codegen; LaTeX/XML pretty buffers; `LOOP-MODE`; redundant BDD debug
cross-checks.

## Risk register (forward items)

1. **Parameterization corner cases** (Phase 2, "Axis A" — the B-iv deferrals) — **RESOLVED**: A1–A5 all
   landed, differentially verified with hand-rolled fixtures. The one residual is a rewrite-**count** delta
   from identity-collapse matching (item 3 below — orthogonal to parameterization, reproduces without it).
2. **`poly`/`Universal` polymorphism** (Phase 2 item 3) gates loading the *real* `BOOL`→`NAT`→`LIST` chain
   (a `Universal`-typed op instantiated per connected component); a separate feature from parameterization.
   → Differential against `prelude.maude`'s `TRUTH`/`BOOL`/`NAT`.
3. **AC/collapse matching at scale** — the naive matcher is correct but un-optimized; porting Maude's
   bipartite/Diophantine matcher is a perf prerequisite for heavy AC search. → Differential `xmatch`/`search`.
3. **BDD backend maturity** (Phase 3) gates all symbolic features. → Prototype `biodivine-lib-bdd` early
   (the `SortBdds` sort-function + AllSat path) before committing.
4. **Incompleteness propagation** (assoc unification) — must thread unify→variant→narrow as a flag so the
   right warnings fire end-to-end.
5. **Fresh-variable families** (`#n`/`%n`) — centralize in one generator.
6. **Search/state-graph memory** — the bounded-memory re-entrant reduction (C6/F-2) is in place; the state
   graph itself needs the same GC discipline.

## Conformance strategy (cross-cutting, unchanged)

Every "PORT" claim above is validated against the C++ binary, not from memory: same input through
`~/Downloads/Maude-3/maude` and our build, diffing canonical output. Seed new fixtures from the prelude, the
manual's worked examples, and `~/code/maude-lang/Maude/tests`.
