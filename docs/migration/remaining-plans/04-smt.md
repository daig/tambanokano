# Phase T — SMT (`check`, `smt-search`) — implementation plan

Status: PLAN (no production SMT code exists; SMT id-hooks are declared-inert). D7 is **bound** by the
T0 gate spike (`spikes/smt-spike/`, `reports/T0-smt-spike.md`): the `z3` crate is the default backend
behind `trait SmtEngine`, feature-gated, default build stays pure-Rust. This document is the phase-T
build plan under `subsystems-goal.md` §2 (Phase T) and the roadmap §G3.

This plan cites both trees: **tnk** = `crates/…`, **ref** = `~/code/maude-lang/maude/src/…`. The oracle
is the **Yices2-enabled** rebuild (`~/.local/bin/maude`); run
`MAUDE_LIB=~/code/maude-lang/maude/src/Main ~/.local/bin/maude -no-banner <f>.maude < /dev/null`.

---

## 1. Subsystem overview

Two user commands plus a built-in SMT theory, all over an external SMT solver:

- **`check <BoolExpr> .`** — decide satisfiability of an SMT Boolean term. Prints exactly one
  solver-derived token: `Result from sat solver is: sat` / `unsat` / `undecided`.
- **`smt-search [bound, depth] <t> =>{1,+,*} <pattern> [such that <cond>] .`** — rewriting-modulo-SMT
  reachability: explore rule rewrites while accumulating a **symbolic** path constraint, pruning states
  whose constraint is unsatisfiable, and report solutions matching the pattern together with the
  accumulated constraint. Continuable (`continue n .`).

The **SMT theory** is the `.maude` library `smt.maude` (ref `Main/smt.maude`), four modules:
- `BOOLEAN` — sort `Boolean`; `true`/`false`, `not_`, `_and_`/`_xor_`/`_or_`/`_implies_`, polymorphic
  `_===_`/`_=/==_`, `_?_:_` (ite).
- `INTEGER` — sort `Integer`; the numeral injector `<Integers>`; `-_`, `_+_`, `_*_`, `_-_`, `_div_`,
  `_mod_`, comparisons `_<_ _<=_ _>_ _>=_`, `_===_`/`_=/==_`, ite, `_divisible_`.
- `REAL` — sort `Real`; `<Reals>`; the arithmetic set with `_/_` (real division) instead of div/mod.
- `REAL-INTEGER` — `toReal`, `toInteger`, `isInteger`.

Every SMT operator is **declared-inert at the Maude level**: `SMT_Symbol` is a plain `FreeSymbol` with
no equations, `<Integers>`/`<Reals>` are `NA_Symbol` numeral injectors. They carry no reduction
behaviour — they only exist to be *translated to solver formulas*. An SMT "program" is therefore a
functional/system module that `protecting`-imports one of these modules, declares SMT-sorted variables,
and writes `check`/`smt-search` commands (or, for `smt-search`, rules whose conditions are SMT
equalities `t = true`). Example (ref `tests/Misc/smtTest.maude`):

```maude
load smt
mod ITEST is
  pr INTEGER .
  sort State . sort Foo .
  op f : Integer -> State .   var X : State .
  crl f(I) => f(I + 1) if I >= 10 = true /\ I <= 12 = true .
  crl f(I) => f(I - 1) if I >= 10 = true /\ I <= 12 = true .
endm
smt-search [4] f(11) =>* X .
```

There are also two **meta-level** entry points (ref `Main/prelude.maude:2977–2985`):
`metaCheck : Module Term ~> Bool` and
`metaSmtSearch : Module Term Term Condition Qid Nat Bound Nat ~> SmtResult?`. See §4.6 for scope.

Role: SMT is one of the three symbolic verification subsystems (with variants/narrowing and LTL model
checking). It sits on the kernel + free/NA theories + the search machinery; it does **not** depend on
order-sorted unification or BDDs. Its one soft dependency is **variant satisfiability** (manual §16.6),
a `.maude` library over variants (S2) — out of core scope here (§4.7).

---

## 2. Reference approach (C++)

### 2.1 The SMT theory objects

- **`SMT_Symbol`** (ref `SMT/SMT_Symbol.{hh,cc}`) `: public FreeSymbol`. Carries an `int op` from the
  `OPERATORS` enum (`SMT_Symbol.hh:34–76`): `CONST_TRUE, CONST_FALSE, NOT, AND, OR, XOR, IMPLIES,
  EQUALS, NOT_EQUALS, ITE, UNARY_MINUS, MINUS, PLUS, MULT, DIV, MOD, LT, LEQ, GT, GEQ, DIVISIBLE,
  REAL_DIVISION, TO_REAL, TO_INTEGER, IS_INTEGER`. `attachData` (`SMT_Symbol.cc:108–128`) maps the
  id-hook code string (`operatorNames[]`, `SMT_Symbol.cc:57–100`) to the enum, with a **special case**:
  code `"-"` → `UNARY_MINUS` if `arity()==1` else `MINUS` (both spelled `-`). No `eqRewrite` — the
  symbol never reduces.
- **`SMT_NumberSymbol`** (ref `SMT/SMT_NumberSymbol.{hh,cc}`) `: public NA_Symbol`. The `<Integers>` /
  `<Reals>` injectors (`numberSystem` = `integers`/`reals`). Numerals at an SMT sort become
  `SMT_NumberDagNode`s holding an `mpq_class` value (ref `SMT/SMT_NumberDagNode.cc:45`); parsed by the
  grammar action `MAKE_SMT_NUMBER` via `mpq_class(name); rat.canonicalize()`
  (`Mixfix/mixfixParser.cc:914–921`) and printed by `handleSMT_Number` — INTEGER prints the numerator,
  REAL prints `num/den` (`Mixfix/termPrint.cc:217–245`).
- **`SMT_Info`** (ref `SMT/SMT_Info.{hh,cc}`) — the per-module SMT metadata, built at module compile by
  each symbol's `fillOutSMT_Info` (`SMT_Symbol.cc:156–186`, `SMT_NumberSymbol.cc:101–122`): a
  `sort-index → {BOOLEAN,INTEGER,REAL}` map, the **conjunction operator** (`AND`), the **true symbol**
  (`CONST_TRUE`), and a per-kind **equality operator** map (`EQUALS`). Consumers read
  `getType(sort)`, `getConjunctionOperator()`, `getTrueSymbol()`, `getEqualityOperator(lhs,rhs)`.

### 2.2 The solver seam and the term→solver translation

- **`SMT_EngineWrapper`** (ref `SMT/SMT_EngineWrapper.hh:30–55`) — the abstract seam:
  `Result assertDag(dag)`, `Result checkDag(dag)`, `clearAssertions()`, `push()`, `pop()`,
  `VariableDagNode* makeFreshVariable(Term*, mpz_class)`. `Result` enum = `BAD_DAG=-2, SAT_UNKNOWN=-1,
  UNSAT=0, SAT=1`.
- **`VariableGenerator`** is the concrete impl, selected **at build time** by `#ifdef`
  (`Mixfix/variableGenerator.cc:57–103`): `USE_CVC4` → `cvc4_Bindings.cc`, `USE_YICES2` →
  `yices2_Bindings.cc`, else a **no-solver stub** whose ctor prints
  `Warning: No SMT solver linked at compile time.` and whose `checkDag`/`assertDag` return
  `SAT_UNKNOWN`. `makeFreshVariable` is **shared** (`variableGenerator.cc:109–125`): it builds a
  `VariableDagNode` named `"#" + number + "-" + baseName` — this is the origin of the `#1-Y` names in
  `smt-search` output.
- **Translation** (ref `Mixfix/yices2_Bindings.cc:221–412`, `dagToYices2`): a recursive walk of the
  DAG. `SMT_NumberDagNode` → `yices_mpq`. `VariableDagNode` → `makeVariable` (`:160–219`), which caches
  by `(sort-index-within-module, name-id)` so a re-seen variable reuses the same solver term, and picks
  the solver type from `SMT_Info::getType(sort)` (Bool/Int/Real; non-SMT sort → warning + `NULL_TERM`).
  `SMT_Symbol` → a per-`op` builder (`yices_not/and2/or2/xor2/implies/eq/neq/ite/neg/sub/add/mul/idiv/
  imod/…/is_int_atom`). `makeBooleanExpr` (`:221–246`) is the entry gate: it requires the top to be an
  `SMT_Symbol` (or variable) of **Boolean** range sort, else warns
  `"Expecting an SMT Boolean expression but saw but saw <dag>"` (the doubled "saw but saw" is a genuine
  reference typo — see §5) and returns `NULL_TERM` → `BAD_DAG`.
- `assertDag` (`:83–110`) = translate, `yices_assert_formula`, `yices_check_context` → verdict.
  `checkDag` (`:112–139`) = **push, assert, check, pop** — a non-mutating satisfiability probe. `push`/
  `pop` map straight to `yices_push`/`yices_pop`, `clearAssertions` to `yices_reset_context`. This
  incremental push/pop contract is exactly the D7 gate (spike P3: incremental ≡ fresh over 894 nodes).

### 2.3 `check`

Ref `Mixfix/execute.cc:536–577`: parse the subject in the current flat module, `normalize(false)`,
`term2Dag`; get `fm->getSMT_Info()`; construct a `VariableGenerator vg(smtInfo)`; `vg.checkDag(d)`.
`BAD_DAG` → only a warning (no result line). Otherwise print
`Result from sat solver is: ` + `sat`/`unsat`/`undecided`. Oracle-confirmed output (harness normalizes
the `====` banner and the `check in M : t .` echo line survives):

```
check in TEST-B : X =/== true and X =/== Y and Y =/== true .
Result from sat solver is: unsat
```

The BAD_DAG case (`check I + J .` where `I,J : Integer`) prints **only** the two warnings and no
`Result` line — and warnings are stripped by the conformance harness, so a BAD_DAG `check` normalizes to
just its echo line.

### 2.4 `smt-search`

Setup ref `Mixfix/search.cc:255–275`; driver ref `Mixfix/smtSearch.cc:27–117`; engine ref
`SMT/SMT_RewriteSequenceSearch.{hh,cc}` + `SMT/SMT_RewriteSearchState.{hh,cc}`. Structure:

- **State** (`SMT_RewriteSequenceSearch.hh:81–90`): `{ constraint (DagNode), context (state term),
  avoidVariableNumber (mpz), parent, rule, depth }`. States are held in an index vector; **no
  hash-consing** (states carry distinct symbolic constraints, so structural collapse would be wrong).
- The initial state's constraint is built from the command's `such that` condition by
  `makeConstraintFromCondition` (`.cc:148–212`): each `t1 = t2` fragment becomes an SMT clause
  (optimising `= true` away), conjoined with the `AND` operator; empty → `true`.
- **Per-state expansion** (`SMT_RewriteSearchState::findNextRewrite`, `.cc:102–169`): `clearAssertions`,
  assert the state constraint (`checkAndConvertState`, `:296–303` — prunes if already UNSAT), then for
  each rule on the state's top symbol: match its non-ext LHS automaton; on a match, `checkConsistancy`
  (`:203–294`) binds unbound rule variables to **fresh SMT variables** (`makeFreshVariable`, seeded from
  `avoidVariableNumber`), instantiates the rule condition into an SMT clause, does `engine->push()` then
  `assertDag(condition)` and prunes if not SAT (`pop` on failure). Success → new state term
  (`getRhsBuilder().construct`) + new constraint (old ∧ condition). Backtracking `pop`s
  (`findNextRewrite:110`). **No equational rewriting happens during SMT search** (`:292` comment) —
  the module must have no equations (§2.5).
- The **sequence** (`findNextState`, `.cc:322–387`) walks states in index order, giving each a fresh
  `SMT_RewriteSearchState`; `findNextMatch` (`:235–267`) then matches the command's target **pattern**
  against each new state with a `MatchSearchState`, and `checkMatchConstraint` (`:269–320`) checks that
  the match's SMT-variable bindings are jointly satisfiable with the state constraint (`checkDag`),
  producing `finalConstraint = stateConstraint ∧ matchConstraint`.
- **Output** (`smtSearch.cc:67–88`): per solution — `Solution N`, a stats line (`rewrites: k`),
  `state: <stateTerm>`, the substitution (goal vars ← bindings, SMT vars printed too), and
  `where <finalConstraint>`; terminates with `No solution.` / `No more solutions.`. Oracle-confirmed
  (`tests/Misc/smtTest.expected:243–257`):

```
smt-search [10] in MULTI : f(-2, X) =>* Z:State .

Solution 1
rewrites: 0
state: f(-2, X)
Z:State --> f(-2, X)
where true

Solution 2
rewrites: 1
state: g(-2 + 1, #1-Y:Foo)
Z:State --> g(-2 + 1, #1-Y:Foo)
where -2 < 0

No more solutions.
rewrites: 1
```

Note the load-bearing, **engine-rendered** details that must be byte-exact: solution **order and
count**, per-solution rewrite counts, the fresh-variable spelling `#1-Y:Foo`, and the constraint's
**mixfix parenthesization** (e.g. `11 >= 10 and 11 <= 12 and (11 + 1 >= 10 and 11 + 1 <= 12)` — the
right conjunct is parenthesized because `_and_` has `gather (E e)`, left-associative). The constraint is
printed by the ordinary mixfix pretty-printer over the SMT operators' `prec`/`gather` (from
`smt.maude`), so tnk's existing printer handles it once the SMT ops carry their syntax.

### 2.5 Module validity for SMT rewriting

Ref `Mixfix/mixfixModule.cc:1603+` (`validForSMT_Rewriting`): the module must have **no equations, no
membership axioms, at least one rule, an SMT conjunction operator, and no collapse-axiom symbols**;
each failure issues a (stripped) warning. This gates `smt-search`.

### 2.6 What is conformance-load-bearing (and what is not)

The T0 spike §2 established (verified across the C++ source, manual ch. 16, and the reference tests)
that **solver identity cannot leak into fixture bytes**: `check` prints one verdict token; `smt-search`
prints engine-rendered state/substitution/**symbolic** constraint; there is no model-printing surface
anywhere in 3.5.1 (`metaCheck` returns a `Bool`, `metaSmtSearch` returns engine terms). So any two
correct solvers over the decidable QF_LIA/QF_LRA/Boolean fragments produce byte-identical Maude output —
**tnk-on-z3 vs oracle-on-Yices2 is byte-safe by construction**, and the cross-library order-fidelity
problem (the D6/BDD analogue) has no counterpart here. This is the single most derisking fact for phase T.

---

## 3. What tnk already has to build on

- **The `SpecialOp` seam** (tnk `symbol.rs:181–285`, resolved in `sig/build_sig.rs:585–723`). SMT
  symbols currently fall through the id-hook dispatch to `_other => return Ok(None)`
  (`build_sig.rs:720`) — **declared-inert**. Adding SMT is a new arm exactly like the existing
  `EqualitySymbol`/`NumberOpSymbol`/`StreamManager` arms: parse the id-hook code into a new
  `SpecialOp::Smt { op }`, and (for `<Integers>`/`<Reals>`) a marker-class NA constructor. The marker
  machinery (`build_sig.rs:363–374`, `set_symbol_class`) and `set_special`/`set_ctor` plumbing
  (`:372–393`) are ready. **The SMT ops are otherwise ordinary free/NA symbols** — the kernel already
  reduces, matches, and rewrites them (they have no equations), so nothing kernel-deep changes.
- **The DAG** (tnk `dag.rs`): `NodeTerm::Free { symbol, args }` (`:48`) makes the DAG→solver recursion a
  trivial `match`; `NodeTerm::Var { symbol, name, index }` (`:94`) is the genuine variable leaf the
  translation keys on (`name` is the interned base token — exactly Maude's `(sortIndex, nameId)` cache
  key). `NaValue` (`:103–115`) currently has `Str/Qid/Float`; SMT numbers need a rational value (§4.2).
- **Bignums** (tnk `num.rs`): `Int`/`Rat` (malachite) with `to_string_base`/`from_string_base`
  (`num.rs:166–173`) — SMT numerals cross to z3 as **string numerals** (spike P4), no i64 truncation.
- **The search / state-graph machinery** (tnk `search.rs`): the existing `Search` is a **hash-consing
  BFS** and is *not* directly reusable for `smt-search` (symbolic states must not collapse), but it is
  the structural precedent — a `State` vector with parent/rule/depth links, lazy one-successor-at-a-time
  expansion, `RootGuard` pinning, and `continue` resume. The reusable primitives are the engine's
  one-step rewrite (`engine.state_successors`/`reduce_successor`) and goal matching (`engine.eval_goal`,
  the `such_that` `CompiledFragment`s).
- **The central fresh-variable generator** (tnk `fresh.rs`, landed as S1 groundwork) — the `#n`/`%n`/`@n`
  families. `smt-search`'s `#n-Base` fresh SMT variables must come from **this** generator (roadmap risk
  #8: one generator before a second consumer exists).
- **The object-message seam / command precedent**: the **`unify` command** is the exact template for
  wiring a new symbolic command — surface parse (`surface/parser.rs:343–357`) → `Command::Unify` →
  REPL dispatch reaching into `lm.built.engine` (`repl/lib.rs:598–655`) via a builder function
  (`unify_command`) with a dedicated renderer (`render_unifier`). `check`/`smt-search` follow this shape.
- **`load` resolution** (tnk `repl/lib.rs:792–814`, `meta_load`): resolves a name against CWD then
  `$MAUDE_LIB` (colon-separated), with and without `.maude`. `load smt` needs `smt.maude` findable → ship
  a byte-identical copy in tnk's lib dir (§4.5).
- **The z3 spike** (`spikes/smt-spike/`, `reports/T0-smt-spike.md`): z3 crate 0.12 / z3-sys 0.8 against
  brew `libz3`; build plumbing `Z3_SYS_Z3_HEADER=/opt/homebrew/include/z3.h` + `-L /opt/homebrew/lib`.
  Every fixture-shaped verdict (P2), the incremental≡fresh gate (P3), and bignum/rational/coercion
  mapping (P4) are green. The spike's `verdict()`, `dagToYices2`-shaped `match`, and push/pop DFS
  transcribe directly into the production `translate.rs` and `smt-search` state machine.

---

## 4. Architectural fit & divergence

### 4.1 The `SmtEngine` trait + feature-gating (D7)

Mirror `SMT_EngineWrapper` as a narrow Rust trait (D3 "traits only at open seams" — the solver is a
genuinely open seam):

```rust
pub enum SmtResult { Sat, Unsat, Unknown, BadDag }   // == Maude's SAT/UNSAT/SAT_UNKNOWN/BAD_DAG

pub trait SmtEngine {
    fn assert_dag(&mut self, e: &Engine, dag: DagId) -> SmtResult;
    fn check_dag(&mut self, e: &Engine, dag: DagId) -> SmtResult;   // push/assert/check/pop
    fn clear(&mut self);
    fn push(&mut self);
    fn pop(&mut self);
    fn make_fresh_variable(&mut self, e: &mut Engine, base: DagId, n: &Int) -> DagId; // "#n-base"
}
```

The trait takes `&Engine` because the translation reads the tnk DAG (unlike Maude, whose `DagNode`
carries its own `symbol()`); it needs the per-module SMT sort/op map (§4.3). `make_fresh_variable`
delegates to `fresh.rs` and builds a `NodeTerm::Var` — it is **solver-independent** (like Maude's shared
`variableGenerator.cc:109`), so it can live outside the feature gate.

**Feature gate.** The trait and all pure-Rust plumbing (SMT theory recognition, the SMT_Info analog, the
`smt-search` state machine, command parsing/rendering, `make_fresh_variable`) live in the **default,
pure-Rust build**. Only the concrete z3 backend (`translate.rs` DAG→`z3::ast`, and the `z3::Solver`
wrapper) is behind a cargo feature `smt-z3` that pulls the `z3` crate. Two backends resolve at runtime
via the trait:
- `smt-z3` on → `Z3Engine` (real verdicts).
- default → `NullSmtEngine`, mirroring Maude's no-solver path exactly: its constructor emits
  `Warning: No SMT solver linked at compile time.` and `check_dag`/`assert_dag` return `Unknown`, so
  `check` degrades to `undecided` and `smt-search` finds nothing. **This keeps even the default build
  oracle-faithful — to a *no-solver* Maude.** (See §4.4 for why that is the right degrade target and how
  the scoreboard handles it.)

Placement: the trait + `SmtResult` + the `smt-search` state machine belong in `tnk-core` (they need
`Engine`/`DagId`/the rewrite primitives); the `z3` dependency and `translate.rs` sit behind
`#[cfg(feature = "smt-z3")]`. If z3's build plumbing proves awkward to gate inside `tnk-core`, the
alternative is a thin `tnk-smt` crate that `tnk-core` depends on only under the feature — decide at T2
(§8). **`tnk-core` must never unconditionally depend on `z3`.**

**CI.** Two lanes: (1) default `cargo test --release` (pure Rust; F1–F4; must not require `libz3`);
(2) `cargo test --release --features smt-z3` (needs brew `libz3` + the header/link env from the spike)
where the T* fixtures live. A `cargo build --no-default-features`/default-only lane guards against an
accidental non-gated z3 dependency.

### 4.2 SMT number representation

SMT `Integer`/`Real` are **distinct sorts** from NAT/INT/RAT and their literals are their own NA
constructors (Maude: `SMT_NumberDagNode` holding `mpq_class`). tnk represents NAT/INT via the S-theory
(`NodeTerm::S { count: Nat }`) and RAT via `_/_`, which is the *wrong* model here (those sorts don't
exist in `smt.maude`). Cleanest fit: a new `NaValue::SmtNum(Rc<Rat>)` arm (a canonical rational), with
the **symbol's range-sort SMT type deciding printing** — INTEGER prints the numerator, REAL prints
`num/den` (mirrors `handleSMT_Number`, ref `termPrint.cc:217–245`). Reading: wire an SMT-number grammar
terminal (like the existing `<Floats>`/`<Strings>` token classes) so a numeral/rational token parses to
`NaValue::SmtNum` at an SMT sort (mirrors `MAKE_SMT_NUMBER`, ref `mixfixParser.cc:914–921`;
`mpq` canonicalised via `Rat`). The value crosses to z3 as a string numeral (spike P4).

### 4.3 The SMT_Info analog

Build a per-module table at module-build time from the resolved SMT symbols (mirroring `fillOutSMT_Info`,
ref `SMT_Symbol.cc:156–186`): `SortId → SmtType {Boolean,Integer,Real}`, the conjunction symbol (`AND`),
the true symbol (`CONST_TRUE`), and per-kind equality symbol (`EQUALS`). The translation and the
constraint-builder read it. This is a small addition to the signature/build alongside the existing
special-op resolution — the data is already available from the `SpecialOp::Smt` arms.

### 4.4 `smt-search` fit with the search machinery

`smt-search` gets its **own** state machine (in `tnk-core`, next to `search.rs`), not the hash-consing
`Search`. It transcribes `SMT_RewriteSequenceSearch` + `SMT_RewriteSearchState`:
- A `Vec<SmtState { term: DagId (RootGuard-pinned), constraint: DagId (pinned), avoid_var: Int,
  parent, rule, depth }>`, walked in index order; **no hash-consing**.
- Per-state expansion drives the `SmtEngine` incrementally: `clear`, assert the state constraint (prune
  if UNSAT), then per rule — match the LHS, bind unbound rule vars to `make_fresh_variable`, build the
  condition's SMT clause, `push`+`assert_dag`, prune-or-keep, `pop` on backtrack. New state term from the
  rule RHS; new constraint = old ∧ condition.
- Pattern matching per discovered state reuses the engine's matcher; the match-constraint sat-check and
  `finalConstraint` follow `checkMatchConstraint` (ref `SMT_RewriteSequenceSearch.cc:269–320`).
- **GC discipline** (roadmap risk #9): every state pins its `term` and `constraint` as roots (RootGuard),
  plus the pattern's SMT-var dags and any `finalConstraint` — the Rust analogue of C++
  `markReachableNodes` (ref `SMT_RewriteSequenceSearch.cc:127–146`). Same discipline the re-entrant
  reducer and `Search` already got.
- `continue` support mirrors `smtSearchCont` (ref `smtSearch.cc:119–134`): the REPL stores the state
  machine between calls (as it does for `Search`).

The **incremental push/pop pruning is precisely what the T0 spike P3 validated** as equivalent to a
fresh solver per node — so this composition is sound by the gate.

### 4.5 Shipping `smt.maude`

`smt.maude` is pure op-declaration data (no C++), so tnk ships a **byte-identical copy** in its lib dir
(next to `prelude.maude`), found by `load smt` via `$MAUDE_LIB` (tnk `repl/lib.rs:792–814`). No
special-casing; it loads through the normal module system once the SMT id-hooks resolve to
`SpecialOp::Smt` (i.e. from T1 on, `smt.maude` loads with computing hooks rather than inert ones). Note
`smt.maude` toggles `set include BOOL off/on` around its modules — tnk's D11 `set include BOOL` support
(`repl/lib.rs:763`) already handles that.

### 4.6 Meta surfaces (`metaCheck`, `metaSmtSearch`)

Ref `Main/prelude.maude:2977–2985`: `metaCheck : Module Term ~> Bool` (sat→`true`, unsat→`false`,
malformed→stays kind-level `[Bool]`) and `metaSmtSearch : … ~> SmtResult?` returning the 4-tuple
`{stateTerm, substitution, constraint, Nat}` (ctor `Main/prelude.maude:2303`) or `failure`
(`:2361`); op-hooks `smtResultSymbol`/`smtFailureSymbol` (`:2742,2770`). These are `MetaLevelOpSymbol`
descent ops, currently `MetaOp::Deferred` (tnk `symbol.rs:347`, `build_sig.rs:781`). They ride the
existing descent machinery (down-translate module+term, run check/smt-search, up-translate the result)
plus byte-exact `SmtResult`/`#n-Base:Sort` rendering. They are a **distinct, later stage** (T5) — see the
scope decision in §8, because the sole reference test bundles them with the object-level commands.

### 4.7 The S2 soft-dependency

**Variant satisfiability** (manual §16.6) is a Maude-level prototype (`.maude` library) built on variant
unification. Its S2 dependency is now satisfied (21/21 variant fixtures on 2026-07-19). The core phase-T
deliverables — the SMT theory, `check`, `smt-search`, and the meta surfaces — remain independent of S2.
Variant satisfiability lands as a shipped `.maude` library as the T6 follow-on and remains outside the
T1–T5 critical path.

---

## 5. Feasibility & risk (honest)

- **D7 incremental push/pop ↔ pruning gate — RESOLVED (low risk).** The T0 spike proved incremental ≡
  fresh over 894 randomized search-tree nodes with balanced assertion stacks. The `smt-search` state
  machine can mirror Maude's `VariableGenerator` seam directly (no adaptation layer).
- **Solver-independence — PROVEN (very low risk).** No model values are ever printed (§2.6). z3 vs
  Yices2 is byte-safe by construction. This removes the class of risk that dominated the BDD subsystem.
- **Feature-gate discipline — the primary real risk.** The default build must compile pure-Rust, stay
  green on F1–F4, load `smt.maude`, and parse+degrade `check`/`smt-search` without ever linking `libz3`.
  Mitigation: isolate all z3 code behind `#[cfg(feature = "smt-z3")]` (ideally a `tnk-smt` sub-crate),
  a `NullSmtEngine` for the default path, and a CI lane that builds default-only. Fragility is
  organizational (a stray unconditional `use z3`), not algorithmic.
- **Byte-exact rendering — low/medium.** Verdicts are a single token (trivial). `smt-search` constraints
  render through the ordinary mixfix printer over the SMT ops' `prec`/`gather` — tnk's printer already
  does prec/gather, so parenthesization matches once the SMT ops carry their `smt.maude` syntax. The two
  additions: SMT number printing (integer numerator / real `num/den`, §4.2) and the `#n-Base` fresh-var
  spelling (from `fresh.rs`). The **doubled "saw but saw" typo** in the BAD_DAG warning
  (`yices2_Bindings.cc:244`) is inside a warning block the harness strips, so tnk need not reproduce the
  typo for conformance — but should degrade a BAD_DAG `check` to *no result line* (only a stripped
  warning), which is the observable behaviour.
- **`undecided` mapping — low.** With z3, QF_LIA/QF_LRA/Boolean always decide; `Unknown` is reachable
  only for genuinely undecidable input (e.g. nonlinear) or the null backend. Map z3 `Unknown` →
  `undecided`.
- **Unseeded fixtures — medium (effort, not correctness).** The manifest names `tests/Misc/smtTest` as
  the seed but nothing is in `conformance/subsystems/` yet, and that **one** file bundles `check`,
  `smt-search`, `metaCheck`, and `metaSmtSearch` (plus a deliberate `[:` no-parse at line 208 and
  `select META-LEVEL`). Seeding means splitting it into `T*` fixtures per surface, oracle-verifying each
  against the Yices2 build, and freezing the manifest in `subsystems-goal.md` §2 (the phase-step-0 rule).
  The manual ch. 16 worked examples supplement it. Risk is in the split + the feature-gate/scoreboard
  interaction (§7), not in producing the values.
- **Module-validity warnings — low.** `validForSMT_Rewriting` (§2.5) issues warnings (stripped) and
  gates `smt-search`; tnk must reproduce the gating behaviour (no eqs/mbs, has rules, has conjunction),
  which is a straightforward pre-check.

---

## 6. Implementation plan (staged)

Ordered; each stage lands with its now-passing fixture(s) and keeps F1–F4 green (working-rules §4).

- **T0 — spike + oracle (DONE).** z3 crate confirmed, Yices2 oracle rebuilt (`reports/T0-smt-spike.md`).

- **T1 — SMT theory recognition + `smt.maude` loads.** (Pure Rust; no solver yet.)
  1. `SpecialOp::Smt { op: SmtOp }` — new enum (the 24-op `OPERATORS` set) resolved from the `SMT_Symbol`
     id-hook in `build_sig.rs` (mirror `attachData`'s `-`→arity split); a marker NA constructor for
     `SMT_NumberSymbol` (`integers`/`reals`).
  2. `NaValue::SmtNum(Rc<Rat>)` (§4.2) + the SMT-number grammar terminal + printing.
  3. The SMT_Info analog (§4.3) built at module-build.
  4. Ship `smt.maude` (§4.5). **Gate:** `smt.maude` loads; SMT ops recognized (not inert); a `reduce`
     leaving an SMT term unreduced matches the oracle; F1–F4 green.

- **T2 — `SmtEngine` trait + z3 backend + `check` (smallest vertical slice).**
  1. `trait SmtEngine` + `SmtResult` + `NullSmtEngine` (default) in `tnk-core`; `Z3Engine` + `translate.rs`
     behind `smt-z3` (§4.1). Translation transcribes the spike's `dagToYices2` match into z3 asts.
  2. `check` command: surface parse (`check` → `Command::Check`), REPL dispatch (the `unify` template) →
     dagify, build engine, `check_dag`, print `Result from sat solver is: …` or the BAD_DAG no-result
     path.
  3. First fixture `T01-check-bool` (a slice of `smtTest` TEST-B). **Gate:** byte-exact under
     `--features smt-z3`; default build parses + degrades to `undecided`.

- **T3 — full `check` conformance.** TEST-B / TEST-I / TEST-R / TEST-RI from `smtTest` → `T*` fixtures;
  the BAD_DAG path; bignum coefficient + exact-rational + `toReal` coercion cases (spike P4). Manual
  ch. 16 `check` examples.

- **T4 — `smt-search`.** The `SMT_RewriteSequenceSearch` state machine (§4.4): per-state incremental
  rewrite + fresh SMT vars + condition→clause + prune, pattern match + match-constraint sat-check,
  accumulated constraint, `Solution`/`state:`/subst/`where` rendering, `continue`. The
  `validForSMT_Rewriting` gate (§2.5). Fixtures: the `smtTest` `smt-search` blocks (MULTI/ITEST — solution
  order/counts, `#n-Base` names, constraint parenthesization all load-bearing).

- **T5 — meta surfaces (scope decision, §8).** `metaCheck`/`metaSmtSearch`: map the `MetaOp` codes,
  down/up translation, `SmtResult`/`failure` + `'#n-Base:Sort` rendering. Fixtures: the meta blocks of
  `smtTest`.

- **T6 — variant satisfiability (deferred, post-S2).** Ship the `.maude` library once S2 exists (§4.7).

---

## 7. Verification

- **Fixture seeding.** Split `tests/Misc/smtTest.maude` into `conformance/subsystems/T*.maude` per
  surface (`T01…` check-Boolean, `T02…` check-Integer, `T03…` check-Real, `T04…` check-RealInteger,
  `T05…` smt-search-object, and — if in scope — `T06…` metaCheck, `T07…` metaSmtSearch), plus manual
  ch. 16 probes and a fresh minimal probe. Oracle-verify **each** against the Yices2 build at authoring;
  freeze the `T*` manifest by appending it to `subsystems-goal.md` §2 in the same commit as the fixtures
  (phase-step-0 rule). Every fixture is expected to FAIL until its stage lands.
- **Harness.** `tools/subsystems-scoreboard.sh` / `diffmaude.sh` against the Yices2 oracle, same
  normalization (strips `====`, banner, `Bye.`, timing tails, **and warning blocks** — so BAD_DAG checks
  and the module-validity/no-solver warnings normalize out).
- **Feature-gate/scoreboard interaction (the key policy).** T* fixtures assert real verdicts, so they
  pass only in the `smt-z3` build; the default (Null) build degrades to `undecided`/no-solution and
  would diff. Recommendation: the T* fixtures are a **z3-lane-only** addition — the SUBSYSTEMS
  denominator grows in a `--features smt-z3` scoreboard run; the default lane runs F1–F4 (pure Rust) and
  does not include the T* verdicts (it only proves `smt.maude` loads and the commands parse/degrade).
  This keeps both lanes oracle-faithful: default ≡ no-solver Maude on SMT surfaces (un-fixtured), z3 lane
  ≡ Yices2 Maude (fixtured). The exact scoreboard mechanism (a `requires: smt-z3` fixture tag vs a
  separate lane invocation) is an open call (§8).
- **Unit tests.** `translate.rs` round-trips reproducing the spike P2/P4 shapes as tnk-DAG→z3; push/pop
  balance after a search tree (spike P3); `make_fresh_variable` naming (`#n-Base`); SMT-number
  parse/print.
- **Pure-Rust-default-green requirement (F-invariant).** A CI job runs `cargo build`/`cargo test`
  **without** `smt-z3` and must be green without `libz3` present.

---

## 8. Open questions / decisions

1. **`SmtEngine` trait shape & placement.** The §4.1 signature (does `check_dag` take `&Engine`; does
   `make_fresh_variable` live inside or outside the gate) and whether the z3 backend is a
   `#[cfg]` submodule of `tnk-core` or a separate `tnk-smt` crate `tnk-core` pulls only under the
   feature. Recommend: submodule first, promote to a crate only if z3's build plumbing forces it.
2. **Default-build degrade behaviour.** Mirror Maude's no-solver path exactly (emit
   `Warning: No SMT solver linked at compile time.` + `undecided`) so the default build is faithful to a
   no-solver Maude — recommended — vs a tnk-specific message. (Warning text is stripped by the harness
   either way; the recommendation matters only for interactive parity.)
3. **Scoreboard treatment of z3-gated fixtures.** A per-fixture `requires: smt-z3` tag the scoreboard
   skips in the default lane, vs a separate `--features smt-z3` scoreboard invocation whose denominator
   is disjoint from the default one. Either keeps F1–F4 pure-Rust; pick one and record it in the working
   rules.
4. **Meta-surface scope (T5).** `metaCheck`/`metaSmtSearch` are bundled into the one reference SMT test,
   so **full byte-exact conformance on `smtTest` requires them**. Decide whether phase-T's
   definition-of-done is (a) the object-level commands + `smt.maude` loading (meta surfaces split into
   separately-gated fixtures, landed at T5), or (b) the whole `smtTest` file byte-exact (T5 mandatory).
   `subsystems-goal.md` §2 phrasing ("`smt.maude` loads; its `SMT_Symbol` hooks compute … byte-exact
   including … `sat`/`unsat` rendering") reads as the object-level commands; the meta descent functions
   are a reasonable T5 follow-on — but this is a user call.
5. **SMT number representation.** `NaValue::SmtNum(Rc<Rat>)` (recommended) vs a dedicated node; plus the
   const-disambiguation fidelity (`(1).Integer` under `PRINT_DISAMBIG_CONST` / overloaded-integer cases,
   ref `termPrint.cc:236`) — likely negligible for the fixtures but noted.
6. **`smt.maude` shipping.** A filesystem copy on the tnk `$MAUDE_LIB` (recommended, no special-casing)
   vs bundling it compiled-in like the prelude. The copy must stay byte-identical to
   `Main/smt.maude` (a checked-in-copy drift risk — pin it).
