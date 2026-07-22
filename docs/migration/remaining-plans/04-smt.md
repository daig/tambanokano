# Phase T — SMT (`check`, `smt-search`) + variant satisfiability — implementation plan

**Status: NEXT (2026-07-21).** No production SMT code exists: `smt.maude` and
`model-checker.maude` load because unknown id-hooks degrade, but `check true .` is silently unparsed
and the solver hooks remain inert. D7 is bound by the T0 gate spike (`spikes/smt-spike/`,
`reports/T0-smt-spike.md`): `z3` 0.20.2 is the feature-gated backend behind `trait SmtEngine`; the
default build stays pure Rust. The previously missing variant-satisfiability research package has
now been recovered and studied (§4.7), removing the source-discovery blocker but exposing a license
gate and substantial Maude-2.7 API drift. This is the phase-T build plan under
`subsystems-goal.md` §2 and roadmap §G3; §8 records the bound implementation choices.

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
order-sorted unification or BDDs. The roadmap's **variant satisfiability** deliverable uses S2, but is
independent of the solver core. Its external 2016 prototype is now a pinned oracle, not production
source (§4.7).

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

Ref `Mixfix/mixfixModule.cc:1603–1742` (`validForSMT_Rewriting`): the module must have **no
equations, no membership axioms, at least one rule, an SMT conjunction operator, and no
collapse-axiom symbols**. In addition, no non-SMT operator may have an SMT sort as its range, and
every rule LHS must contain neither an SMT operator nor a nonlinear variable. Each failure issues a
(stripped) warning and gates `smt-search`. The command separately rejects `=>!`/`=>#`, term
disjunctions, and a target pattern containing an SMT operator or nonlinear variable
(`Mixfix/search.cc:39–143`). Unsupported non-equality command-condition fragments are warned and
skipped; a non-equality **rule** condition makes that candidate fail at runtime.

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
- **Bignums** (tnk `num.rs`): `Nat`/`Int` wrap malachite integers, but there is currently **no**
  general `Rat` node/value despite older plan prose assuming one. T1 adds a narrow canonical
  `SmtNumber` wrapper over `malachite::Rational`; SMT numerals cross to z3 as strings (spike P4), so
  no path truncates to `i64`.
- **The search / state-graph machinery** (tnk `search.rs`) is a structural precedent only. Its
  hash-consing BFS is wrong for constraint-bearing SMT states, and its existing
  `state_successors`/`reduce_successor`/`eval_goal` helpers are also semantically wrong here: they
  rewrite nested positions, perform equational reduction, and evaluate ordinary conditions. SMT
  search matches **non-extension rule LHSs at the root only**, never equationally reduces states, and
  turns equality conditions into solver clauses. T4 therefore needs a dedicated matcher/constructor
  boundary in `engine.rs`, while reusing the underlying LHS automata, `Subst`, RHS instantiation,
  `RootGuard`, and continuation patterns.
- **Rule retention is a real prerequisite.** `load.rs` currently skips an ordinary `[nonexec]` rule
  before parsing it, including `smtTest`'s load-bearing `f(I, X) => g(I + 1, Y)` whose unbound `Y`
  must become `#1-Y`. Do **not** widen `CompiledRule` and add skip branches to every ordinary rewrite
  path. Add a dedicated source-ordered `Signature::smt_rules` table (compiled LHS plus
  RHS/condition/slot-sort/base-name metadata), populated for every rule in a module with SMT metadata
  before the existing nonexec/executable split. Ordinary `rules` remains executable-only and
  unchanged; the SMT table alone retains the extra-RHS-variable nonexec case.
- **SMT fresh names are not a fourth symbolic family.** `fresh.rs` owns only the `#n`/`%n`/`@n`
  family contract. A solver-independent helper in `smt.rs` builds `#<Nat>-<base>`, interns it
  through `NameCodes`, and calls `Engine::make_var(sort, code, u32::MAX)`—the Rust sentinel
  corresponding to C++ `VariableDagNode(..., NONE)`. Object search starts at zero and
  `metaSmtSearch` supplies the arbitrary-precision base. This keeps the distinct C++
  `VariableGenerator::makeFreshVariable` convention out of `FreshVariableGenerator`/`UnifyEnv`.
- **The object-message seam / command precedent**: the **`unify` command** is the exact template for
  wiring a new symbolic command — surface parse (`surface/parser.rs:343–357`) → `Command::Unify` →
  REPL dispatch reaching into `lm.built.engine` (`repl/lib.rs:598–655`) via a builder function
  (`unify_command`) with a dedicated renderer (`render_unifier`). `check`/`smt-search` follow this shape.
- **`load` resolution** (tnk `repl/lib.rs`, `meta_load`) resolves a name against CWD then
  `$MAUDE_LIB`, with and without `.maude`. T1 checks in a byte-identical repository-root
  `smt.maude`; it is found through the normal filesystem path, with no compiled-in special case
  (§4.5).
- **The z3 spike** (`spikes/smt-spike/`, `reports/T0-smt-spike.md`) now uses `z3` 0.20.2 /
  `z3-sys` 0.11 against brew `libz3`. The verified build variables are
  `Z3_SYS_Z3_HEADER=/opt/homebrew/opt/z3/include/z3.h` and
  `Z3_LIBRARY_PATH_OVERRIDE=/opt/homebrew/opt/z3/lib`. Every fixture-shaped verdict (P2), the
  incremental≡fresh gate (P3), and bignum/rational/coercion mapping (P4) are green. The refreshed
  spike is the production API reference; the old lifetime-parameterized z3 0.12 calls are obsolete.

---

## 4. Architectural fit & divergence

### 4.1 The `SmtEngine` trait + feature-gating (D7)

Mirror `SMT_EngineWrapper` as a narrow Rust trait (D3 "traits only at open seams" — the solver is a
genuinely open seam):

```rust
pub enum SmtResult { Sat, Unsat, Unknown, BadDag }

pub trait SmtEngine {
    fn assert_dag(&mut self, e: &Engine, dag: DagId) -> SmtResult;
    fn check_dag(&mut self, e: &Engine, dag: DagId) -> SmtResult; // push/assert/check/pop
    fn clear(&mut self);
    fn push(&mut self);
    fn pop(&mut self);
}
```

The trait takes `&Engine` because translation reads the tnk DAG and the signature's SMT sort/op
table (§4.3). Fresh-DAG construction is deliberately **not** a solver operation: the pure helper
described in §3 owns `#n-Base`, accepts a `Nat`, and uses `NameCodes` + `Engine::make_var`.

**Feature gate.** All pure plumbing—SMT recognition/metadata, number values, fresh naming, search
state, and command/meta dispatch—lives in the default build. Only DAG→z3 translation and `Z3Engine`
are behind `smt-z3`. Two implementations resolve through the trait:
- `smt-z3` on → `Z3Engine` with real verdicts.
- default → `NullSmtEngine`; assertions/checks return `Unknown`, so valid `check` prints
  `undecided` and `smt-search` has no solutions. The no-solver Maude warning requires the future
  phase-E diagnostic sink and is intentionally outside this phase's normalized output.

Placement is bound: the trait, `SmtResult`, `SmtNumber`, metadata, pure fresh helper, and search state
machine live in `tnk-core::smt`; `tnk-core::smt::z3` and the optional `z3 = 0.20.2` dependency are
behind `#[cfg(feature = "smt-z3")]`. `tnk-repl` exposes a same-named feature forwarding to
`tnk-core/smt-z3`. A separate backend crate would either need the core DAG dependency injected from
the REPL or create a cycle; there is no payoff for that split now. **`tnk-core` must never
unconditionally depend on z3.**
`ConfiguredSmtEngine` is a small cfg-shaped enum (`Null`, plus `Z3` when enabled) implementing the
trait; `SmtSearch<ConfiguredSmtEngine>` owns the persistent solver. The main `Engine` does not own a
solver, and there is no per-successor trait-object allocation.


Two lanes: (1) default `cargo test --release` without libz3; (2) a distinct
`CARGO_TARGET_DIR=target/smt-z3` build with `--features smt-z3`, the two brew variables above, and the
T fixture scoreboard. Separate target directories prevent a feature build from silently replacing
the default `target/release/tnk-repl`.

### 4.2 SMT number representation

SMT `Integer`/`Real` are **distinct sorts** from NAT/INT/RAT and their literals are their own NA
constructors (Maude: `SMT_NumberDagNode` holding `mpq_class`). tnk represents NAT/INT via the
S-theory and RAT structurally via `_/_`; neither is the right scalar payload here. Add
`NaValue::SmtNum(Rc<SmtNumber>)`, where `SmtNumber` is a private canonical
`malachite::Rational` wrapper with decimal numerator/denominator accessors. Extend `NodeRepr`,
hash/order/sort classification, static `Term`, and both pretty paths exhaustively.

The **symbol range sort** decides rendering: INTEGER prints only the numerator; REAL always prints
`num/den`, including denominator `1` (ref `termPrint.cc:217–245`). A dedicated SMT-number grammar
action accepts exactly the integer/rational token classes at the appropriate constructor and
canonicalizes once. Translation passes numerator/denominator strings to z3; it never converts
through a machine integer or float.

### 4.3 The SMT_Info analog

Build a per-module table at module-build time from the resolved SMT symbols (mirroring `fillOutSMT_Info`,
ref `SMT_Symbol.cc:156–186`): `SortId → SmtType {Boolean,Integer,Real}`, the conjunction symbol (`AND`),
the true symbol (`CONST_TRUE`), and per-kind equality symbol (`EQUALS`). The translation and the
constraint-builder read it. This is a small addition to the signature/build alongside the existing
special-op resolution — the data is already available from the `SpecialOp::Smt` arms.

### 4.4 `smt-search` fit with the search machinery

`smt-search` gets its **own** state machine in `tnk-core::smt`, not the hash-consing `Search`:
- `Vec<SmtState { term, constraint, avoid_var: Nat, parent, rule, depth }>` in creation order, with
  `RootGuard`s for both DAGs and no structural state collapse.
- A dedicated crate-internal engine seam enumerates the source-ordered `smt_rules` table ×
  non-extension root-match and returns the rule descriptor + substitution without running ordinary
  conditions. A second step binds every unbound rule slot to a `#n-Base` variable, instantiates
  equality fragments without reduction, solver-checks the clause, and only then constructs the RHS.
  Do **not** call ordinary `state_successors`, `reduce_successor`, `eval_goal`, or `drive_match` with
  its normal condition path.
- Per-state expansion uses one solver incrementally: `clear`, assert the accumulated constraint,
  then candidate `push`/assert/check/pop. One accepted rule application increments the rewrite count;
  there are no reduction rewrites.
- The goal is a linear, non-SMT pattern. Goal variables of SMT sorts retain their source name codes;
  their match bindings become equality clauses checked with the state constraint. The final printed
  constraint is accumulated-state ∧ match-constraint.
- The command builder must pass source variable names/codes for both rules and the goal because
  `Term::Var` stores only `(slot, sort)`. `continue` retains the search object and solver, mirroring
  `smtSearchCont`.
- All states, pattern-variable DAGs, pending fresh variables, and final constraints are rooted across
  callbacks and commands.

The **incremental push/pop pruning is precisely what the T0 spike P3 validated** as equivalent to a
fresh solver per node — so this composition is sound by the gate.

### 4.5 Shipping `smt.maude`

`smt.maude` is pure declarations, so T1 checks in a **byte-identical repository-root copy** of
`Main/smt.maude`. `load smt` finds it through the existing CWD/`$MAUDE_LIB` search with no
special-casing or compile-time embedding. The harness normally points `$MAUDE_LIB` at the oracle tree,
so T1 also needs a smoke run with `MAUDE_LIB=$PWD` to prove the shipped copy—not merely the reference
copy—loads. Pin its bytes/checksum in the T1 verification. Its `set include BOOL off/on` directives
already use the D11 path.

### 4.6 Meta surfaces (`metaCheck`, `metaSmtSearch`) — required

Ref `Main/prelude.maude:2977–2985`: `metaCheck : Module Term ~> Bool` maps SAT/UNSAT to meta
`true`/`false`; `Unknown` or `BadDag` leaves the redex unreduced. `metaSmtSearch : … ~> SmtResult?`
returns `{stateTerm, substitution, constraint, maxVariableNumber}` or `failure`. Its input fresh
counter is a `Nat`, and the returned counter is the largest `#n-Base` number used.

These `MetaOp` arms are mandatory T5 surface, not an optional follow-on. They reuse the existing
down/up module/term machinery, but `metaSmtSearch` must also use the persistent solution cache:
same/equal request reuses the result, a forward index resumes, a backward index restarts, and
exhaustion returns `failure`. The meta goal has the same no-SMT-operator/nonlinear-variable checks as
the object command. The one reference fixture exercises base `42`, bounded/unbounded search, result
construction, and cache progression.

### 4.7 Variant satisfiability: recovered oracle, separate Rust deliverable

This is **not SMT solving**. It decides quantifier-free equational formulas in the initial algebra of
an FVP decomposition whose constructor decomposition is OS-compact. It uses variant generation and
variant unification; it does not call z3, `check`, or `smt-search`, and does not depend on T1–T5 or M.

#### 4.7.1 Recovered primary evidence

The source/test tree still contains no implementation, but the manual's external prototype is no
longer missing:

- Official tool page: `https://maude.cs.illinois.edu/tools/var-sat/`.
- Official archive: `https://maude.cs.illinois.edu/tools/var-sat/var-sat-rel3.tgz`;
  SHA-256 `03f8f91362d90295ca9ae8497dd7dc7af3bc1d704ee7dce1679aa566983fce47`.
- Paper: Stephen Skeirik and José Meseguer, *Metalevel Algorithms for Variant Satisfiability*,
  DOI `10.1016/j.jlamp.2017.12.006`. The paper gives the decision procedure and its
  FVP/OS-compactness assumptions; the archive supplies a reflective Maude implementation and examples.
- The archive contains **1,246 lines** across the five core files `ctor-refine.maude`,
  `ctor-var-unif.maude`, `empty-fin-sorts.maude`, `var-sat.maude`, and `vs-wf-check.maude`, plus
  utility modules, 25 example theory files, 12 example drivers, Full Maude 2.7, and a bundled
  x86-64 Linux Maude executable. Its README recommends Maude 2.7 Alpha 108.
- The prototype-owned files carry **no explicit license**. The bundled Full Maude file has its own
  GPLv2-or-later notice, which does not establish a license for the prototype files. Until the owner
  records acceptable provenance, those files are executable/reference material only: do not copy,
  adapt, or check them into this repository.

The package is also not source-compatible with Maude 3.5.1. A live run loads enough to make
`vswf-check(nat-acu)` reduce to `true`, but the actual `var-valid` call remains partially reduced:
the prototype matches the old three-field `Variant` result while current `metaGetVariant` returns
`{term, substitution, familyQid, parent, moreInLayer}`. Full Maude view syntax has also drifted, and
the archive's nested relative loads rely on behavior tnk's current CWD/`MAUDE_LIB` loader does not
provide. The bundled ELF therefore remains the authoritative behavior oracle and must run in an
x86-64 Linux lane; “it loads under 3.5.1” is not an implementation shortcut.

#### 4.7.2 The actual algorithm

For each DNF branch `G /\ D`, where `G` contains equalities and `D` disequalities:

1. Compute a complete set of **constructor unifiers** for `G`. The prototype first obtains ordinary
   variant unifiers, then computes each result's most-general constructor instances (MGCI) by
   disjoint unification against a constructor-sort-refined signature.
2. Apply each constructor unifier to `D`, hygienically rename branch variables, normalize, and
   compute the finite complete set of **constructor variants** of the resulting disequalities.
3. Discard a branch containing a constructor disequality whose two sides are equal modulo the
   constructor theory.
4. Classify the remaining variables by finite versus infinite constructor sort. Enumerate the
   finitely many canonical ground representatives for finite-sort variables, streaming the Cartesian
   product. After each assignment, the OS-compactness theorem says a conjunction of consistent
   disequalities over only infinite-sort variables is satisfiable.
5. Short-circuit on the first satisfiable branch. `var-valid(M,F)` is
   `not var-sat(M, not F)` after formula normalization.

This is exactly the paper's reduction: constructor unifiers handle positive literals; constructor
variants plus OS-compact finite-sort instantiation handle negative literals. Solver-SMT concepts and
the z3 backend play no role.

#### 4.7.3 Supported contract and prototype defects

The public semantic precondition is not “any Maude module.” The input must be an FVP decomposition
with finitary `B`-unification and an OS-compact constructor decomposition. For the theorem-5
syntactic class, constructor axioms may be any ACCU combination except an associative-but-not-
commutative operator, and every typing in an overloaded family must carry the same axioms.
Membership axioms are outside the recovered implementation's domain.

The prototype's `vswf-check` is only advisory. It checks (1) no associative-without-commutative
operator and (2) constructor preregularity below the whole signature. It explicitly omits the
constructor-freeness-modulo-`B` check, defines but never invokes another same-arguments/different-
result check, and cannot establish the FVP assumption. Its finite-sort classifier calls
`modelCheck`; examples with identity axioms manually pass finite and infinite sort sets. The README
also says disjunction is unsupported even though the shipped code implements `\/` and uses it in an
example. Source plus executable behavior, not those stale README claims, define the oracle.

Production must therefore:

- preserve the theorem's precondition instead of returning a plausible Boolean for a definitely
  invalid module;
- implement every sound syntactic eligibility check available from the built signature and distinguish
  **rejected**, **proved by the supported syntactic class**, and **caller-preconditioned/unknown**
  internally;
- preserve the explicit finite/infinite-sort overloads for theories where automatic classification
  is not justified, rejecting overlapping, unknown, or falsely finite declarations;
- reject memberships and unsupported constructor axiom families explicitly; do not silently feed
  them to the algorithm;
- use no arbitrary variant bound. Termination is guaranteed by the declared FVP precondition, not by
  truncating a search and calling the partial answer complete.

#### 4.7.4 Bound implementation approach

Implement a **new native Rust decision procedure with a thin source-compatible Maude facade**.
The facade ships as repository-root `variant-satisfiability.maude`, defines `VAR-SAT-TOOL`, the
formula sorts/operators, and the prototype's documented entry points:

- `var-sat : FModule DNF -> Bool`;
- `var-sat : FModule SortSet SortSet DNF -> Bool`;
- `var-valid : FModule DNF -> Bool`;
- `var-valid : FModule SortSet SortSet DNF -> Bool`;
- `vswf-check : Module -> Bool`.

There is no invented REPL command; users invoke these with ordinary `red`, normally passing
`upModule(<name>, true)`. Formula syntax remains `==?`, `=!?`, `/\`, `\/`, and `~`.

The facade's top operators carry a dedicated meta descent hook. `MetaDescent` down-translates the
reflected module through the existing flatten/build path, converts the formula's meta-terms into that
object engine, calls `tnk-core::variant_sat`, and returns a Bool in the outer engine. Hook arguments
identify every formula constructor by symbol ID; the implementation must not dispatch on printed
names. Cache entries are structural and module-generation-sensitive, following the existing
variant/narrowing meta caches.

This choice is binding for T6 because it:

1. reuses the completed Rust `VariantSearch`, variant-unification, disjoint-unification, filtering,
   sort lattice, canonical DAG, and fresh-variable machinery directly;
2. keeps T6 independent of the unimplemented model checker and Full Maude;
3. replaces the prototype's reflective finite-sort model-checking construction with a direct,
   auditable graph analysis;
4. avoids copying unlicensed source and avoids importing the obsolete Full Maude 2.7 library/runtime;
5. avoids the archive's old variant tuple, reserved `#`/`@` sort names, and nested-loader assumptions.

The prototype remains the semantic oracle. No prototype source text or utility module enters
production. A pure-Maude reimplementation would preserve implementation rewrite counts better, but
would duplicate the Rust symbolic engine through reflection and retain every dependency above; that
is the wrong layer for this Rust rewrite.

#### 4.7.5 Internal shape

Keep the algorithm in `tnk-core` and the reflected-module adapter in `tnk-modules`:

- `variant_sat` owns a query-local formula AST, constructor-signature view, eligibility result,
  constructor variant/unifier adapters, finite-sort analysis, and the decision iterator.
- A cached **derived constructor engine** adds private refined sorts and constructor overloads once
  per object-module generation. Explicit ID maps translate only query terms/substitutions across
  engines; no `DagId`, `SortId`, or `SymbolId` crosses an engine boundary untyped. The cache avoids
  cloning a signature for every MGCI request.
- MGCI calls the existing disjoint-unifier in that derived engine, lifts refined sorts through the
  ID map, and composes substitutions with the ordinary variant result. Constructor unifiers and
  constructor variants retain only the existing most-general filtered frontier.
- Empty/finite-sort analysis runs over the constructor production graph. Empty sorts are a least
  fixpoint. Productive dependencies form the finiteness graph; a reachable productive cycle means
  infinite for the supported no-identity class. Finite ground terms are generated in topological
  order, canonicalized by the object engine, and deduplicated. Identity-bearing theories use the
  explicit override path unless a separate proof handles the collapse.
- Finite assignments and DNF branches are iterators, not materialized powersets. The implementation
  short-circuits on the first witness and roots every live DAG across allocation/GC.
- Fresh variables come only from `FreshVariableGenerator`; private refinement IDs eliminate the
  prototype's reserved-name convention.

---

## 5. Feasibility & risk (honest)

- **D7 incremental push/pop ↔ pruning gate — RESOLVED (low risk).** The T0 spike proved incremental ≡
  fresh over 894 randomized search-tree nodes with balanced assertion stacks. The `smt-search` state
  machine can mirror Maude's `VariableGenerator` seam directly (no adaptation layer).
- **Solver-independence — PROVEN (very low risk).** No model values are ever printed (§2.6). z3 vs
  Yices2 is byte-safe by construction. This removes the class of risk that dominated the BDD subsystem.
- **Feature-gate discipline — medium.** The placement and lane policy are now bound (§4.1/§7):
  optional z3 only in `tnk-core::smt::z3`, feature forwarded by `tnk-repl`, and a separate target dir.
  The default must still load the theory and parse/degrade both commands without linking libz3.
- **Dedicated source-rule table + match seam — the primary structural risk.** The reference fixture
  depends on an extra-RHS-variable `[nonexec]` rule that tnk currently skips before parsing. Populate
  `smt_rules` without admitting that rule to ordinary `CompiledRule`; preserve flattened source order,
  slot sorts, and source base names. Keep SMT matching root-only/non-extension/no-reduction. Reusing
  the ordinary successor path would silently produce wrong states and counts.
- **Byte-exact rendering — low/medium.** Verdicts are a token. Constraints use the ordinary mixfix
  printer once `smt.maude` syntax is present. New leaves are exact SMT numbers and `#n-Base` names
  from `smt.rs`. The doubled reference `"saw but saw"` BAD_DAG typo is in ignored diagnostics; the
  observable contract is no result line.
- **`undecided` mapping — low.** z3 `Unknown` and the null backend map to `undecided`; QF
  LIA/LRA/Boolean cases should decide.
- **Unseeded fixtures — immediate next work.** `tests/Misc/smtTest.maude` bundles all object/meta
  surfaces and restriction failures. Split it before code. Its `[4, 0]` command is an intentional
  parse rejection, not a `[:` token. Its `debug smt-search`/`step`/`resume` blocks belong to roadmap
  F4 and are an enumerated T exclusion; all non-debug `metaCheck`/`metaSmtSearch` blocks are required.
- **Validity fidelity — medium.** The gate includes the range-sort and rule-LHS restrictions omitted
  by the earlier plan (§2.5), plus different handling for unsupported command versus rule condition
  fragments. Seed every bottom-of-`smtTest` rejection case.
- **Variant-satisfiability provenance/domain — medium/high.** The official archive and algorithm are
  now pinned (§4.7), so source discovery is resolved. The prototype has no explicit license, targets
  Maude 2.7, omits a constructor-freeness check, and assumes FVP/OS-compactness. The bound native
  implementation avoids source reuse, but its eligibility boundary and old-oracle harness must be
  explicit and reproducible.

---

## 6. Implementation plan (staged)

Ordered; each stage lands with its now-passing fixture(s) and keeps F1–F4 green (working-rules §4).

- **T0 — spike + oracle (DONE).** z3 0.20.2 confirmed and the Yices2 oracle rebuilt
  (`reports/T0-smt-spike.md`).

- **T0a — fixture seeding (NEXT, before production code).** Split all non-debug SMT semantics from
  `tests/Misc/smtTest.maude`, add manual ch. 16 and bignum/rational probes, enumerate the F4 debugger
  exclusion, oracle-run every command, and freeze the T manifest in `subsystems-goal.md`.

- **T1 — SMT theory recognition + shipped `smt.maude`.** (Pure Rust; no solver yet.)
  1. `SpecialOp::Smt { op: SmtOp }` for the **25** C++ `OPERATORS`, including the arity-sensitive
     `"-"` split; marker-class `SMT_NumberSymbol` constructors for integers/reals.
  2. `NaValue::SmtNum(Rc<SmtNumber>)`, grammar actions, exact sorting/hashing, and printing (§4.2).
  3. `Signature::smt_info` with sort types, conjunction, true, and per-kind equality symbols.
  4. Check in and pin `smt.maude`. **Gate:** shipped-copy load smoke; all hooks recognized but
     intentionally reduction-inert; SMT leaf parse/print and ordinary `reduce` match the oracle;
     default F1–F4 green.

- **T2 — `SmtEngine` + z3 backend + `check`.**
  1. Pure trait/`SmtResult`/`NullSmtEngine`; cfg-gated `Z3Engine` and DAG translator in
     `tnk-core::smt`; workspace feature forwarding.
  2. Parse/dispatch/render `check` without equationally reducing its subject. BAD_DAG emits no result;
     null emits `undecided`.
  3. **Gate:** T01 Boolean byte-exact in the z3 lane; default command parses and degrades; both builds.

- **T3 — full `check` conformance.** TEST-B/I/R/RI, BAD_DAG, bignum coefficients, exact rationals,
  mixed coercions, and manual examples.

- **T4 — `smt-search`.** Add the dedicated source-ordered `smt_rules` descriptor table for all rules
  in SMT-aware modules, including nonexec/extra-RHS-variable rules, while leaving ordinary
  `CompiledRule` executable-only. Add the root/non-extension/no-reduction candidate seam, then the
  incremental state machine, rule/command constraint construction, goal match constraints,
  counters/rendering, restriction gate, and `continue`. **Gate:** all object search and rejection
  fixtures, exact order/counts/`#n-Base`/parentheses, plus default Null degradation.

- **T5 — mandatory meta surfaces.** Implement `metaCheck` and cached `metaSmtSearch`, including input
  and returned fresh counters, bounded/unbounded search, `SmtResult`/`failure`, and equal/forward/
  backward cache requests. **Gate:** every non-debug meta block from `smtTest`.

- **T6 — native variant-satisfiability + Maude facade (independent of T1–T5/M).**
  1. **T6a — provenance + executable oracle.** Pin the official URL/checksum above. In an x86-64
     Linux sandbox, run the untouched archive with its bundled interpreter from the documented
     working directory; freeze version, every command from the 12 example drivers, exit status, and
     result value/sort. Record that no prototype license was found. Do not vendor the archive.
  2. **T6b — contract fixtures before code.** Write independent minimal fixtures, not copies of the
     package examples: free equality-only sat/unsat; finite and infinite disequalities; mixed
     positive/negative literals; multiple constructor unifiers; disjunction and validity; overloaded
     constructor typings; AC, C, ACU, and one-sided-identity cases with explicit sort overrides;
     empty sort; no ground assignment; definitely invalid A-without-C, memberships, inconsistent
     constructor family axioms, and constructor-preregularity cases. Add helper-oracle probes for
     MGCI, constructor variants, constructor unifiers, finite sorts, and canonical representatives.
  3. **T6c — eligibility + constructor view.** Extract constructor declarations/axioms from the built
     signature; implement the prototype-compatible `vswf-check` result plus the richer internal
     eligibility classification. Build and generation-cache the derived refined constructor engine,
     with typed sort/symbol/DAG/substitution translation maps and collision-free private IDs.
     **Gate:** all rejection fixtures and constructor-refinement unit contracts.
  4. **T6d — constructor variants and unifiers.** Adapt `VariantSearch`,
     variant-unification, `meta`-equivalent disjoint unification, substitution composition, and
     `filter::subsumes` to implement MGCI, constructor variants, and constructor unifiers. Preserve
     deterministic family/solution order and root every cross-search DAG. **Gate:** helper fixtures
     match the pinned oracle on sets/order after the declared old-version normalization.
  5. **T6e — empty/finite sorts and representatives.** Implement the productive-constructor
     fixpoints/SCC analysis, canonical finite-term enumeration, and validated finite/infinite
     overrides. Unit cases cover empty sorts, singleton and multi-element finite sorts, subsorts,
     productive recursion, dead recursion, AC canonical deduplication, and identity override errors.
     **Gate:** no model-checker dependency and no materialized Cartesian product.
  6. **T6f — formula decision procedure.** Down-translate and validate formula literals, lazily
     normalize Boolean structure into DNF branches, solve positives with constructor unifiers,
     apply/rename/normalize negatives, enumerate constructor variants and finite assignments, test
     remaining disequalities, and implement validity by negation. Preserve short-circuit order and
     query-local state; no hidden bound or solver call.
  7. **T6g — facade + differential lane.** Ship one flat
     `variant-satisfiability.maude` defining `VAR-SAT-TOOL` and its hook contract; add the `MetaOp`,
     hook resolution, `MetaDescent` adapter/cache, and root-level load smoke. Extend the harness with
     side-specific silent prefixes: the oracle side loads the pinned package, while tnk loads the
     shipped facade, then both evaluate the same fixture body. **Gate:** all T6 values, result sorts,
     termination, helper sets, and declared ordering match; default `cargo build/test --release`
     remains independent of z3, Full Maude, model checking, and the downloaded archive.

---

## 7. Verification

- **Fixture seeding.** Split `tests/Misc/smtTest.maude` into `T01…` check-Boolean, `T02…`
  check-Integer, `T03…` check-Real, `T04…` check-RealInteger, `T05…` object search/restrictions,
  `T06…` metaCheck, and `T07…` metaSmtSearch, plus manual/fresh probes. T06/T07 are mandatory.
  Enumerate only the debugger block as an F4-owned exclusion. Oracle-verify each command against the
  Yices2 build before freezing the manifest.
- **Harness.** The z3 lane uses the existing `TNK_BIN` override—no fixture tags and no silent skips:
  `CARGO_TARGET_DIR=target/smt-z3 cargo build --release -p tnk-repl --features smt-z3` with
  `Z3_SYS_Z3_HEADER=/opt/homebrew/opt/z3/include/z3.h` and
  `Z3_LIBRARY_PATH_OVERRIDE=/opt/homebrew/opt/z3/lib`, then
  `TNK_BIN=target/smt-z3/release/tnk-repl tools/subsystems-scoreboard.sh -p T`.
  An aggregate subsystem run may use that superset binary. The default lane never asserts solver
  verdict fixtures; it runs F1–F4 plus dedicated parse/load/degrade smoke tests.
- **Normalization.** Existing diagnostic stripping applies. BAD_DAG and restriction warnings may
  differ until phase E, but absence/presence of command echoes, verdicts, solutions, counts,
  substitutions, states, and constraints remains byte-exact.
- **Unit contracts.** DAG→z3 translation for every `SmtOp`; exact number parse/print; variable cache
  key `(sort,name)`; `#n-Base` naming with bignum counters and `u32::MAX` non-slot index;
  retained-nonexec isolation; root-only rewrite; unsupported condition handling; balanced push/pop;
  cache forward/equal/backward/exhausted.
- **T6 oracle contract.** The 2016 executable is a semantic oracle, not a Maude-3.5 byte oracle:
  require exact Bool value, result sort, termination, canonical helper sets, and documented
  enumeration order. A native hook cannot reproduce the prototype's thousands of Maude-level
  rewrites; keep global normalization unchanged and record a narrow T6-only accepted difference for
  rewrite counts and old-version command wrapping. Never weaken the U/V/N/T1–T5 count contract.
- **T6 stress contracts.** Stream finite assignments and disjunction branches; prove bounded live
  roots on a large finite product with an early witness, no stale cache after module replacement,
  deterministic repeat output, and no z3/model-checker/Full-Maude linkage.
- **Pure-Rust invariant.** `cargo build --release` and `cargo test --release` without `smt-z3` remain
  green on a machine with no libz3.
- **Shipped copy.** Smoke `load smt` with `MAUDE_LIB=$PWD` and verify the checked-in file bytes against
  the pinned reference copy.

---

## 8. Bound decisions and remaining prerequisite

1. **Trait/placement — bound.** Solver operations only; fresh naming stays pure. The z3 backend is a
   cfg-gated `tnk-core` submodule and `tnk-repl` forwards the feature.
2. **Default degradation — bound.** Match the no-solver result semantics (`undecided` for valid
   `check`, no solutions for SMT search). Warning text waits for the single phase-E diagnostic sink
   instead of adding a one-off warning channel; diagnostics are outside the current byte contract.
3. **Scoreboard — bound.** Separate `target/smt-z3` binary selected through existing `TNK_BIN`;
   `-p T` is the z3-only denominator. No per-fixture skip metadata.
4. **Meta scope — bound.** T5 is required. “Full SMT semantics from `smtTest`” excludes only its
   debugger-owned F4 block, not `metaCheck`/`metaSmtSearch`.
5. **Number representation — bound.** `NaValue::SmtNum(Rc<SmtNumber>)`, not a new DAG variant and not
   the structural RAT representation. Preserve explicit INTEGER/REAL constant disambiguation.
6. **`smt.maude` shipping — bound.** Byte-identical filesystem copy at repository root, normal
   CWD/`$MAUDE_LIB` loading, no compiled-in special case.
7. **Variant-satisfiability source — resolved.** The official `var-sat-rel3.tgz` archive and paper
   are pinned in §4.7. The archive is an old executable oracle, not a file from the Maude 3.5 tree.
8. **Variant-satisfiability implementation — bound.** New native Rust core plus a thin
   `VAR-SAT-TOOL` Maude facade; no new REPL command and no prototype source reuse. T6 is independent
   of z3, T1–T5, M, and Full Maude.
9. **Variant-satisfiability provenance — bound conservatively.** No explicit license was found for
   the prototype-owned files. Do not vendor or adapt them unless the owner separately records
   acceptable provenance. Published algorithm + observed behavior are the implementation inputs.
10. **Variant-satisfiability parity — bound.** Exact semantic values/sorts/sets/order; a narrow,
    explicit accepted difference for native-vs-reflective rewrite counts and Maude-2.7 wrapping.
    Global harness normalization remains strict.
