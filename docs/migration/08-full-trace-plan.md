# Full Maude `trace` — implementation plan (resume document)

> **STATUS (2026-06-23) — COMPLETE. Phases 2–6 all done; the full `trace` surface ships.** Commits
> `0ef40cd` (P2 kernel `TraceEvent` stream) → `61cae43` (P3 frontend `eq_traces`/`mb_traces`) → `fe0b932`
> (P4+P5 REPL `TraceFlags` + the eq/built-in/membership/conditional renderer + a pretty-printer comma/
> bracket spacing fix) → P6 (this commit: `conformance/trace-*.maude` fixtures + docs). The REPL renders
> **byte-identically to the reference binary** (color off) for: user equations (header + `[c]eq … .` body +
> `Var --> binding` substitution + redex/`--->`/result), built-ins (`(built-in equation for symbol _+_)`),
> memberships (`mb … : … .` + `oldSort: t becomes newSort`), the **conditional sub-stream** (`trial #N` /
> `[re-]solving` / `success`/`failure for condition fragment` / `success`/`failure #N`, render-time trial
> numbering reset per command + stack-paired), and the granular **`set trace <option> on|off`** sub-flags
> (`body`/`substitution`/`rewrite`/`whole`/`condition`/`eqs`/`mbs`/`builtin`). **Faithful `set trace
> whole`** for equations (`Old:`/`New:` reconstructed from the reduce frame stack, gated + zero-cost off).
> Verified live against `~/Downloads/Maude-3/maude` over all of §1a–1e + the sub-flags; 5 inline + 1
> fixture-driven REPL tests lock it. **199 tests (104 core + 69 frontend + 10 modules + 16 repl); clippy
> `-D` clean; fib(22)=186579 at ~7 M rw/s** (the per-rewrite trace cost is an `if self.trace.is_some()`).
>
> **Documented deviations (none block correctness; none hit by any conformance fixture):**
> 1. **Command echo line** (`reduce in M : <echo> .`) — pre-existing `join_tokens` spacing (`g ( g ( a ) )`
>    vs Maude's `g(g(a))`); orthogonal to the trace (the trace lines are byte-identical). A REPL follow-up
>    (re-render the parsed command term).
> 2. **Membership `Whole:`** (the `whole` flag on a membership step) — Maude prints `Whole: <root>`; we omit
>    it. Our sort constraints fire *eagerly at node construction* (off the reduce frame stack, and — for the
>    initial term — before the whole term even exists), so the root isn't reconstructable there. Equation
>    `Old:`/`New:` is faithful.
> 3. **Multi-fragment `:=` backtrack** — exact for single-fragment conditions (all conformance fixtures) and
>    for backtracking that re-solves a *matching* fragment. The only gap: when backtracking crosses a
>    *deterministic* (equality/sort-test) fragment to re-solve an earlier matching fragment, Maude emits a
>    `re-solving`/`failure for condition fragment` pair for that deterministic fragment (it has no further
>    solutions); our recursive solver returns through it without re-emitting. Needs ≥3 fragments with a
>    multi-solution `:=` before a deterministic fragment. Result identical; only extra event lines in Maude.
>
> *(An earlier draft listed a fourth "variable index order" deviation — that was wrong: `Equation::check`
> indexes lhs→condition→rhs (rhs last, `equation.cc:74`), exactly our `load_statements` order; verified
> identical to the binary on the order-sensitive case. There is no variable-order deviation.)*
>
> Everything below is the original plan, kept for reference.

**Purpose.** Bootstrap the next session to finish the **full Maude reduction trace** in the REPL. This
doc is self-contained: it has the verified output spec, every code pointer, the Maude C++ references, and
the phase-by-phase plan. The work is partly done (the step trace + the Term pretty-printer); **Phases 2–6
below remain.**

Read order to re-acquire context: this doc → `docs/migration/07-stageB-plan.md` §2 B5 (Phase 1 is
complete; the REPL `tnk-repl` exists) → the code pointers in §"Our code map" below.

---

## 0. Status — what is already DONE

- **Step trace (commits `4590e0d` kernel / `97b9aab` repl).** `set trace on` in the REPL prints, per
  rewrite, `*********** equation` (or `*********** built-in`) + the redex + `--->` + the result. The
  redex/result lines are byte-identical to Maude. Kernel: a `trace: Option<Vec<TraceStep>>` on `Runtime`
  (off = zero-cost); `try_rewrite_top` records `(kind, before, after)`; `Engine::{set_trace, is_tracing,
  take_trace}`. REPL: a `trace: bool` flag + `set trace on|off`; `render_trace` renders the steps.
- **Phase 1 — Term pretty-printer (commit `dec8743`).** `crates/tnk-frontend/src/pretty.rs` now has
  `pub fn print_term(m: &BuiltModule, i: &Interner, t: &Term, var_names: &[String], color: bool) ->
  String`. It renders a static `Term` (an equation/membership LHS/RHS pattern, **with variables**) using
  the **same** mixfix prec/gather walk as the DAG printer — refactored via a private `trait Child` (impl
  for `DagId` → `print`, for `Term` → `print_term`) so the frag/hole loop (`print_mixfix`,
  `print_arg_list`) is shared, not duplicated. This is Maude's own split (`dagNodePrint` vs
  `MixfixModule::prettyPrint`). `Term::Var(v)` renders as `var_names[v.index]`. Verified:
  `add(s(X), Y)`, `X + Y + Z` (nested binary → flat), `0`.

**Why the step trace is not enough / what remains:** Maude's full trace also prints the **equation body**
(`eq lhs = rhs .`, via the Term printer — now available), the **variable substitution** (`X --> binding`),
**membership-axiom** steps, the **conditional-equation** trial/fragment sub-stream, and honours the
granular **`set trace <option> on/off`** sub-flags. The user opted into this whole surface.

---

## 1. The spec — Maude's exact output (captured from the reference binary)

Captured via `~/Downloads/Maude-3/maude -no-banner <file>.maude < /dev/null` with `set trace on .`
before a `red`. **Reproduce these to diff against during implementation.**

### 1a. User equation
```
*********** equation
eq d(X) = X + X .          <- the equation, via the Term printer over LHS/RHS
X --> 2                    <- the substitution: each LHS variable --> its binding (DAG printer; `2` = s s 0 as a SuccSymbol numeral)
d(2)                       <- the redex
--->
2 + 2                      <- the result
```

### 1b. Built-in (special op) — no body, no substitution
```
*********** equation
(built-in equation for symbol _+_)   <- the operator's canonical name
2 + 2
--->
4
```

### 1c. Membership axiom — a sort-narrowing, NOT a term rewrite
```
*********** membership axiom
mb s 0 : NzNat .                  <- the membership (Term LHS : target sort)
empty substitution               <- or `Var --> binding` lines if the mb has variables
Nat: s 0 becomes NzNat           <- `<oldSort>: <term> becomes <newSort>`
```

### 1d. Conditional equation (`ceq`) — a whole sub-stream (the `condition` flag)
```
*********** trial #1                        <- begin trying this conditional eq (trial counter)
ceq f(N) = 0 if z(N) = tt .                 <- the ceq (Term printer; note `ceq … if …`)
N --> 0                                     <- substitution so far
*********** solving condition fragment      <- begin a condition fragment
z(N) = tt                                   <- the fragment (Term printer); for `:=` it's `pat := subj`, sort-test `t : S`
  …nested equation steps for z(0) --> tt…   <- the fragment's own reduction traces normally
*********** success for condition fragment
z(N) = tt
N --> 0                                     <- substitution after the fragment (may bind fresh vars)
*********** success #1                       <- the trial succeeded
*********** equation                         <- …then the eq fires as a normal equation step:
ceq f(N) = 0 if z(N) = tt .
N --> 0
f(0)
--->
0
```

### 1e. Sub-flags (`set trace <option> on|off`) — each controls a section
```
# `set trace substitution off` drops the `X --> …` lines:
*********** equation
eq d(X) = s s X .
d(0)
--->
s s 0

# `set trace whole on` adds Old:/New: the WHOLE term before/after:
*********** equation
eq d(X) = s s X .
X --> 0
Old: d(0)
d(0)
--->
s s 0
New: s s 0
```

**Flag → section map** (Maude `Interpreter` flags, `interpreter.hh:96-107`):
| Flag | Section it gates |
|---|---|
| `TRACE` (master) | everything; `set trace on/off` |
| `TRACE_BODY` | the `*********** <kind>` header **and** the `eq …`/`mb …`/`ceq …` body line |
| `TRACE_SUBSTITUTION` | the `Var --> binding` lines |
| `TRACE_REWRITE` | the `redex` / `--->` / `result` lines |
| `TRACE_WHOLE` | `Old:`/`New:` whole-term lines |
| `TRACE_CONDITION` | the `trial`/`solving fragment`/`success` sub-stream |
| `TRACE_EQ` / `TRACE_MB` / `TRACE_BUILTIN` | whether equation / membership / built-in steps trace at all |
| (`TRACE_RL`, `TRACE_SD`, `TRACE_SELECT`) | rules / strategies / selected-symbols — **Phase 2 of the project; defer** |

Maude **defaults** (observed): with `set trace on`, body+substitution+rewrite+eq+mb+builtin are ON,
whole OFF, condition ON (the ceq sub-stream shows by default). The `set trace <option> on|off` toggles a
single flag.

`set trace <option>` grammar (Maude `Mixfix/commands.yy:626-637`): options are `condition`, `whole`,
`substitution`, `select`, `mbs`, `eqs`, `rls`, `sds`, `rewrite`, `body`, `builtin` (bare `set trace
on|off` = the master).

---

## 2. Maude C++ references (the source to draw from)

Root: `/Users/dai/code/maude-lang/Maude/src`.

- **`Mixfix/userLevelRewritingContext.cc`** — the trace printing:
  - `tracePreEqRewrite(redex, equation, type)` (≈138-211) + `tracePostEqRewrite(replacement)` (≈214-225):
    the eq/built-in step. `header[] = "*********** "`. `cout << header << "equation\n"` (gated by
    TRACE_BODY); `if (equation==0 && type==BUILTIN) cout << "(built-in equation for symbol " <<
    redex->symbol() << ")\n"` else `cout << equation` (the eq body) + `printSubstitution(...)`; then
    `cout << redex << "\n--->\n"` (pre, TRACE_REWRITE) and `cout << replacement` (post). `TRACE_WHOLE`
    adds `"Old: " << root()` / `"New: " << root()`.
  - membership: `tracePreScApplication` (≈487) → `cout << header << "membership axiom\n"`.
  - conditional sub-stream: `traceBeginTrial` / `traceBeginFragment` / `traceEndFragment` /
    `traceBeginEqTrace`-style hooks (grep `trace.*[Tt]rial`, `[Ff]ragment` in this file).
  - `printSubstitution(substitution, varInfo, ignored)` (≈542-571): loops `varInfo.index2Variable(i)`
    (a `VariableTerm`, a `NamedEntity`) and `substitution.value(i)`, printing `v << " --> " << d`.
    Variable name = `Token::name(namedEntity->id())` (`Mixfix/global.cc`).
- **`Mixfix/interpreter.hh:96-107`** — the `TRACE_*` flag enum.
- **`Mixfix/commands.yy:626-637`** — `set trace <option>` parsing.
- **`Core/rewritingContext.hh`** — the virtual `tracePre/PostEqRewrite` declarations (the hook seam).

Our analog of Maude's `RewritingContext` trace hooks is the `trace: Option<Vec<TraceEvent>>` buffer +
recording calls in the reduce loop / condition solver (we render **after** `reduce` returns, not
interleaved — same content for finite reductions; see §6).

---

## 3. Architecture (the plan)

Maude prints during reduction via flag-gated hooks; we **record a structured event stream** in the
kernel (off-by-default) and **render it after `reduce` returns** in the REPL per the flags. Render-after
avoids borrowing the `&mut` engine mid-reduce and keeps the pretty-printer in the frontend layer; the
content is identical for finite reductions. Three layers:

1. **Term printer** — DONE (§0 Phase 1).
2. **Kernel** (`tnk-core`): replace the flat `TraceStep` with a `TraceEvent` enum; assign stable ids to
   equations + memberships; capture the substitution; hook the condition solver. (Phases 2 & 5.)
3. **Frontend metadata + REPL flags/render** (`tnk-frontend` + `tnk-repl`): store per-equation/membership
   LHS/RHS/condition Terms + variable names keyed by the kernel ids; a `TraceFlags` struct; render the
   event stream to Maude's format. (Phases 3 & 4.)

---

## 4. Phase plan (each a verified commit; order matters)

### Phase 2 — Kernel trace-event stream  (`crates/tnk-core/src/engine.rs`, `term.rs`)
Replace `pub struct TraceStep` / `pub enum TraceKind` with:
```rust
pub enum TraceEvent {
    Rewrite { kind: RewriteKind, eq_id: Option<u32>, before: DagId, after: DagId, bindings: Vec<Option<DagId>> },
    Membership { mb_id: u32, subject: DagId, old_sort: SortId, new_sort: SortId, bindings: Vec<Option<DagId>> },
    // Phase 5 adds: TrialStart{eq_id,trial,bindings}, FragmentStart{eq_id,fragment}, FragmentSuccess{eq_id,fragment,bindings}, TrialSuccess{trial}
}
pub enum RewriteKind { Equation, BuiltIn }
```
- `Runtime.trace: Option<Vec<TraceStep>>` → `Option<Vec<TraceEvent>>`. `Engine::take_trace ->
  Vec<TraceEvent>` (rename or keep). Keep `set_trace`/`is_tracing`.
- Give each `CompiledEquation` (engine.rs ≈28) an `id: u32`; each `SortConstraint` (≈42) an `id: u32`.
  Add `next_eq_id`/`next_mb_id` counters to `Signature` (≈95). `push_equation` (≈572) /
  `push_membership` assign + **return** the id; `Engine::{add_equation, add_conditional_equation,
  add_owise_equation, add_membership, add_conditional_membership}` (Engine ≈1671) **return `u32`**
  (existing callers — tests/peano — ignore it).
- **Record `Rewrite`**: move equation recording OUT of `try_rewrite_top` (≈1266, currently records
  `TraceKind::Equation` after `try_equations` returns) and INTO `try_equations` at the accept point
  (≈1358-1367): there `eq` (→ `eq.id`), `subst`, `id` (redex), and the built result are all in scope.
  Snapshot the substitution: `(0..eq.nr_vars).map(|i| subst.get(i)).collect()` (`Subst::get` is pub,
  term.rs ≈128). Keep the **built-in** recording in `try_rewrite_top` (the `try_special` arm,
  `eq_id: None`, empty bindings).
- **Record `Membership`** in `constrain_to_smaller_sort` (≈682-728; the `rewrite_count += 1` at ≈695 is
  the application point): capture the subject node, its old sort, the mb's target (new) sort, the
  mb.id + the mb's substitution. (The mb match's `subst` is local there — thread it out or snapshot at
  the application.)
- **GC**: `safe_point_gc` (≈1090) already roots the trace's `before`/`after`; extend it to root each
  event's `bindings` + `subject` ids (collect-first to avoid the `&self.trace` vs `&mut self`
  borrow clash, as the existing code does).
- **Tests + perf**: a kernel test asserting the events of a small reduction; **re-verify fib(22)=186579
  at ~7 M rw/s** (`cargo run --release --example peano 22 1 100`) — the per-rewrite cost must stay an
  `if let Some` when off.

### Phase 3 — Frontend trace metadata  (`crates/tnk-frontend/src/sig/syntax.rs`, `load.rs`)
- `BuiltModule` (sig/syntax.rs ≈38) gains `eq_traces: Vec<EqTrace>` + `mb_traces: Vec<MbTrace>` (indexed
  by the kernel ids — per-module ids start at 0, dense):
  ```rust
  pub struct EqTrace { pub lhs: Term, pub rhs: Term, pub condition: Vec<ConditionFragment>, pub var_names: Vec<String>, pub owise: bool }
  pub struct MbTrace { pub lhs: Term, pub sort: SortId, pub var_names: Vec<String> }
  ```
- `load_statements` (load.rs ≈59-106) has, per statement, the built `lhs_t`/`rhs_t`/`condition` Terms and
  the per-statement `VarIndex` (`vars`). **Before** calling the kernel `add_*` (which moves the Terms),
  clone them + capture `var_names = (0..vars.count()).map(|i| vars.name(i).to_string()).collect()`
  (`VarIndex::{count,name}` are pub, build_term.rs ≈25). Store at the **returned id**:
  `assert_eq!(id as usize, m.eq_traces.len()); m.eq_traces.push(EqTrace{…})`. Same for `mb`.
  - `ConditionFragment` (term.rs ≈97) is the pre-compilation, Term-based condition the frontend builds
    in `parse_condition` (load.rs) — clone it for the EqTrace so the `ceq … if …` line + the condition
    fragments can be Term-printed.

### Phase 4 — REPL trace flags + eq/built-in/membership render  (`crates/tnk-repl/src/lib.rs`)
- Replace the `Repl.trace: bool` with a `TraceFlags` struct (master + body/substitution/rewrite/whole/
  condition/eq/mb/builtin; Maude defaults from §1e). `meta_set` parses `set trace [<option>] on|off`
  (current `meta_set` only does the stub + master). `set trace on|off` = master.
- `render_trace(events: &[TraceEvent], lm: &LoadedModule, flags)` walks the events:
  - `Rewrite{kind: Equation, eq_id: Some(id), …}`: look up `lm.built.eq_traces[id]`; print (gated by
    flags) `*********** equation` + `[c]eq {print_term(lhs)} = {print_term(rhs)}[ if {print fragments}] .`
    + the `var_names[i] --> print_pretty(bindings[i])` substitution + `Old:` + redex + `--->` + result +
    `New:`. Use `print_term(&lm.built, i, &lhs, &eqt.var_names, color)` for the body, `print_pretty` for
    the bindings/redex/result/whole, `engine.sorts().name(...)` for sorts.
  - `Rewrite{kind: BuiltIn, eq_id: None, …}`: `*********** equation` + `(built-in equation for symbol
    {name})` (name = `lm.built.engine.symbol(lm.built.engine.node(before).symbol()).name()` — the
    canonical mixfix name, e.g. `_+_`) + redex/result.
  - `Membership{mb_id, subject, old_sort, new_sort, bindings}`: `*********** membership axiom` +
    `mb {print_term(lhs)} : {sort_name} .` + substitution (or `empty substitution`) +
    `{old_sort_name}: {print_pretty(subject)} becomes {new_sort_name}`.
- The reduce path in `run_command` (lib.rs) already does `set_trace(self.trace)` + `take_trace()`; change
  to use the flags (master) + render via the new `render_trace`. Drop the old `TraceStep` renderer.
- **Diff vs the binary** for §1a/1b/1c + the §1e sub-flags. Byte-identical for body/subst/redex/result/
  sort lines.

### Phase 5 — Conditional-equation events  (`tnk-core` condition solver + `tnk-repl` render)
- Find the condition solver: `condition_holds` / `solve_condition` (B2.3, engine.rs — grep
  `condition_holds`, `solve_condition`). It is a recursive backtracking solve over `CompiledFragment`s.
- Emit, when tracing: `TrialStart{eq_id, trial, bindings}` when beginning to try a conditional eq's
  solution (trial counter increments per solution attempt); `FragmentStart{eq_id, fragment}` before each
  fragment; `FragmentSuccess{eq_id, fragment, bindings}` when a fragment holds; `TrialSuccess{trial}`
  when all fragments pass (just before the eq fires). The fragment's own reduction (`reduce` on an
  equality fragment) already records its nested `Rewrite` events between Start and Success.
- REPL `render_trace`: render the §1d sub-stream from these events (gated by `condition`); the firing eq
  is the subsequent `Rewrite{Equation}` event. The fragment text is Term-printed from the EqTrace's
  `condition` fragments (`Equality{lhs,rhs}` → `{lhs} = {rhs}`; `Matching{pattern,subject,…}` →
  `{pattern} := {subject}`; `SortTest{term,sort}` → `{term} : {sort}`).
- Diff the §1d `ceq` format vs the binary.

### Phase 6 — Verify, commit, docs
- `cargo test` all four crates + `cargo clippy --all-targets -- -D warnings`; fib(22)=186579.
- Diff every format (§1a–e) against the binary.
- Sync `docs/migration/07-stageB-plan.md` (full trace done) + the memory file `maude-rust-migration.md`.

---

## 5. Our code map (file:line — confirmed this session)

**`crates/tnk-core/src/engine.rs`**
- `Runtime` struct ≈115 (has `trace: Option<Vec<TraceStep>>`); `TraceStep`/`TraceKind` ≈117-130;
  `trace_step` helper ≈1300; `Engine::{set_trace,is_tracing,take_trace}` ≈1775-1787.
- `CompiledEquation` ≈28 `{ lhs: LhsAutomaton, rhs: Term, nr_vars: u32, condition: Vec<CompiledFragment>, owise: bool }`.
- `SortConstraint` ≈42 `{ lhs: LhsAutomaton, sort: SortId, nr_vars, condition }`.
- `Signature` ≈95 `{ sorts, symbols, equations: HashMap<SymbolId, Vec<CompiledEquation>>, memberships: HashMap<SymbolId, Vec<SortConstraint>>, eq_epoch }`.
- `add_equation`/`add_conditional_equation`/`add_owise_equation` (Engine ≈1671; Signature ≈543);
  `push_equation` ≈572; `add_membership`/`add_conditional_membership`; `push_membership`.
- `constrain_to_smaller_sort` ≈682-728 (membership application; `rewrite_count += 1` ≈695).
- `try_rewrite_top` ≈1266 (records BuiltIn via `try_special`, Equation via `try_equations`); the eq
  trace recording to MOVE is at ≈1326/1330. `try_equations` ≈1341; accept point ≈1358-1367.
- `safe_point_gc` ≈1090 (roots frames + child_result + trace ids).
- condition solver: grep `condition_holds` / `solve_condition`.

**`crates/tnk-core/src/term.rs`**
- `Term` ≈20 `Var(Var{index:u32,sort:SortId}) | Op{symbol:SymbolId, args:Vec<Term>}`; `Term::{var,op,constant}`.
- `Subst` ≈115 `{ bindings: Vec<Option<DagId>> }`; `get`/`reset` pub, `bind`/`unbind` pub(crate).
- `ConditionFragment` ≈97 `Equality{lhs,rhs} | SortTest{term,sort} | Matching{pattern,subject,fresh_vars}`.

**`crates/tnk-frontend/src/pretty.rs`** — `print_raw`/`print_pretty`/`print_term` (DONE); the `Printer`
struct + `Child` trait + shared `print_mixfix`/`print_arg_list`.
**`crates/tnk-frontend/src/build_term.rs`** — `VarIndex` ≈25 `{ entries: Vec<(String, SortId)> }`;
`index_of`/`count`/`name` pub.
**`crates/tnk-frontend/src/load.rs`** — `load_statements` ≈59-106 (per-statement `VarIndex` + Terms +
`add_*` calls); `build_loaded_module` ≈47; `reduce_command` ≈277; `match_command`/`format_matchers`.
**`crates/tnk-frontend/src/sig/syntax.rs`** — `BuiltModule` ≈38 `{ engine, name, sorts, ops, syntax,
vars, statements, nat_succ, nat_zero, string_sym, float_sym, qid_sym, minus_sym }` (add `eq_traces`/`mb_traces`).
**`crates/tnk-repl/src/lib.rs`** — `Repl` (`interner, db, modules: HashMap<String,LoadedModule>, order,
current, color, trace: bool`); `eval`; `run_command` (the reduce arm sets `engine.set_trace(self.trace)`
+ `take_trace()` + renders); `meta_set` (`set trace on/off` → `self.trace`); `render_trace` (the current
step renderer — replace); `input_complete`.

---

## 6. Design notes / decisions (carry forward)

- **Render-after, not interleaved.** The kernel records events; the REPL renders after `reduce` returns
  (the engine is `&mut` during reduce; the pretty-printer needs `&BuiltModule`). Content is identical for
  finite reductions. The intermediate (redex/binding/subject) node ids stay valid because the REPL runs
  with in-reduction GC **off** (`gc_interval = None`); `safe_point_gc` still roots them for correctness.
- **ids are per-module** (each module's `Engine` has its own `Signature`/counters starting at 0), so the
  frontend's `eq_traces`/`mb_traces` `Vec`s are dense and `eq_id`-indexed.
- **`Old:`/`New:` whole-term**: Maude prints the in-progress whole term (`root()`); our render-after model
  shows the command's start/end term instead (documented deviation — minor).
- **Term printer style for bodies**: `print_term` uses the mixfix syntax (no compact numeral / `-3`
  faithful forms — those are DAG-value-only; Terms are successor chains rendered via `s_` syntax). This
  matches Maude's equation rendering.
- **Conditional body line**: prefix `eq`/`ceq` and append ` if <fragments>` only when the eq is
  conditional (the EqTrace `condition` is non-empty); `owise` eqs append ` [owise]` (check Maude's
  rendering when you get there).
- **Deferred (Phase 2 of the project / noted):** rule/strategy/narrowing tracing (`*********** rule` /
  `strategy call` / `narrowing step`) — needs rules; `trace select` (trace only chosen symbols);
  `trace sd`.

## 7. Verification commands

```sh
# build + test + lint + perf
cargo test -p tnk-core -p tnk-frontend -p tnk-modules -p tnk-repl
cargo clippy --all-targets -- -D warnings
cargo run --release --example peano 22 1 100      # expect fib(22) = 17711 (186579 rewrites), ~7 M rw/s

# capture Maude's reference trace to diff against (put a module + `set trace on .` + `red …` in a file):
~/Downloads/Maude-3/maude -no-banner <file>.maude < /dev/null
# drive our REPL non-interactively (it reads stdin; eval() in lib.rs is the testable, terminal-free path):
printf 'fmod … endfm\nset trace on .\nred … .\nquit\n' | cargo run -q -p tnk-repl
```

The §1 modules (`d(X)=X+X` with NAT special ops for built-in; the `mb s 0 : NzNat` module; the
`ceq f(N)=0 if z(N)=tt` module) are the diff fixtures — re-create them or add as `conformance/trace-*.maude`.
