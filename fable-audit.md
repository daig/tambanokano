# Migration audit — tnk vs Maude 3.5.1 (2026-07-01)

> **Ledger state (2026-07-05, correctness goal `docs/migration/correctness-goal.md`):** every finding
> in the goal's frozen manifest is closed — `tools/audit-scoreboard.sh` = **74/74 PASS**, the legacy
> corpus is **87/87 CLEAN** (`tools/legacy-sweep.sh`; two counts-only recorded divergences of the
> §3.3 [D] matchrew/exploration-schedule class are flagged for user review in
> `conformance/accepted-diffs/README.md`), `cargo test --release` fully green, and the stock
> `term-order.maude` / `machine-int.maude` / `linear.maude` load clean through the binary. Findings
> below carry per-item `RESOLVED (<commit>)` annotations; still-open items are the out-of-scope
> subsystems (§2/roadmap E–G) and the §3.7 cosmetic classes.

Independent differential audit of the Rust port against the C++ oracle (`maude` 3.5.1 on PATH; source at
`~/code/maude-lang/maude`, same version). Method: a shared normalizing diff harness (strips only `====`
separators, banner, `Bye.`, timing tails, and the two documented LEXICAL/LOOP-MODE build errors); roughly a
thousand differential runs across seven surface-area sweeps (the 231-test C++ suite, equational theories,
builtins, module algebra, commands, syntax/printing, dynamics/meta) plus main-session architecture probes;
every headline finding reproduced with a minimal case through both binaries (the highest-severity ones
re-verified independently of the sweep that found them). Repo docs (`docs/migration/*`) were used as leads
only — several claims were found stale in both directions (too pessimistic: ACU value printing, kind-sort
declarations, erewrite round-robin all now conform; too optimistic: collapse-at-top "value same",
`metaPrettyPrint` done, flatten "counts only"). The port's own test suite is green (312/312) and its 88
conformance fixtures were re-diffed against the live oracle.

**Bottom line.** The core engine — reduction, all four axiom-theory matchers on their common paths, sorts/
memberships, rules/search/strategies, the data-type builtins, the module algebra on its exercised paths, and
the implemented META-LEVEL descent surface — is genuinely conformant on values, sorts, AND rewrite counts to
a degree that is rare for a port of this scale (byte-identical output across most of the fixture corpus and
most fresh probes, including exact MT19937 RANDOM sequences and byte-exact 80-column line wrapping). The
gaps are just as real: the REPL/tool surface accepts only a fraction of Maude's command language and rejects
whole classes of legal input (most damagingly: implicit BOOL, `load`, several literal token classes,
non-ground reduce, statement labels), a handful of silent wrong-value bugs exist in the builtins, identity
matching, renaming, and redefinition, three classes of Rust panic can kill a session, and one architectural
choice — re-parsing imported statements in the importer's grammar — makes module validity context-dependent
in a way Maude's semantics forbids (it already breaks two stock library files). Detailed inventory below.

---

## 1. Where we stand — completed and verified conformant

Everything in this list was re-verified against the live oracle this session (not taken from repo docs).

- **Functional + system modules end to end.** `fmod`/`mod`/`fth`/`th`/`smod`/`omod`/`oth`, equations
  (`eq`/`ceq` with `=`/`:=` fragments), memberships, rules (`rl`/`crl` incl. `=>` conditions), `owise`,
  `nonexec`, `frozen`, `ctor`, `iter` (print side), `strat` laziness (values AND counts), `format`
  directives, `metadata`/`label` (trailing form).
- **The real 3.5.1 prelude loads** except `LEXICAL` and `LOOP-MODE` (documented). All data types work:
  NAT/INT/RAT/FLOAT/STRING/QID/CONVERSION/RANDOM (exact MT19937 seed-0 sequence)/COUNTER/BOUND; containers
  LIST/SET/MAP/ARRAY incl. parameterized instantiation; ~360 builtin edge-case probes conformant outside the
  bugs in §3.
- **Theories.** Free/AC/ACU/AU/C/CUI/S matching on confluent common paths: values, sorts, counts. Non-linear
  AC, cross-argument bindings, free/AC/AU alternation, extension matching at the top of larger subjects,
  two-sided `id:` with assoc/comm, `comm idem`/`assoc comm idem`, preregularity least-sort picks, error-sort
  (kind) terms inside AC.
- **Module algebra on its main paths.** Summation `M + N`, diamond imports, sort renames, prefix-target op
  renames + attribute clauses + collision/double renames, special hooks surviving renames, structured-sort
  renames, op→op prefix views, op→term constant views, inclusion views, multi-parameter modules, bound
  parameters, parameterized/nested views, default views (`LIST{Nat}`), chained instantiation — all
  conformant. (The mixfix-rename/view breakage in §3.2 is the counterpoint.)
- **Commands that exist are mostly right.** `reduce`/`rewrite [n]`/`frewrite`/`erewrite [n,g]`/
  `search =>* =>1 =>+` (+ `such that`)/`continue`/`srewrite`/`dsrewrite`/`match`(values)/`select`/
  `show path N`/`show search graph`/`set trace on|off` — byte-identical modulo the documented timing tail.
- **Dynamics internals verified conformant** (beyond the fixtures): rewrite's per-symbol round-robin rule
  cursor and `rew [1]` + `continue 1` ≡ `rew [2]` trajectories; frewrite position fairness on free ops;
  rewrite-condition counts incl. nested search (305-rewrite composite exact); search state hash-consing
  incl. states that become equal only after reduction; erewrite spawn/kill/stuck-message handling AND
  **per-message-symbol round-robin — the gaps.md item claiming it missing is stale, it now conforms**;
  strategy `sd` recursion is cycle-safe where it could hang; *nested* meta (`metaReduce` inside an
  equation) computes with exact counts.
- **Strategy language** (per repo suite + fresh probes): full combinator surface, solution values/order/
  per-solution counts, both srewrite and dsrewrite.
- **META-LEVEL descent surface**: the descent family, up*/down maps, sort/kind queries, metaParse/
  metaPrettyPrint on binary-nested inputs — including `upModule` of an *instantiated* parameterized module
  (`upModule('LIST`{Nat`})` is byte-identical). The flat-assoc reader gap and parameterized-module
  up-translation losses are in §3.2.
- **Objects**: `omod` desugaring, class completion, plain and object-message-fair `erewrite` on the
  bank/ping-pong shapes, STD-STREAM scripted IO.
- **Robustness beyond Maude in two spots** (divergence in tnk's favor): a 300k-deep term reduce+print works
  where Maude segfaults (exit 139); `modExp(x,y,0)` is left unreduced where Maude dies with SIGFPE (exit
  136). Deep recursion `f^3000`, 5000-char tokens, 500-op modules: all fine.
- **Performance**: same order of magnitude on small free-theory loads; ~5–6x slower than Maude on a
  builtin-NAT-heavy fib (2.6M vs 14.5M rw/s); counts byte-identical. See also the super-linear large-term
  issue in §3.5.

## 2. Intended features not built yet

Whole subsystems (all planned in `roadmap.md`, all failing *gracefully* today with clear errors):

- **Unification / variants / narrowing** (`unify`, `variant unify/match`, `get variants`, `vu-narrow`,
  `fvu-narrow`) — commands rejected cleanly; META declarations present but inert.
- **SMT** (`smt-search`, `check`; `smt.maude` needs `SMT_Symbol`) and the **model checker**
  (`model-checker.maude`: `SatSolverSymbol`/`ModelCheckerSymbol`).
- **Meta-interpreters** (`metaInterpreter.maude`: `InterpreterManagerSymbol`).
- **External IO beyond STD-STREAM** — `file`/`socket`/`process`/`time`/`prng` managers. Note: per the revised
  D5 decision (2026-06-30) these are now *intentionally out of scope for the engine* (host-embedding model);
  the audit records the consequence: existing Maude IO programs will not run unmodified, and `process.maude`
  additionally trips over the missing `sload`.
- **LOOP-MODE / LEXICAL** (the two prelude modules that don't build), Full Maude, LaTeX output.
- **`memo`** (parsed, ignored) and the **Diophantine/bipartite AC matcher** (naive backtracking stands in;
  plan exists in `ac-matcher-plan.md`).
- **Tracing inside `search`** (and inside a rewrite-condition's nested `=>` search): with `set trace on`,
  Maude prints the per-rule trace blocks during the search; tnk prints none (verified — results and counts
  unaffected). `reduce`/`rewrite` tracing itself conforms.
- **`xmatchrew`** (extension-match *rewriting*) and **conditional strategy definitions (`csd`)** — both
  error clearly at resolve time (verified; parser state survives). For the eventual fixes: `xmatchrew`
  needs the engine to expose an extension match's *residue* so the rewritten matched portion can be
  reassembled (assoc/AC only); `csd` needs runtime condition bindings to flow into the definition body —
  the syntactic parameter-token substitution that powers `sd` cannot express that.
- **Sort-decision diagrams**: least sorts are computed by direct down-set-GLB iteration per application,
  not Maude's precompiled flattened sort diagrams — same results everywhere this audit looked; a
  per-application throughput item only.
- **Command/REPL surface** — the biggest not-built area by count (~20 command families):
  - `load`/`in`/`sload`/`pwd`/`cd`/`ls`/`popd`/`eof`: **no file commands at all** (breaks nearly every
    real-world multi-file spec, incl. two stock library files).
  - `parse`, `debug` family (`debug reduce`, `resume`/`abort`/`step`/`where`), `trace select/exclude`,
    `break select`, profiling (`set profile`, `show profile`), `do clear memo`.
  - Most of `show`: `show all/sorts/kinds/ops/vars/mbs/eqs/rls/summary/components/desugared` are stubs;
    `show module` prints a flattened internal summary (no attributes, imports, statements, or `endfm`;
    everything renders as `fmod`) — the introspection surface is essentially absent.
  - The **entire `set print` family is silently inert** (`flat`, `with parentheses`, `number`, `rat`,
    `graph`, `conceal`, `attribute`, statement `print` attributes) — accepted, no effect.
  - `set include BOOL on/off` (see §3.4 — the `on` direction is the implicit-BOOL gap), `set verbose`,
    `set clear …`, `set break` — silent no-ops.
  - CLI flags: none exist (`-no-banner`, `-no-prelude`, `-batch`, `-random-seed`, … are read as a filename).
- **Kind-level on-the-fly variables** `X:[Foo]` in command terms (kind sorts in declarations DO work).
- **Interrupts**: no Ctrl-C abort of a running reduction.
- **Diagnostics**: Maude's warning/advisory surface (preregularity, collapse-at-top, ambiguity, import
  hygiene, "discarding module", …) is entirely absent. Where Maude warns-and-continues, tnk is silent (or
  hard-errors — see §3.4). This is a cross-cutting feature gap, not one bug.

## 3. Behavioral deviations (same input, different outcome)

Ordered by severity. **[N]** = novel (absent from the pre-audit `gaps.md`, whose verified content is now
folded into this document — the file itself is deleted); **[D]** = was documented there; **[D↑]** =
documented but materially understated. Every item verified with the minimal repro shown.

### 3.1 Session-killing crashes (Rust panics)

- **[N] Iter pattern with a pre-bound variable panics.** **RESOLVED (ee20fa7).** `eq f(X, s X) = z .` (`s_` is `[iter]`), then
  `reduce f(z, s z) .` → panic `s.rs:222 "non-linear S variable is not yet supported"`. Maude: `z`. Any
  non-linear equation over an iter constructor kills the whole session.
- **[N] Op-decl underscore/arity mismatch panics.** **RESOLVED (8b4522e).** `op _+_ : A A A -> A .` loads silently, first use panics
  (`engine.rs:1385` arity assert); a 3-hole unary op panics at module build (`grammar/build.rs:170`).
  Maude warns at load and disables the op. A one-character typo is a hard crash.
- **[N] Unbound right-hand-side variable panics.** **RESOLVED (a2d6c86).** `eq wrap(A:S) = B:S .` is *accepted* at load (Maude warns
  and leaves the term unreduced); `reduce wrap(x) .` → panic `term.rs:371 "unbound variable in
  instantiation"`, process exit. Reachable through parameterized instantiation (the documented
  build-at-instance deferral makes the instance the first checkpoint).
- **[N] Non-terminating rewrite-*condition* recursion stack-overflows** (`crl b => c if b => c .` + `rew b .`)
  where Maude spins forever. Both diverge; tnk aborts the process (vs Maude's interruptible loop).
  **RESOLVED (773a0d4** — heap-backed stack growth at the condition seam; tnk now spins. Re-verification
  note: on this machine the ORACLE itself exits 139 (SIGSEGV, its own stack overflow) on the minimal repro
  within seconds, so "Maude spins forever" does not reproduce — tnk now degrades strictly more gracefully
  than the reference.)

### 3.2 Silent wrong results (worst class: no error, different value)

- **[N] `rewrite` ignores `frozen`.** **RESOLVED (b2c1cdc).** `op g : S -> S [frozen]`, `rl a => b`: `rew g(a)` → tnk `g(b)`
  (1 rewrite); oracle `g(a)` (0). Partial `frozen (i)` equally ignored. `frewrite` and `search` honor
  frozen correctly — only the rule-fair `rewrite` traversal skips the check (`engine.rs:2420` pushes all
  children). Any spec using frozen for controlled rule application gets wrong results under `rew`.
- **[N] Statement application order across imports is REVERSED.** **RESOLVED (601239d — root-own-first + post-order donations, coupled with the META up* leading-window flip; new fixture A3b2-meta-own-window guards the coupling.)** Maude applies the importing module's
  statements first (local-then-imported donation order); tnk applies imported-first. `BASE: rl a => b`,
  `EXT includes BASE + rl a => c`: `rew a` → oracle `c`, tnk `b`. The same reversal hits overlapping
  *equations* (`red a` on non-confluent eq pairs → different values) and `search` solution order. Every
  deterministic `rew`/bounded-`rew` trajectory over multi-module rule sets is suspect.
- **[N] Negative INT shifts drop the sign.** **RESOLVED (d471d45).** `-8 >> 1` → tnk `4` (oracle `-4`); `-1 >> 100` → `0` (oracle
  `-1`); `-5 << 2` → `20` (oracle `-20`). `builtin.rs` shifts the magnitude. Plain arithmetic on ordinary
  specs is wrong.
- **[N] `id:`-only and `idem`-only operators are treated as free** — **RESOLVED (b2c1cdc)** — the axiom is never applied.
  `op _o_ : E E -> E [id: e] .` `reduce a o e .` → tnk `a o e` (oracle `a`); `[idem]` `reduce a o a .` →
  tnk `a o a` (oracle `a`). (Maude 3.5.1 does accept and apply both; `comm idem` and two-sided `id:` with
  assoc/comm are handled correctly in tnk.)
- **[D↑] Collapse-at-top under `id:`/CUI produces different VALUES, not just counts.** **RESOLVED (c6b9f36** — collapse indexing + identity-first enumeration + one-shot via the reduced cached identity dag; the Maude-loops case stays a loop, verified.) gaps.md calls this
  "rewrite count one lower, value same" — false in general: with `eq a + X = c` (`[assoc comm id: e]`),
  `reduce a` → tnk `a` (oracle `c`); `reduce a + b` → tnk `c` (oracle `b + c`). And a **termination
  divergence**: `eq X Y = c` over `[assoc id: nil]`, `reduce nil` → Maude loops forever, tnk halts. Bounded
  to patterns Maude itself warns about, but the doc's claim is wrong.
- **[N] tnk manufactures NaN floats.** **RESOLVED (d471d45).** `Infinity - Infinity`, `Infinity * 0.0`, `Infinity / Infinity`,
  `Infinity rem 2.0` → tnk `Float: NaN`; Maude leaves all of them unreduced (NaN can never appear in a
  Maude value). Downstream float code sees a value Maude's semantics excludes.
- **[N] String escapes broken in both directions.** **RESOLVED (501ff8f).** Lexing: `"\101\102\103"` → tnk the 9-char literal text
  (oracle `"ABC"`); `\a \b \f \r \v` are stripped to the bare letter. Printing: control/high bytes are
  emitted RAW (oracle escapes `\a`…`\r` + octal `\ooo`) — `char(13)` prints an actual CR into the output.
- **[D] Strings are char-indexed (UTF-8) where Maude's are byte sequences.** **RESOLVED (501ff8f).** `length("héllo")` → tnk 5,
  oracle 6; `substr`/`find`/`ascii` shift the same way on any non-ASCII content (verified). ASCII content —
  every fixture and the prelude's own use — is identical.
- **[N] `downTerm`/meta down-translation rejects flat (≥3-arg) assoc meta-terms — silently.** **RESOLVED (8fe4be2).**
  `downTerm('_+_['s_^2['0.Zero],'s_^3['0.Zero],'s_^4['0.Zero]], 99)` → tnk `99` (the fallback!), oracle `9`.
  Same root makes `metaReduce(['NAT], <flat term>)` inert. Maude metaprograms (and Maude's own `upTerm`)
  produce flat assoc meta-terms routinely; tnk's own internal rep is flat, yet the meta reader requires
  exact binary nesting (`meta.rs:1490,1596`, `descent.rs:74` resolve by exact (name, arity)).
- **[N] `upModule` of a parameterized module drops the parameter list** **RESOLVED (8fe4be2)** (`fmod 'LIST is` vs oracle
  `fmod 'LIST{'X :: 'TRIV} is`) **and loses `ditto`-inherited attributes** on subsort overloads (bare
  `[ctor]` vs `[assoc ctor id(…) prec(25)]`). Metaprogramming over parameterized modules sees a different
  module than Maude shows.
- **[N] `-0.0 == 0.0` → `false`** (bit-level equality; oracle `true`). IEEE `<`/`<=` conform. **RESOLVED (d471d45).**
- **[N] Kind-only builtins reduced where Maude fails them:** **RESOLVED (d471d45 divides/float/qid; 501ff8f char).** `0 divides 5` → `false` (oracle: stays at
  `[Bool]`); `char(256)` → `"Ā"` (oracle: unreduced, byte domain); `float("NaN")`/`float("5")` over-accepted;
  `string(qid("a b"))` → `"a b"` (oracle `"a`b"` — qid normalization missing).
- **[N] `metaParse` returns the flattened parse** **RESOLVED (ce71c36 — lazy AU splice; metaParse up-translates the nested surface parse; trace shows the two steps.)** (`'_+_[a,b,c]`) where Maude returns the true nested
  surface parse (`'_+_[a,'_+_[b,c]]`) — the eager-flatten architecture visible as a wrong meta *value*
  (gaps.md claims flatten affects counts only). Same root shows the trace as one fold (`2+3+4 ---> 9`)
  vs Maude's two steps.
- **[N] Meta-modules containing a `strat`-attributed op go inert.** **RESOLVED (8fe4be2; the metaXapply hole-context order rode along — the metaMeta/upImports medium-confidence corners remain open.)** The meta down-translation rejects the
  `strat (…)` op *attribute*, so `metaReduce`/`metaRewrite`/`metaApply` over such a meta-module return
  unreduced (object-level `strat` works fine). Hits four of the C++ Meta tests directly. Related medium-
  confidence meta corners from the suite sweep: `metaMeta` (self-reflection) returns a degenerate module;
  a `metaXapply` extension-context hole lands in the wrong argument; `upImports` on an error-containing
  module returns a value where Maude stays unreduced (tnk has no "unusable module" tracking).
- **[N] `metaNormalize` applies user equations.** **RESOLVED (8fe4be2).** It must normalize modulo structural axioms ONLY:
  oracle returns the term unchanged (`{'g['a.S], 'S}`); tnk fully reduces it (== `metaReduce`) —
  `meta.rs:94` routes `Reduce | Normalize` to one handler. (Pure AC-reordering cases coincide, masking it.)
- **[N] `upModule` of a strategy module is wrong**: result sort `SModule` instead of `StratModule`, prints
  `mod`…`endm`, and **omits the `strat` declarations and `sd` definitions entirely** (mb/rl content is
  right). **[N]** `metaPrettyPrint` is inert even with the default `none` option set on a fresh module
  (docs and the fixture claim it done — the conformance pin evidently exercises a narrower path).
- **[N] Renaming a single-token mixfix op silently produces a *prefix* op.** **RESOLVED (fe2485e — incl. the op→op mixfix view family.)** `M * (op _+_ to _plus_)` →
  `x plus y` no longer parses; only `plus(x, y)` does (`rename.rs:77-89` keeps just the first literal
  fragment). If the renamed op occurs in any statement, the renamed module is REJECTED outright. Same
  family: **op→op views break whenever either side is mixfix** (only prefix→prefix works; mapping
  `op _#_ to _+_` — the common case — fails to build the instance). Multi-token punctuation names
  (`_,_` → `_;_`, the prelude's own pattern) work, which masked this.
- **[N] Module/view redefinition leaves dependents stale.** **RESOLVED (ee4846b).** Redefine `M` after `N` imported it: `reduce in
  N` still uses the OLD `M` (oracle re-flattens with an advisory and recomputes). Silent wrong results in
  any interactive redefinition workflow.
- **[N] Fake parameter sorts are wrongly substituted.** **RESOLVED (fe2485e).** `sort X$Foo` where `Foo` isn't in the parameter
  theory must survive instantiation unchanged (only real `X$Elt` maps); tnk renames it to `Y$Foo`
  (`tests/Corner/fakeParameterSort` shape).

### 3.3 Wrong counts / enumerations (value right, accounting or solution-set off)

- **[D] Infix ≥3-operand builtin folds count 1 vs k−1** **RESOLVED (dd46724 — lazy ACU splice preserves the surface nesting through bottom-up reduction; prefix n-ary folds still count 1, §3.9.3.)** (`2 + 3 + 4`: 1 vs 2). Prefix folds (`gcd(a,b,c)`)
  conform. Leaks through meta (`upTerm(2 + 3 + 4)`: 2 vs 3) and `set trace`.
- **[N] `search … =>!` per-solution snapshots differ** (`states: 4 rewrites: 3` vs oracle `5/4` on the first
  solution; totals agree — tnk explores lazily where Maude expands the frontier first). **RESOLVED (a3291c8).**
- **[N] `xmatch` over iter under-enumerates**: **RESOLVED (b6e9656 — command-gated extension refinements: AU-with-id 10, iter 3, AU bare-var 3.)** `xmatch X:Nat <=? 3 .` → 1 matcher (oracle 3: whole + s-residue
  portions). **[N]** AU bare-variable xmatch under-enumerates (1 vs 3). **[D-quantified]** AU-with-identity
  xmatch over-enumerates (20 vs 10 on `X Y <=? a b c`).
- **[N] AC memberships are not applied through extension** **RESOLVED (5028a8e — canonical prefix fold; written-order corner documented.)** (`mb (a | a) : Special` on `a | a | a`: 0 vs 1
  rewrite; cmb 2 vs 3; result terms equal).
- **[N] `such that` condition-evaluation rewrites are not counted.** **RESOLVED (a3291c8).** `search [3] c(0) =>+ c(N) such that
  N rem 2 =/= 0` → per-solution counts oracle 4/12/20 vs tnk 2/10/18 (the missing 2 = the `rem` and `=/=`
  reductions). Sort-test conditions (0-cost) match. Now confirmed at object level, not just meta.
- **[D-concrete] `metaParse` failure position**: oracle `noParse(1)` on `'a 'b`, tnk `noParse(0)`. **RESOLVED (a3291c8).**
- **[N] `show search graph` merges arcs differently**: two rules reaching the same successor are one arc
  listing both rules in Maude, two separate arcs in tnk; rule text in the graph prints `f(s s 0)` where
  Maude prints `f(2)`. **RESOLVED (a3291c8).**
- **[D] `matchrew`/`amatchrew` and rewrite-condition substrategies run their sub-searches eagerly within a
  step**, so their per-solution cumulative counts can collapse to the final total when interleaved with
  unequal-depth parallel work (values, order, reachability faithful; `dsrewrite` coincides, which is how the
  fixtures pin it). The faithful mechanism is Maude's *parallel* `SubtermTask`/`rewriteTask` odometer — a
  scheduler change, not a counting tweak. Related narrow item: a `one`/`!` nested after a union with a
  multi-solution sub-search can swap two same-count solutions' order.
- **[D] `decFloat(f, 0)`** (exact full expansion) stays unreduced for subnormals whose denominator exponent
  is ≥ 64 (needs more than a machine word); finite `prec > 0` and all normal-range floats are exact
  (verified).
- **[D] Collapse-under-identity count** (the `makeSet(nil)` family) — subsumed by the §3.2 collapse item.

### 3.4 Rejections of legal input (Maude accepts; tnk errors)

Each of these breaks real specs; several break stock library files.

- **[N] No implicit BOOL import.** **RESOLVED (6e963ae — set include BOOL wired + auto-import).** Maude injects BOOL into every module (`set include BOOL on`, prelude
  line 3233); `a == b`, `if_then_else_fi`, `and` fail to parse in any tnk module that doesn't explicitly
  `protecting BOOL`. Virtually every published Maude spec relies on it. (The repo's fixtures all
  explicitly import BOOL — the suite can't see this gap.)
- **[N — fundamental] Imports re-parse imported statements in the importer's grammar.** **RESOLVED (3538530 — home-grammar point-fix per D10: imported statements parse against their home module's grammar, flattened-first with home reparse on failure; plain named imports; the full compiled-module-algebra rework remains a user decision.)** Adding a constant
  or op in an importer can make an *imported, already-valid* module's statement ambiguous → the importing
  module fails to build. Minimal: BASE has `var X : S . eq h(X) = a .`; EXT = `including BASE . op X : -> S .`
  → `error in module EXT: ambiguous parse: h ( X )`; oracle is fine (statements are parsed once, at home).
  **Breaks stock `term-order.maude`**: any module importing META-MODULE together with RAT/CONVERSION dies on
  RAT's own `eq I / N - J / M = …` (prelude.maude:449). Sibling-import var collisions are safe (bubbles parse
  with their own module's vars); the exposure is importer-signature × imported-statement-text. Always a noisy
  build error (the original parse stays as a candidate), never a silent re-parse — but module validity is
  context-dependent, which Maude's module algebra forbids.
- **[N] Glued rational literals never parse**: **RESOLVED (04f7515; the 1/6+1/6 count via 6e963ae's lazy ACU merge).** `reduce in RAT : 1/6 .` → no parse (spaced `1 / 6` works);
  tnk *prints* `1/6`, so its own output doesn't re-read. Fixtures avoided the glued form entirely.
- **[N] Numeric literal classes capped/missing**: **RESOLVED (04f7515 + 5028a8e bignum facade).** integers > 2^64−1 → `bad numeral` (tnk computes and
  prints them fine — asymmetric); float forms `1.`, `.5`, `1.e3`, `1e3`, `Infinity` rejected (the lexer
  unit test asserts Maude rejects these — it doesn't); iter input `s_^k(t)` unparseable at ANY k (tnk
  prints that form for k ≥ 2).
- **[N] `eq [label] : lhs = rhs .` (leading bracketed labels on eq/ceq/mb/cmb) rejected** **RESOLVED (04f7515.)** — only rl/crl
  accept them; the ubiquitous labeled-equation style kills whole modules.
- **[N] A single bad statement kills its whole module** **RESOLVED (04f7515 — statement dropped, module kept.)** (Maude drops the statement, keeps the module) —
  compounding every parse-level gap above; subsequent commands then fail with "no current module".
- **[N] Ambiguous terms hard-error** **RESOLVED (40a68e7 — command-term warn-and-pick per D9; pick matches the oracle on the C5 cases; statement bubbles stay strict pending D1a.)** where Maude warns, picks the first parse, and computes (`reduce f a g .`,
  non-assoc `a + b + c`). tnk gives no result. (Matching Maude's pick requires reproducing MSCP's
  enumeration order — a real architecture question for the Earley parser.)
- **[N] `reduce`/`rewrite` of non-ground terms rejected** **RESOLVED (04f7515 — inert variable atoms.)** (`red X + a .` etc. — Maude reduces open terms;
  `build_term.rs:234` demands groundness).
- **[N] `left id:` / `right id:` rejected at parse** **RESOLVED (04f7515 — construction-side; matcher sidedness noted as follow-up.)** (one-sided identities unusable). **[N]** `pconst`
  (parameter constants) likewise rejected, failing the enclosing theory.
- **[N] `(M * (renaming)){Args}` — instantiating a renamed module expression — unparseable** **RESOLVED (04f7515 — incl. arity-disambiguated renames, label renames, op->term views with args, OO items, pconst.)**; breaks stock
  `linear.maude`. **[N]** Arity-disambiguated renaming `op f : A B -> C to g` is a self-reported stub
  ("B5 follow-up"); breaks stock `machine-int.maude`. **[N]** `label l to m` renaming items and **op→term
  views with variable arguments** (`op lt(A, B) to term A < B` — the main use of op→term) rejected;
  **OO renaming/view items** (`class`/`attr`/`msg to`) rejected, so valid OO renamings kill their module
  (OO *modules* work; OO *views* don't).
- **[N] A renaming that touches a parameter-theory sort rejects the module** (oracle ignores the mapping
  with an advisory and builds). **RESOLVED (pre-scoreboard: fixture A4e-param-rename-shield passes from
  birth — tnk now recovers by ignoring the mapping, value-identical to the oracle; the rejection is only
  reachable via the `(M * (renaming)){Args}` form, which is finding C3a. Kept as regression net.)**
- **[N] Top-level junk-token recovery**: **RESOLVED (04f7515 — warn-and-skip + comment-before-select fix.)** Maude warns and skips token-by-token; tnk hard-errors and can
  abandon the rest of the file (recovery inconsistent between cases). Related: **a `***`/`---` line comment
  immediately before `select` or `show` desyncs the command parser** (spurious "unexpected top-level
  token"; `reduce`/`rewrite`/`search` after a comment are fine) — breaks two C++ suite tests.
- **[N] `id:` referencing a constant declared later in the module** **RESOLVED (04f7515 — constants declared first.)** → `unknown id: constant`, module
  unusable (declaration-order dependence Maude doesn't have; breaks `ResolvedBugs/physArgIndexOct2018`).
- **[N] Multi-sort kind brackets `[A,B]` in declarations** rejected **RESOLVED (04f7515.)** (`kindNameDecember2022`); single-sort
  `[A]` works. **[N]** `generated-by` declarations and the `rpo` attribute rejected.
- **[N] `frewrite [bound, gas]`** (the two-number form) rejected **RESOLVED (04f7515 — incl. the [_]-headed LHS and matchrew-pipe items in the same bullet.)** — the gas parameter is stuck at its
  default of 1 (`erewrite [n,m]` parses fine). **[N]** A statement whose LHS starts with a `[_]`-headed
  term (`rl [N] => [N + 1] .` over `op [_] : Nat -> Obj`) fails with "empty term" — the leading `[` is
  taken for a label/attribute bracket; nested occurrences work. **[N]** A bare `|` inside a
  `matchrew`/`amatchrew` pattern is misparsed as strategy union (parenthesizing works).
- **[D] Two commands on one line**: tnk runs both; oracle rejects both **RESOLVED (04f7515 — whole line rejected, files with one command per line unaffected.)** (documented dot-heuristic risk, now
  characterized: tnk is more permissive).

### 3.5 Scale/robustness

- **[N] Naive AC matching hangs on trivially small inputs.** **RESOLVED (41e22a7 — Diophantine matcher core, ac-matcher-plan phases 1-3; 30-element set <1ms, N=100 flat; naive matcher retained as cross-check.)** `Misc/dataStructures`: computing the size of a
  30-element `Set{Nat}` (`| gen(30,13) |`) times out (>60s) where the oracle finishes the whole test in
  seconds. The documented "AC matcher is perf-only" framing understates this: real container workloads at
  double-digit sizes are already unusable, independent of the separate large-term parse/build issue below.
- **[N] Super-linear (~cubic) handling of large well-formed terms**: **RESOLVED (dd46724 + earlier frontend work — the 2000-element chain parses, reduces (1999 counted folds), and prints oracle-equal well inside the budget; D3 fixture passes.)** a flat 2000-element AC sum takes 14s
  (oracle: milliseconds), 5000 elements > 60s vs oracle 30ms. Distinct from the documented garbage-bubble
  Earley blowup — this is the well-formed path (parse/build dominates; AC contributes the larger factor).
- **[D] Garbage-term Earley blowup** (the distinct, documented case — not re-reproduced this audit): a
  genuinely unparseable command term against a large module's grammar can enumerate exponentially. The
  `in <MODULE> :` command qualifier removed the common historical trigger (the module name is parsed
  structurally, not as part of the term bubble); a true typo against a big module remains a latent hang. A
  parse timeout / ambiguity cap is the eventual fix.
- **[N] `rewrites/second` timing is a stub** (always `0ms (~ rewrites/second)`).

### 3.6 Extra acceptance (tnk accepts what Maude rejects)

- **[N] A theory imported into a plain module is accepted — and its axioms EXECUTE.** **RESOLVED (70768e8 — import ignored, axioms never run.)** `fmod M is protecting
  TH .` (TH an `fth`): oracle refuses (theories import only as parameters); tnk builds M and runs the
  theory's equations as if they were module equations. The theory/module semantic distinction is not
  enforced.
- **[N] Importing a module with FREE parameters is accepted** **RESOLVED (70768e8.)** (instantiation through a theory-target view
  leaves the parameter free; oracle refuses to import such a module; tnk builds and reduces).
- **[N] Self-import accepted** **RESOLVED (70768e8.)** (`fmod M is protecting M .`) — no import-cycle detection.
- **[N]** `sort A.B .` (dotted sort names) accepted and usable; **RESOLVED (70768e8.)** Maude rejects with warnings.
- **[N]** Zero bounds `rew [0]`/`search [0]` accepted and run 0 steps; **RESOLVED (70768e8.)** Maude rejects a `[0]` bound at parse.
- **[N]** Malformed `[print …]` attribute contents parse-ignored **RESOLVED (70768e8 — statement dropped per the oracle's validation rule.)** (Maude validates and drops the statement —
  effective ruleset differs). `[otherwise]` on a *rule* runs silently (Maude warns, then runs — same result).
- **[N]** `exit` quits (not a Maude command).

### 3.7 Cosmetic / diagnostic (bounded; summarized)

- Mixed-symbol ACU argument print order and AC echo pre-canonicalization (same multiset; the docs' claim
  that the ACU print-order divergence was fully resolved is true only for same-symbol multisets).
- Strategy-expression echo drops needed parens (`(r1 | r2) !` echoes as `r1 | r2 !` — a *different* strategy
  than the one executed; results are computed for the right one).
- Trace statement-body rendering (`s 0` for `1`; substitution-order vs canonical AC order in the redex);
  `Matched portion` labels; extra blank line before `No match.`; bounded `frewrite [n]` prints
  `result (sort not calculated):` where Maude computes the sort — and inversely, bounded `erew [n,m]` on a
  non-config term prints a computed sort where Maude says `(sort not calculated)`; zero-solution `search`
  says `No more solutions.` instead of `No solution.` (the srewrite path gets it right); boolean
  `such that` echo omits Maude's `= true`; a goal variable shadowing a declared var prints `N:Nat` vs `N`;
  `metaXapply`'s AC hole context puts the hole first (`'_+_[[], 'b.S]` vs Maude's residue-first — RESOLVED (8fe4be2));
  `continue`-with-nothing-pending wording; meta-module echo grouping parens/element order; count-1 prefix
  iter prints `t c` (doesn't round-trip); no warnings/advisories anywhere (the single largest byte-diff
  source vs the oracle on real files).
- **[D] Multi-top-component kind labels and the incomparable-membership tiebreak.** A kind-level result in
  a component with several *maximal* sorts lists them in declaration order (`[A,B,D]`) where Maude uses its
  ConnectedComponent sort index (a per-component DFS-topological numbering, `Core/sort.cc`
  `registerConnectedSorts`/`appendSort`) → `[B,D,A]`; the same index drives which of two *incomparable*
  membership targets wins (contradictory specs only). Load-bearing for no computed result — least sorts are
  down-set intersection + declaration-order tiebreak, not index comparison; single-maximal kinds (all
  well-formed signatures) print identically. Reproducing it means porting that DFS numbering.
- **[D] Bounded `frewrite [n]` intermediate over an AC operator** inherits the mixed-symbol ACU argument-
  order divergence above (free-operator intermediates are exact — verified; the unbounded result and count
  are order-independent for terminating systems).

### 3.8 The C++ test suite, quantified

All 231 tests in `~/code/maude-lang/maude/tests/` were run through both binaries with each test's real
flags (mostly `-no-advise`). Clean byte-identical passes: 7 (2 Meta, 4 ResolvedBugs, 1 Corner), plus one
more ResolvedBugs test that passes once the implicit-BOOL gap is patched around. Graceful
missing-feature failures (unify/variants/narrowing/SMT/model-checker/meta-interpreter/sockets/files/
loop-mode): ~100. Diffs traced to findings in §§2–3: ~120 — dominated by the missing warning surface, the
missing `show`/`parse` commands, non-ground reduce, and iter notation, i.e. **display/command/acceptance
artifacts around correct computation** (e.g. `Corner/ACU_TreeVariableSubproblem`'s 24 ACU results and
counts are byte-identical once advisories are set aside). One hang (the AC-matching item in §3.5); zero
tnk crashes in the suite (the panics in §3.1 come from constructs the suite doesn't exercise). The
low raw pass count is an honest statement of *tool-surface* distance, not engine distance — but
`ResolvedBugs` (79 tests, each encoding a bug Maude fixed) yields several genuine behavioral findings
(`id:` forward-reference, `[A,B]` kinds, disambiguated renaming, `generated-by`, upImports-on-broken,
frew sort annotation) now folded into §§2–3.

### 3.9 Non-obvious constraints when closing these gaps (folded from the retired `gaps.md`; each verified)

Facts that are easy to get wrong when starting the corresponding fix — kept because they would *not* be
naturally rediscovered, and getting them wrong produces a new divergence:

1. **Do not add a no-op rewrite guard.** Maude itself loops forever on `eq a = a` / `eq f(X) = f(X)`
   (verified empirically; mechanism: `DagNode::reduce` exits only when `eqRewrite` fails —
   `dagNode.hh:563` — with no result==redex check), and tnk matches that. A guard would make tnk halt
   where Maude loops. The legitimate item behind the temptation is *interruptibility* (Ctrl-C), §2.
2. **`frozen` blocks rule application only — never equational reduction** (Maude's semantics). The
   §3.2 `rewrite`-ignores-`frozen` fix must copy `frewrite`'s check, not suppress reduction in frozen
   arguments.
3. **The infix builtin-fold count cannot be fixed by folding the flat node pairwise.** Prefix N-ary folds
   (`gcd(12,18,8)`) count **1 in both engines**; only *infix* chains count k−1 in Maude — and
   infix-vs-prefix is exactly the information the eager flatten destroys. Hence the surface-preserving
   representation requirement (`ac-matcher-plan.md` Phase 6), which this audit widens to `metaParse`
   values and trace shape (§3.2).
4. **Collapse-under-identity firing is one-shot.** With `eq (S, S) = S` over `[assoc comm id: e]`, Maude
   fires the collapse exactly once on an identity subject and stops (`red e` = 1 rewrite) even though the
   step is a no-op — naive apply-to-fixpoint hangs (that *is* the §3.2 termination divergence, from the
   other side), and skipping it entirely is today's undercount. Captured numeric targets live in
   `ac-matcher-plan.md` §3.2.
5. **`DagNode.nf` (normal-form forwarding) is load-bearing.** It costs ~6% on sharing-free workloads by
   field size alone, and it is what makes structure-sharing rewrite *counts* byte-faithful (a membership
   or reduction over a repeated subterm counts once, as in Maude). Don't strip it for throughput.
6. **Conditional-rule `metaApply` / conditioned `metaMatch` want a condition-evaluator seam, not new
   logic.** The engine already evaluates `ceq`/`crl` conditions internally; the work is exposing a
   reusable "evaluate this condition under this substitution, enumerate solutions" entry point. Until
   then both stay inert (never misfire) — verified, along with the non-empty-partial-substitution
   `metaApply` corner (inert; Maude returns `(failure).ResultTriple?`).
7. **Flat-mode `up*` over a builtin-importing closure omits the builtin declarations by construction.**
   Builtin/prelude imports live at the *engine* level — their ops/eqs are never re-inlined into the
   flattened statement list — so a faithful `flat = true` `upOpDecls`/`upModule` must up-translate
   `special (id-hook … op-hook …)` and `poly` attributes: the inverse of the down-path's `special → None`
   boundary. (Verified: `upModule('NAT, …)` stays inert today, and `metaReduce` over it likewise.)
8. **Strategy-meta has two structural prerequisites** (why `upStratDecls`/`upSds`/`metaParseStrategy`
   stay inert): (i) the ~25 strategy meta-constructors overload bare names (`none`, `_;_`, `_,_`, `_|_`)
   across many result sorts, so the meta reader's resolve-by-(name, arity) (`descent.rs:74`) cannot build
   them — resolution by *result sort* is required; (ii) tnk's strategy parser desugars
   `try`/`not`/`test`/`or-else` into the `_?_:_` branch (verified in `strategy.rs`), but the meta-rep
   keeps them as distinct constructors — a faithful round-trip needs the surface form preserved through
   resolution.

## 4. Architecture: where we may be boxed in

1. **Import-as-reparse (the PreModule→PreModule module algebra).** The flatten inlines statement *bubbles*
   and re-parses them under the importing module's grammar. Maude parses statements once, in their home
   module, and imports copy *compiled* statements. Consequences today: §3.4's context-dependent module
   validity (term-order.maude), the documented instance-only typechecking of parameterized modules, the
   `upModule` parameter/ditto losses, and `show module`'s inability to render source-form modules. This is
   the deepest divergence from Maude's semantics: fixing it fully means giving modules a compiled,
   import-stable statement representation (i.e., moving toward Maude's semantic module algebra), which also
   unblocks faithful `show module`, meta fidelity, and Full Maude later. Point-fixes (e.g. parsing each
   bubble against its *home* grammar even when installing into the flattened module) could remove the
   breakage without the full rework — worth deciding deliberately rather than case-by-case.
2. **Eager assoc-flatten at construction.** Documented as a count-only issue; it is also a *value* issue at
   the meta level (`metaParse` returns flat parses) and shapes `set trace` output. The planned
   bipartite/Diophantine matcher rework (`ac-matcher-plan.md`) already calls for a surface-preserving
   representation — that rework should explicitly own `metaParse`/trace/count fidelity, not just matching.
3. **Earley parser vs MSCP ambiguity policy.** tnk errors on ambiguity; Maude warns and deterministically
   takes its "first" parse. Reproducing Maude's pick order is an MSCP implementation detail — decide whether
   to (a) reproduce it, (b) keep the stricter error (a deliberate, documentable divergence that already
   blocks one stock file via item 1's reparse amplification), or (c) warn-and-pick tnk's own first parse.
4. **No diagnostics infrastructure.** Dozens of behaviors differ only in a missing Warning/Advisory. One
   sink + call sites threaded through build/parse/reduce is a wide but shallow retrofit; without it, real
   Maude workflows (which read the warnings) and differential testing both stay noisy.
5. **No standing prelude / no implicit imports / no file commands — the "tool identity" gap.** All are REPL
   -layer, none engine-deep, but together they mean tnk cannot run existing .maude files as found in the
   wild. The `set include <MOD> on/off` mechanism (prelude lines 31/3233) is the missing semantic piece;
   `load`/`sload`/`in` + argv flags are the missing plumbing.
6. **Frontend literal token classes.** Rationals, float variants, big numerals, `s_^k` — all parse-layer
   only (the engine handles the values); a single lexer/terminal sweep closes them, and the round-trip
   asymmetries (prints what it can't read) disappear.
7. **Conformance methodology.** The in-repo suite pins expected strings — usually oracle output, but for at
   least three surfaces (meta op-decl echo, strategy echo, prelude-list's comment fallout) the pins are
   tnk's own divergent output, so regressions of that class are invisible. An oracle-in-the-loop harness
   (like this audit's `diffmaude.sh`) run in CI over the fixture corpus would catch pin drift and the
   warning-layer diffs at ~zero maintenance cost.

## 5. Priority recommendations

1. Fix the panic classes (§3.1: iter non-linearity, op-decl arity, unbound rhs variable) and the
   silent-wrong-value bugs (§3.2: **`rewrite`-ignores-`frozen`**, **import statement order**, negative
   shifts, NaN, string escapes, id/idem-only ops, mixfix renames, stale redefinition, `metaNormalize`) —
   mostly small and isolated, all high-severity.
2. Decide the import-reparse question (§4.1) before more module-algebra features stack on it; at minimum,
   parse imported bubbles against their home signature.
3. Close the input-acceptance layer: implicit BOOL + `load`/`sload` + literal token classes + eq-labels +
   non-ground reduce + statement-level error recovery (§3.4). This is what stands between "conformant
   engine" and "can run real Maude files".
4. Meta fidelity: flat assoc meta-term reading (downTerm/metaReduce), `strat`-op meta-modules, upModule
   parameter list + ditto attributes (§3.2) — prerequisites for any reflective tooling and eventual Full
   Maude.
5. Re-rate the AC matcher port from "perf, when it matters" to near-term: 30-element sets already hang
   (§3.5), which blocks running realistic container workloads at all.
6. Adopt the oracle-diff harness in CI (§4.7).
7. The `show`/`set print`/debugger/trace-selection surface (§2) — large, mechanical, user-facing.

---

*Detailed per-area reports (with every probe file) live in the session scratchpad (`findings-{main,commands,
theories,builtins,syntax,cpptests,modalg,dynamics}.md`, probe dirs alongside); the reusable differential
harness is `diffmaude.sh` there. All seven sweeps are integrated above.*
