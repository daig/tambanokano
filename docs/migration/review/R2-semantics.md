# R2 — Rewriting semantics review

Adversarial review of the Phase-0 kernel (`crates/tnk-core/src/`) through the lens of
**rewriting-logic semantics correctness**: where does this produce a wrong normal form, loop,
crash, or diverge from Maude's free-theory semantics?

Scope reviewed: `term.rs` (`match_pattern`, `deep_equal`, `instantiate`, `Subst`), `engine.rs`
(`reduce`, `reduce_args`, `try_rewrite_top`, `compute_free_sort`, `add_equation`, `make_free`),
`sort.rs` (poset / kinds / closure / `leq`), plus `dag.rs`, `arena.rs`.

All 19 unit tests pass; canonical forms and rewrite counts match reference Maude on the conformance
fixtures (`2+2 → s⁴0` / 3 rewrites; `3*4 → s¹²0` / 21; `fib(22) → 17711` / 186579). The reduction
*strategy* (eager innermost, textual equation order) is faithful. The findings below are about
**inputs and configurations the fixtures do not exercise**.

Findings are tagged with the build/profile used to reproduce. Empirical results were obtained by
running `examples/peano` at escalating inputs and a throwaway probe (since removed).

---

## CRITICAL

### C1 — `reduce` / `reduce_args` / `deep_equal` are recursive on *subject depth*; deep terms stack-overflow. The Fibonacci benchmark is ~2 steps from the cliff.
`engine.rs:147-158` (`reduce`), `engine.rs:161-181` (`reduce_args`, recursive call at line 172),
`term.rs:113-127` (`deep_equal`, recursive at line 124).

`reduce` descends the subject via `reduce_args` → `reduce(child)` → `reduce_args` … so the host
call stack grows with the **depth of the runtime term**, not the size of the (small, fixed)
patterns. In unary Peano, term depth equals the numeric *value*, so depth is exponential in the
input. The dominant driver is the addition loop: reducing `plus(sᵖ 0, sᵠ 0)` recurses ≈ `q` frames
deep, because `N + s M = s(N + M)` rebuilds `s(plus(...))` and `reduce_args` immediately re-enters
`reduce` on the inner `plus`. For naive `fib(n)` the top redex is `fib(n-1) + fib(n-2)`, so peak
depth ≈ `fib(n-2)` ≈ Θ(1.618ⁿ).

Measured cliff (8 MB main-thread stack):

| build | last OK | first crash | depth at crash (`fib(n-2)`) |
|---|---|---|---|
| `--release` | `fib(24)` (514105 rw) | **`fib(25)`** → `SIGABRT` "has overflowed its stack" | 28657 |
| debug | `fib(23)` (309813 rw) | **`fib(24)`** → `SIGABRT` | 17711 |

The shipped benchmark / conformance fixture is **`fib(22)`** (`examples/peano` default, `fib.maude`,
`04-phase0-results.md`). That is **one step below the debug cliff and three below release** — and
because depth grows ~1.6× per step there is essentially no headroom. A routine Maude input like
`fib(30)` (instant in reference Maude, which normalizes with an explicit stack) crashes hard here.

Minimal reproductions:
- `cargo run --release --example peano 25 1 100` → `fatal runtime error: stack overflow, aborting`.
- Non-fib trigger: `reduce` of any depth-≳100k term (release) / ≳50k (debug) overflows even with **no
  equation firing**, since `reduce_args` walks the whole spine; e.g. `reduce(sᵏ 0)` for `k ≈ 300_000`.
- `deep_equal` independently overflows: a non-linear equation `g(X,X)=z` reduced on `g(D,D)` with `D`
  of depth 200_000 aborts with stack overflow (the non-linear arm at `term.rs:124`).

This is the headline "latent scalability cliff." It is a hard crash on valid, well-typed input, and
it understates real risk because the chosen benchmark sits just under the threshold.

**Fix:** make normalization iterative with an explicit work stack (mirroring Maude's stack-based
`reduce`), at least for the spine descent in `reduce_args` and for `deep_equal`. As an interim
guard, run reductions on a worker thread with a large/growable stack (e.g. the `stacker` crate) or a
configurable recursion limit that returns an error rather than aborting the process. Note `instantiate`
(bounded by rhs depth) and `match_pattern` (bounded by pattern depth) are *not* at risk, and GC's
`mark_reachable` is already iterative — so the fix is localized to `reduce`/`reduce_args`/`deep_equal`.

---

## HIGH

### H2 — The `REDUCED` flag goes stale when equations are added after a reduction → silently wrong normal form.
`engine.rs:148` (early return on `is_reduced`), `engine.rs:156` (`set_reduced`), `engine.rs:131-134`
(`add_equation` never invalidates flags).

`reduce` marks a node `REDUCED` and thereafter short-circuits it. The flag means "normal form **with
respect to the equation set that existed at the time**," but nothing ties it to the equation set.
`add_equation` mutates `self.equations` without clearing any `REDUCED` bit, so a node reduced *before*
an equation was added is permanently treated as canonical even though the new equation applies to it.

Note this fires even for a term that was *already* a normal form: with no equations, `reduce(a)` for a
constant `a` still sets `REDUCED` on `a` itself (`reduce_args` returns it unchanged, no top redex), so
the flag sticks to the original node.

Minimal failing input (confirmed, release):
```
ops a, b : S .                 // no equations yet
let a0 = make_const(a);
reduce(a0);                    // marks a0 REDUCED, returns a0
add_equation(a = b);
reduce(a0)  => a               // WRONG: should be b (stale REDUCED short-circuit)
reduce(make_const(a)) => b     // a fresh node *does* rewrite to b
```
So the *same operator* `a` reduces to either `a` or `b` depending on allocation/reduction history —
a silent, non-deterministic wrong result and a soundness violation. The same hazard hits any shared
subterm that was normalized before a later `add_equation`.

This does not affect the "build the whole module, then reduce" flow (why the fixtures pass), but the
kernel exposes `add_equation` publicly with no ordering guard, and the project explicitly targets
REPL / incremental modules (report A5) and meta-interpreters / multiple engines (D1), where
reduce-then-extend is normal.

**Fix:** version the equation set — store an epoch on the engine, bump it in `add_equation`, stamp it
into the node when `set_reduced` runs, and treat `REDUCED` as valid only if the node's epoch equals the
current epoch (replace the bare bit with `Option<epoch>` or compare a stored `u32`). Cheaper but
coarser: clear all `REDUCED` marks on `add_equation`. Minimal but restrictive: forbid `add_equation`
after the first `reduce` (assert/`Result`).

---

## MEDIUM

### M3 — `add_equation` performs no well-formedness check; malformed equations panic at *reduce* time (process abort), not at definition time.
`engine.rs:131-134` (`add_equation`), `term.rs:132` (`instantiate` `.expect`), `term.rs:73`
(`Subst::get` index), `engine.rs:132` (`top_symbol().expect`).

`add_equation` accepts any `Equation` and indexes it by `lhs.top_symbol()`. Three classes of
malformed equation Maude rejects at parse/compile time instead reach the rewrite loop and **panic**
(an unrecoverable abort for a library):

- **Extra rhs variable** (rhs var not bound by lhs, or `nr_vars` too large): confirmed panic
  `unbound variable in instantiation` at `term.rs:132`. Repro: `eq f(X)=Y` with `nr_vars=2`,
  `reduce(f(c))`.
- **Variable index ≥ `nr_vars`** (inconsistent `nr_vars`): confirmed panic `index out of bounds: the
  len is 0 but the index is 0` at `term.rs:73` (`self.bindings[index]`). Repro: `eq f(X)=X` with
  `nr_vars=0`, `reduce(f(c))`.
- **Non-application lhs** (a bare `Term::Var`): `top_symbol()` is `None` → `expect` panics in
  `add_equation`. (A variable lhs is not a legal equation in Maude either.)

These are robustness/faithfulness gaps: a misconfigured module brings down the host process at an
unpredictable later point. **Fix:** validate in `add_equation` and return `Result`: lhs must be an
application; `vars(rhs) ⊆ vars(lhs)`; every variable index `< nr_vars`; (ideally) recompute `nr_vars`
from the lhs rather than trusting the caller. Also re-check rhs sort-correctness so reductions can't
silently move a term into the error sort via a bad rhs.

### M4 — Ill-typed term construction is silently accepted; cross-kind arguments are absorbed into the error sort, and arity is only `debug_assert`ed.
`engine.rs:64-67` (`make_free`), `engine.rs:76-89` (`compute_free_sort`, `zip` at 80-83,
`debug_assert_eq!` arity at 78).

`compute_free_sort` decides well-sortedness by `domain.iter().zip(args)`. Two issues:

- **Cross-kind argument:** giving `f : Nat -> Nat` an argument of sort `Bool` (a different kind)
  yields `leq(Bool, Nat) == false` → the node is assigned `error_sort(kind_of(Nat)) = [Nat]`. Maude
  would *reject the term* (it cannot be formed: `Bool` is not in `[Nat]`). Here it is silently
  constructed in `[Nat]`. It does not cause a *wrong reduction* (sorted variables won't match an
  error-sorted subterm, so no equation fires — error-sort propagation is otherwise monotone and
  correct), but it makes constructible a term Maude says does not exist, which can surface as
  divergent behavior in later phases.
- **Arity mismatch is only a `debug_assert`:** in release, `zip` silently truncates to the shorter of
  `domain`/`args`. A wrong-arity `make_free` (e.g. from a malformed rhs in `instantiate`) builds a
  corrupt node whose `args.len() ≠ arity`, mis-reports well-sortedness, and corrupts later traversal
  — with no error in release builds.

**Fix:** enforce, in `make_free`, that `args.len() == arity` and that each argument's sort is in the
operator's domain *kind* (return `Result`/error-sort deliberately rather than relying on `zip`
truncation); promote the arity `debug_assert` to a checked condition.

### M5 — No progress/termination guard: a stuttering or non-terminating equation spins `reduce` forever and (no hash-consing) leaks memory unboundedly.
`engine.rs:152-155` (the `while let Some(next) = try_rewrite_top(current)` loop).

The loop trusts the equation set to be terminating. Beyond genuine non-termination (which Maude also
diverges on), note a sharper footgun specific to this implementation: an equation whose rhs
instantiates to a term structurally identical to the redex — e.g. `eq f(X) = f(X)` or `eq a = a` —
makes `try_rewrite_top` return `Some` every iteration. Because there is no hash-consing and no
"did the term actually change?" check, each iteration **allocates a fresh node**, increments
`rewrite_count`, and never terminates → unbounded memory growth plus a meaningless rewrite count.
This is partly inherent to rewriting, but the no-op case is detectable. **Fix (optional for Phase 0):**
break the loop when `try_rewrite_top` returns a node equal to `current`, and/or expose an optional
rewrite/step bound so a non-terminating module fails gracefully instead of OOM-ing the host.

---

## LOW

### L6 — Subsort cycles are silently accepted (no preregularity / acyclicity check).
`sort.rs:59-62` (`add_subsort`), `sort.rs:99-169` (`close`). Declaring `a < b` and `b < a` makes the
BFS closure put each in the other's `geq`, so `leq(a,b)` and `leq(b,a)` both hold — they become
order-equivalent rather than being flagged as the error Maude reports. The closure itself terminates
(the `seen` set guards the cycle) and is otherwise correct. Acceptable for Phase 0 (garbage-in via a
low-level API), but worth a validation pass when modules become user-authored. The full
preregularity / least-sort-under-overloading machinery is already documented as Phase-1 (`sort.rs`
header).

### L7 — Equation selection is first-match in insertion order; faithful to Maude *only* for plain, textually-ordered equations.
`engine.rs:185-201` (`try_rewrite_top`), `engine.rs:131-134` (`add_equation` preserves push order per
symbol). For non-overlapping or confluent systems (all the fixtures) this reproduces Maude exactly,
including rewrite counts. Caveats to track: there is no `owise` (otherwise) handling, no
most-specific / preregularity-based ordering, and for **non-confluent** equation sets the normal form
becomes order-sensitive — faithful to Maude *iff* the caller inserts equations in source order. No
confluence/termination checking is performed. Mostly documented scope; flagged so it is not assumed
to generalize.

### L8 — `u32` arena id space aborts at ~4·10⁹ nodes.
`arena.rs:62` (`expect("arena exceeded u32 capacity")`). A hard panic rather than a graceful error,
but memory exhaustion would arrive first for realistic workloads. Note `rewrite_count` is `u64` and
fine.

---

## What is correct (verified)

- **Non-linear matching is sound.** `match_pattern` does a left-to-right DFS, so a variable's first
  occurrence binds (`term.rs:90-97`) and later occurrences compare via `deep_equal` (`term.rs:88`).
  Operands are normalized before matching (innermost), so structural `deep_equal` coincides with
  semantic equality in the free theory. (`f(X,X)` on equal-but-distinct-id subterms matches; on
  unequal subterms it does not — confirmed by `term.rs` tests and probe.)
- **Partial bindings on failed sub-matches are correctly contained.** `match_pattern`'s `args.iter()
  .zip().all(...)` short-circuits on the first failing argument, so a partially-bound failed branch's
  bindings are never *read* by a sibling; and `try_rewrite_top` calls `subst.reset(eq.nr_vars)` before
  every equation (`engine.rs:192`). A successful match leaves a total substitution over the pattern's
  variables. (Currently correct, though it relies on the reset discipline — see the note in H2/M3.)
- **The `REDUCED` flag is sound for a fixed equation set.** Invariant holds: when `set_reduced` runs,
  the node has fully-reduced children (every `reduce_args` path reduces children first) and no top
  redex (`try_rewrite_top` returned `None`), i.e. it is a genuine normal form. The only hole is
  cross-equation-set staleness (H2).
- **Sort closure is correct.** `close` computes connected components via union-find (`sort.rs:104-120`),
  a reflexive-transitive upward closure via BFS (`sort.rs:146-156`), and one error/top sort per kind
  that is a supersort of every member and `≤` only itself (`sort.rs:158-164`). Transitivity, kind
  separation, and error-sort maximality are test-covered and matched my reading.
- **Error-sort propagation is monotone and safe.** Ill-sorted arguments push a node into its kind's
  error sort (`engine.rs:84-88`), which no sorted pattern variable matches (`leq(error, userSort)`
  is false), so ill-sorted terms simply don't reduce — no spurious rewrites.
- **GC handles deep DAGs.** `mark_reachable` is iterative (`engine.rs:119-126`), so the recursion
  cliff (C1) is confined to reduction/equality, not collection. The `examples/peano` 2,000,000-node
  GC chain confirms this.
- **Strategy fidelity.** Eager innermost evaluation with textual equation order reproduces Maude's
  exact rewrite counts on `+`, `*`, and `fib` (3 / 21 / 186579).
