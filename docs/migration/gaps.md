# Known gaps from the reference (within the built engine)

Where our **built** functional engine differs from, simplifies, or defers something Maude does. (Not-yet-built
*features* are in `roadmap.md`; this is about the parts that already exist.) Three kinds: **accepted
divergences** (won't fix), **deferred optimizations** (correct now, faithful-when-ported), and **deferred
sub-features / robustness**. Everything here was found by differential testing; none affects a well-formed
spec's value / sort / rewrite count / termination unless noted.

## 1. Accepted divergences — output-only, won't fix

These reproduce a semantically-empty Maude-internal artifact; the differential harness absorbs them
(set-comparison for orderings; no fixture asserts the divergent surface).

- **ACU print / match-solution order.** Our kernel orders AC arguments by `SymbolId`; Maude orders by
  `Symbol::orderInt`. Same multiset → identical equality / normal forms / sorts / counts; only the printed
  argument order (`5 + x` vs `x + 5`) and the AC **match-solution enumeration** order (Maude's Diophantine
  order) differ. Match solutions are **set-compared** in the conformance harness. Hits `nat`, `acu-*` — the
  most common cosmetic delta.
- **Multi-operand infix built-in number fold — rewrite *count* (the one count divergence here, noted).**
  Same eager-flatten root as the ACU-order bullet above: our kernel flattens an ACU term at construction,
  so an infix chain `2 + 3 + 4` becomes one flat node `+(2,3,4)` and the built-in `ACU_NumberOpSymbol`
  fold combines *all* numeric operands in **one** rewrite. Maude keeps the surface parse **nested**
  (`2 + (3 + 4)`) and folds each binary node separately, counting **k−1** rewrites for k infix operands
  (trace: `2 + 3 + 4 → 2 + 7 → 9`, 2 rewrites). **Value and sort are always identical** (`9 : NzNat`); only
  the count differs, and only for a **≥3-operand infix chain of a built-in number op** — a 2-operand op
  (`5 xor 3`; every M1 example) and a **prefix** N-ary form (`gcd(12,18,8)` folds to 1 in *both*) match
  exactly, and **user-equation** AC reduction is unaffected (`a+a+a+a ⇒ a` is 3 in both, pairwise on the
  flat multiset). A faithful count needs the surface-preserving AC representation that comes with the
  **bipartite/Diophantine matcher** rework (§2) — a flat node can't distinguish infix-nested from
  prefix-flat post-parse, so it is not a built-in-fold tweak. No conformance fixture asserts the divergent
  case.
- **Multi-top component sort-index order.** Maude's `ConnectedComponent` "sort index" (a DFS-topological
  numbering, `Core/sort.cc`) leaks into two outputs: the **kind label** order (`[B,D,A]` vs our declaration-
  order `[A,B,D]`, only for a kind-level term in a multi-maximal component) and the **incomparable-membership
  tiebreak** (`sortConstraintLt`, only a *contradictory* spec). Proven load-bearing for **no** computed
  result (least-sort is down-set intersection + op-decl-order tiebreak, not index comparison). The ~40-line
  port recipe (per-component DFS numbering) is recorded if byte-parity is ever needed, but reproducing it
  would be over-indexing on an implementation detail.
- **REPL-vs-batch framing.** The piped reference prints `====` separators between command results, a startup
  banner, and `Bye.` on exit; our REPL omits these. Structural, not term-rendering — the echo / result /
  count / trace content matches byte-for-byte (incl. line-wrapping).
- **`frewrite` bounded-stop position order (Pillar A-ii).** Our `frewrite` ports Maude's `fairTraversal`
  *substance* faithfully — gas-bounded position fairness, the progress/pass loop, equational-reduce-between,
  frozen-argument skipping, `continue` — but as a clean post-order (leaves-first, left-to-right) walk rather
  than its exact redex-stack discipline. For a terminating system the unbounded result + rewrite count are
  order-independent (`frewrite (a|a)|a` = `(d|d)|d`, 9, byte-identical). The only place the order shows is the
  **intermediate term of a bounded `frewrite [n]`**, and only over an **AC** operator (a free op's children
  have a fixed order, so `frewrite [2] (a|a)|a` = `(b|b)|a` matches exactly) — there it inherits the existing
  ACU-argument-order divergence above, surfacing through one more surface. No new concession; no well-formed
  spec asserts it.

## 2. Deferred optimizations — correct now, perf-only, port when it matters

Faithful results today via a simpler mechanism; porting Maude's optimized version is a throughput step, not a
correctness fix.

- **AC / AU / CUI matcher.** We match modulo the axioms by **naive backtracking enumeration** (greedy
  smallest-first for reduce, full enumeration for `match`), not Maude's optimized **bipartite + Diophantine**
  solver. Reduce values/counts conform, including **AU and ACU identity-collapse** (a pattern `E L` / `(E, S)`
  matches a singleton `c` as `E=c, L=nil` / `S=empty` via the `id:` axiom — what `LIST`/`SET` need) and
  **non-linear** matching across arguments (`E in (E, S)` — a variable already bound by an outer subterm must
  agree with its multiset binding; the ACU pure path now deep-equal-checks pre-bound vars, as the free matcher
  does). Remaining gaps, off the reduce path of what's landed: (a) **CUI identity-collapse** is still
  `_ => return None` — no comm-only-with-identity op needs it yet (`sd` has no identity; `SET`/`MAP`'s `_,_` is
  assoc-comm = ACU), so it is wired only when one does; (b) **`xmatch` with extension over-enumerates** on a
  multi-element AU subject (residue splits Maude does not report at the top level) — pre-existing, affects only
  the `xmatch` command's solution *set*, not reduce/rewrite. The optimized matcher is also a prerequisite for
  heavy AC `search`.
- *(Resolved — the whole view-frontend, including chained instantiation, now loads the prelude's container
  views. See the Resolved section.)*
- **Sort computation.** Least sorts come from direct `findMinSortIndex`-style iteration (down-set GLB), not
  Maude's precompiled **flattened sort-decision diagram**. Same result; the diagram is a per-application
  speedup.
- **Throughput headroom generally.** fib runs ~6–8 M rw/s (session-noisy); Maude is faster on compiled
  matching. The gap is matcher/sort-table compilation, not the reduce loop or GC, which are already iterative
  and bounded. (One deliberate cost: C7's `nf` field adds ~6% to no-sharing reductions like fib — accepted
  for the structure-sharing count fidelity it buys.)

## 3. Deferred sub-features (within built areas) + robustness

- **Operator attributes `memo`; `frozen` partial.** `frozen` (`frozen`/`frozen (…)`) is now parsed and wired
  into the **rewriting** layer (Pillar A-ii): `rewrite`/`frewrite` (and `search`, A-iv) never apply a rule
  within a frozen argument — note this blocks *rules*, not equational reduction, which is Maude's actual
  semantics. `memo` (result caching) is still parsed-and-ignored — add it as a perf cache.
- **`frewrite` over a custom `strat` (lazy positions).** Our `frewrite` reduces equationally between rule
  steps at every position. Maude's `lazyMarker` suppresses that reduction *inside a non-eager (lazy) subtree*
  of an operator with a custom `strat`. Only observable for the rare combination of a `strat`-annotated
  operator that is also `frewrite`d into a lazy argument; default-strategy modules (every conformance fixture)
  are unaffected. The eager/lazy bit is already on `Symbol` (`strategy`); threading it through the traversal is
  a localized follow-up. (`frewrite_pass` also recurses on subject depth — shallow for object/config terms, an
  explicit-stack rewrite is the same follow-up as C12 if a deep rule structure ever appears.)
- **On-the-fly variables — kind form only.** Inline `name:Sort` colon variables (the idiomatic `search` goal
  `X:St`, legal anywhere a term is) are **done**, including **structured** sorts: the lexer keeps a
  `name:Base{…}` colon variable in one token (`L:List{Nat}`, and the chained `X:Box{A}{B}`) — a plain sort
  `List{Nat}` with no colon still splits on the braces — and a `Terminal::ColonVar` grammar terminal matches
  the whole token, the part before `:` becoming the variable name (so `X:Nat`/`X:Foo`/`X:List{Nat}` are
  distinct), echoed back with its sort. The instantiation path produces the same single-token form (a
  parameterized module's variables are inlined as single-token colon variables at their instance sorts,
  `flatten.rs`). The *remaining* form is the **kind** variable `X:[Foo]` (sort = a kind/error sort, square
  brackets) — but this is **not** a colon-var lexing gap: kind-level bracket sorts are unsupported across the
  whole surface, so even `op g : [B] -> [B]` fails to parse (`sort_name` has no `[…]` case; the error sort,
  which exists internally and is named `[B]`, is not registered as a parseable sort; the per-kind grammar
  productions exclude it). Making `[Kind]` sorts first-class is the kind-variable machinery Maude bundles with
  **`poly`/`Universal`** (`var B : [Bool]`) — roadmap item 3 / Axis B, a separate feature from parameterization,
  not a loose end of it.
- **Lexer parity (vs `lexer.ll`/`token.cc`).** Our tokenizer is stateless (whitespace + the same special
  splitters `()[]{},`, the same terminator-dot rule); Maude's is parser-driven and stateful (ID/CMD/BUBBLE
  modes, the bubble handshake) — replaced by our explicit surface parser. Audited differentially against the
  reference; **bracketed comments `***( … )` / `---( … )`** (balanced parens across newlines, backquoted
  parens excluded — Maude warns on a stray-`(` line comment like `*** (foo).`, and so do we) and **strings
  glued into a maudeId** (`foo"bar"`/`"x"y` are one identifier; a lone `"hi"` is a `Str` constant — Maude's
  `Token::computeSpecialProperty`) are both now handled, byte-identically. Two divergences remain, both rare
  and unexercised by the prelude/conformance: (a) a backquote before a *normal* char (`a`b`) is a token
  **separator** in Maude (`a`b` ≡ the two-token name `a b`, printed `a b`); we drop the backquote → `ab`,
  which mis-prints *and* silently **merges** a distinct `a`b` and `ab` (a wrong *result*, not just a name).
  This is a special case of multi-token prefix op names, which our term parser does not support at all
  (`op a b : -> S` likewise fails to parse), so it is not fixable standalone; the sole real occurrence is the
  prelude's `op_to`term_.` (a view op-to-term map, behind the deferred view op-maps). Escaped *specials*
  (`` `[_`] ``, `<_`,_>`) are byte-identical either way — both engines map the backquoted special to the
  bare-char grammar terminal. (b) the terminator-dot heuristic (`is_terminator_dot`) approximates Maude's
  mode-based SEEN_DOT rule and could differ on the idiom-rare *two-commands-on-one-line* case. (Leading-zero
  numerals like `00`/`01` are **not** a divergence — verified: both engines lex them as one token then
  reclassify by value, so `00` fails to parse and `01` reduces to `1`; our `classify`→`Number` +
  `SmallNat`-grammar-terminal two-stage split reproduces Maude's exactly.) The `latex`/file-name lexer
  sub-modes are for unbuilt features.
- **`search` tracing.** `search` runs with `trace` off; `set trace` + a traced search (per-state rewrite
  trace, `set trace select`/`rls`) is a follow-up. Results/counts are unaffected.
- **Rewrite-condition (`=>`) trace.** A `crl ... if t => p` condition's *result, bindings, and rewrite
  count* are byte-conformant (Pillar A-v), but the detailed trace of its **nested `=>*` search** (the
  per-state trial stream) is not pinned to Maude — the fragment renders, but the inner search steps
  aren't traced. Same family as `search` tracing above.
- **Diagnostics sink.** Maude warns on non-preregular signatures, collapse-prone membership patterns, etc. We
  compute the preregularity bit but emit no warning (no diagnostics surface yet). Results are unaffected; the
  user-facing advisory text is missing.
- **Collapse matching under an identity.** A pattern whose top operator has an identity element (`id:`) can
  *collapse* — `S , S` matches a bare `empty` with `S = empty` (both sides the identity), and `mb a L : Lst`
  with `[id: nil]` matches the collapsed sub-element. Maude applies such an equation/membership to the
  collapsed case too (and **warns**: *"collapse at top of … may cause it to match more than you expect"*); we
  don't. The visible effect is a rewrite **count** one higher in Maude — e.g. `eq (S , S) = S` fires once more
  on the `empty` an accumulator like `makeSet(nil) = empty` produces (`conformance/instantiation-list-and-set`
  reduces to the right value but counts one low per such `empty`). **Reproduces in a non-parameterized
  module** — orthogonal to parameterization, a property of the AC/collapse matcher — and Maude itself flags
  the pattern. Result/sort always faithful.
- **Interruptibility.** Maude's Ctrl-C aborts a runaway reduce; our REPL can't yet interrupt an in-progress
  reduction (a signal-checked reduce loop — the real concern once `rew`/`search` can diverge). Note: this is
  *not* the rejected F-1 "no-op rewrite guard" — Maude itself loops on `eq a = a`, and we match that; adding a
  guard would *introduce* a divergence.
- **Parameterized-module statements built only at the instance (Pillar B-iv).** Instantiation `M{V}` flattens
  `M`'s statement *bubbles* into the instance and builds them there; we never build the parameterized module
  `M` standalone (with one exception: a *standalone* `flatten` of a parameterized module — e.g. for
  `show module` — does build `M`'s own statements, but using `M`'s own parameter copy). So a statement that is
  **ill-typed in `M` but well-typed after the substitution** is wrongly accepted at the instance, where Maude
  builds-and-rejects `M` once. Ill-formed-spec only — every well-formed prelude module typechecks in `M` — but
  it is a genuine architectural asymmetry vs. Maude's build-then-instantiate.
- **Built-in string ops are byte/ASCII-oriented (Tier 2).** Maude's strings are byte sequences; ours wrap a
  Rust UTF-8 `str`, and the string ops (`length`/`substr`/`find`/`rfind`/`ascii`/the `ctype` predicates/
  case/trim) index by **char**. For ASCII content — every conformance case, and the prelude's own use —
  char index ≡ byte index, so they are byte-identical; a string holding a multi-byte UTF-8 scalar would
  diverge from Maude's per-byte semantics. `char(n)`/`ascii(c)` likewise use the Unicode scalar value,
  which equals the byte for 0–127.
- **`decFloat(f, 0)` (exact full expansion) for extreme subnormals.** The exact path needs the float's
  denominator exponent `k` (`|f| = num/2^k`) to fit a machine word; for `k ≥ 64` (tiny subnormals) it falls
  through (unreduced) rather than computing a 300+-digit expansion. Finite `prec > 0` and all normal-range
  floats are exact. Off any real conformance path.
- **A malformed reduce/match *bubble* can still blow up the Earley parser.** A genuinely unparseable command
  term against a large module's grammar (e.g. a typo, or the old `red in M : t` before the qualifier existed)
  can enumerate exponentially. The `in <MODULE> :` qualifier (added in Tier 2) removes the common trigger
  (the module name is parsed structurally, not as part of the term); a true typo in a big module is still a
  latent hang. A parse-timeout / ambiguity cap is the fix when it matters.
- **META-LEVEL descent — corner inputs (the reflection core, item 3(c) Stage 3).** The rewriting/matching/
  search family computes byte-identically (value + rewrite count) on the common inputs; four corners are
  deferred, each tied to a **different** subsystem — so they are *not* one META subphase (the roadmap's
  Stage-3.5 is the separate, coherent `format`-display prerequisite, not these). (a) A **conditional rule** in
  `metaApply`/`metaXapply` and a **conditioned** `metaMatch` need the descent **condition evaluator** — the
  engine already evaluates `ceq`/`crl` conditions internally; exposing a reusable "eval-under-substitution,
  enumerate" seam is the work. Until then a labelled conditional rule keeps `metaApply` inert (never
  misfires), and a non-`nil` `metaMatch` such-that returns `None`; `metaSearch`'s such-that already rides the
  engine's native search. (b) A **non-empty partial substitution** σ to `metaApply`/`metaXapply` (down σ +
  seed/filter the matcher) — only the empty `none` is handled. (c) The **AC-residue `metaXmatch` context** —
  a proper sub-multiset match (`op([], residue)`) rides the AC matcher's residue extraction (same area as the
  `xmatch`-over-enumerates note in §2); a whole-subject match (context `[]`) is handled, a partial AC match
  stays inert rather than report a wrong context. (d) The **exhausted-search count** — asking `metaSearch`/
  `metaSearchPath` for a solution past the last over-counts the sibling expansion (a `search.rs`
  solution-enumeration snapshot detail, off every success path). The `format`-attribute *display* of a
  descent result is the Stage-3.5 pretty-printer item, not a corner here.

## Resolved (here for cross-reference; detail in git history)

The Phase-1.5 sweep closed: eager→lazy membership timing (C1), cross-theory alien-subterm matching (C8/C5),
the engine-global condition-reduce GC root set (C6/F-2), structure sharing (C7), the frontend-fidelity cluster
(float/glued-minus/rational/echo, C9–C11), the deep-chain pretty-printer overflow (C12), and long-output
line-wrapping (C13). The F-3 (ExtensionInfo) / F-4 (`Subst` unbind) matcher-seam gaps were closed in B1.

The Pillar-B "Axis A" parameterization corner cases all landed: view op-maps (A1), import/view-target dedup
(A3), theory-vs-module-declared sorts (A4), and — the entangled hard pair — parameterized views + free-vs-
bound nested instantiation (A2/A5: all three argument kinds — module-view, by-parameter, theory-view —
including `LIST{List{Nat}}`-style nesting). That work also closed **cross-kind ad-hoc operator overloading**
in the kernel (a constructor spanning several connected components, e.g. nested-container `cons`/`nil` — now
distinct symbols selected by argument kind, with Maude's `(t).Sort` print/parse disambiguation) and
**memberships over structured sorts** (`mb t : NeList{X}`).

Tier 2 (the remaining built-in data types) landed byte-identically: `INT` (`abs`/`~`/signed two's-complement
bitwise), `RAT`, `FLOAT` (full op set + Maude's partiality — `/0`/NaN stay at kind `[Float]`), `STRING`/`QID`
(+ STRING-OPS `ctype`/`trim`), `CONVERSION` (exact float↔rational, base conversion, `decFloat`), and the leaf
specials `CommutativeDecomposeEqualitySymbol` / `RandomOpSymbol` (MT19937) / `CounterSymbol` (a stateful
*rule*-special). It also closed five cross-cutting seams: the **`in <MODULE> :` command qualifier**, a
**`Term::Na` literal** (built-in constants in an equation rhs), **value-dependent NA sorts** (`Char`/`String`,
`FiniteFloat`/`Float`), **`~>` partiality tracking** (a partial op ranges over its kind), and a
**punctuation-aware `split_mixfix`** (operators whose names lex with brackets/commas — `_=[_]_`, `<_,_,_>`,
`[]`, `{}`). Verified by `conformance/prelude-tier2.maude` + `prelude_tier2_through_repl`.

The prelude's **parameterized container views** and **chained instantiation** now load — closing the last
Axis-A5 residual. The parser side: parameterized view declarations, structured-sort renamings (`renaming()`
→ `sort_name`, reading a chain of `{…}` groups), and a `[_]`-list rhs / trailing `[owise]` in equations
(split at the last top-level `=`, attribute-keyword-gated `[attrs]` peel). The flatten side: a chain
`M{ToTheory}{Arg}` binds the parameter's `$`-sort to only the **final** level (`X$Elt`, not the malformed
`ToTheory}{X$Elt`) while the structured sort keeps the full chain, and a chained import's **renaming items**
are parameter-substituted so the chain name collapses level by level. So `NAT-LIST`/`QID-LIST`/`QID-SET`
build & reduce, the `[_]`-list `LIST*`/`SET*` build, and the `SORTABLE-LIST` family loads — `SORTABLE-LIST
{Nat<}` sorts byte-identically. A duplicate `if_then_else_fi` (a parameter theory's `protecting BOOL` and a
regular `BOOL` import) is folded by an idempotent Branch re-attach. Verified by
`conformance/{instantiation-chained,view-parameterized,eq-bracket-rhs}.maude`. The only prelude modules that
still don't build are `META-LEVEL` (Tier 3) and the `QID-LIST`-via-objects `LEXICAL`/`LOOP-MODE` + the
`[object]` attribute (Phase 2 item 5).
