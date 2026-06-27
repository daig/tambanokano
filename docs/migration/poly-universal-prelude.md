# Bootstrap — Phase 2 item 3: `poly`/`Universal` polymorphism + the real `.maude` prelude

*Self-contained design doc for the next session — the gateway from "verified on hand-rolled fixtures" to
"runs the actual Maude library". Everything else (functional engine, rewriting, the whole module algebra
incl. parameterized programming / Axis A) is done. Retire this file once the prelude loads (fold the durable
parts into `gaps.md` + git history, as the A2–A5 bootstrap was). File:line refs verified against the code at
authoring time — re-confirm before relying on any single line.*

## 0. The exact blockers (probe `./target/debug/tnk-repl ~/Downloads/Maude-3/prelude.maude`, 3,234 lines)

In first-hit order:
- **`set` directive** — `set include BOOL off .` (prelude:31) → `unexpected top-level token "set"`
  (`parser.rs` `parse_top_item` default arm).
- **`SystemTrue`/`SystemFalse`** — `op true : -> Bool [ctor special (id-hook SystemTrue)]` (prelude:34-35)
  → `unsupported special id-hook` (`build_sig.rs` `special_op`'s `other => Err`). Re-fires in every module
  flattening TRUTH-VALUE.
- **`Universal`/`poly`** — `if_then_else_fi : Bool Universal Universal -> Universal [poly (2 3 0) …]`
  (prelude:60-64), `_==_`/`_=/=_` (prelude:66-76) → `unknown sort Universal` (`build_sig.rs` `sort_id`).
  `poly` is currently silently discarded (`parser.rs` attr arm).
- **`[Bool]` kind sort in a var** — `var B : [Bool] .` (prelude:88, EXT-BOOL) → `expected '.', found "Bool"`
  (`sort_name` has no `[…]` form). **Off the `LIST{Nat}` path** (EXT-BOOL is a leaf) — defer.
- **`~>` partial arrow** — `op modExp : Nat Nat NzNat ~> Nat` (prelude:154) → the op-domain loop only stops
  at `->`. Needed for NAT to build.
- The trailing `expected a name … line 52` is a downstream resync cascade — re-probe after the above land.

**The kernel needs no new reduction code.** `SpecialOp::{Equality, Branch}` already exist and reduce
correctly on concrete decls; `Branch` auto-installs its own lazy `strat (1 0)`. All work is frontend +
surface + a handful of arithmetic codes.

## 1. The `poly`/`Universal` model

**C++ mechanism** (`~/code/maude-lang/Maude/src/Mixfix`): `Universal` is **not a sort** — a polymorphic
position is a **null `Sort*` (0)** in the op's `domainAndRange`; `Universal` is only a print label
(`visibleModule.cc:602,607`). `struct Polymorph` (`mixfixModule.hh:565-578`) holds the name, the
`domainAndRange` (0 at poly positions), the id/op/term hooks, and a `Vector<Symbol*> instantiations` cache.
`poly (2 3 0)` is 1-based for args, `0` for the range (so `if_then_else_fi : Bool U U -> U` →
`domainAndRange = [Bool, 0, 0, 0]`; `Bool` is *not* poly). `instantiatePolymorph(polyIdx, kindIdx)`
(`mixfixModule.cc:868-957`) copies the profile, replaces each `0` with that component's **kind/top (error)
sort** (`sort(Sort::KIND)`), builds a concrete `Symbol`, re-attaches the same hooks per instance, and
memoizes. It's lazy (triggered at symbol lookup, `mixfixModule.cc:520-556`), runs **after** sorts close;
grammar productions are made eagerly per component (`makeGrammar.cc:1524-1539`).

**How it maps onto our kernel.** Our `build_sig` already makes same-name ops in *different domain-kind
profiles* distinct symbols (the `(name, dom_kinds, range_kind)` key) and grammar-disambiguates them — which
is exactly what per-kind poly instances are. So:

> **Eager per-kind expansion in `build_sig::build_module`, after `close_sorts()`, folded into Pass A.** For
> each op carrying `poly`, loop `k in 0..num_kinds()`; build a concrete `domain`/`range` where each poly
> position → `engine.sorts().error_sort(k)` (= Maude's `sort(Sort::KIND)`) and every other position → the
> real `sort_id`; run the existing `declare_op` + profile-group + syntax-record + special-attach on it.
> **`Universal` is never passed to `sort_id`** — the `poly` attribute drives the substitution — so "unknown
> sort" never arises. This must live in `build_module` (not `tnk-modules` flatten): kinds/error-sorts don't
> exist until `close_sorts`.

Eager (all kinds) vs Maude's lazy (used kinds) is observationally identical for `red`/`match`/`search`
(reduction dispatches on the node's actual symbol); the only difference is `show module` / symbol
enumeration (§7).

## 2. SystemTrue/False + the truth / equality / branch substrate

`SystemTrue`/`SystemFalse` are **markers**, not rules (`specialSymbolTypes.cc:31-32`; `entry.cc:609-640`
records `trueSymbol`/`falseSymbol`/`boolSort`). They are read by sort-test predicates and **bare boolean
conditions** — `_==_`/`if_then_else_fi` do *not* read them (they carry true/false via explicit `term-hook`s).

- **Have:** `SpecialOp::Equality { eq, neq }`, `SpecialOp::Branch { tests }` (resolved at `build_sig.rs`,
  already byte-correct on concrete decls); marker hooks returning `None` (Succ/String/Float/Qid).
- **Missing for M0:** the `SystemTrue`/`SystemFalse` marker arm (add `"SystemTrue" | "SystemFalse" =>
  Ok(None)`), and recording `true_sym`/`false_sym` anchors on `BuiltModule` in Pass A2 (needed by §6.4 bare
  conditions + later sort-test predicates).

**Composition with poly is clean:** the poly expansion just *generates* the concrete `_==_ : [K] [K] -> Bool`
/ `if_then_else_fi : Bool [K] [K] -> [K]` decls; attaching the existing `Equality`/`Branch` to each instance
(the per-kind hook re-attach Maude does) gives correct behavior with **zero new kernel code**. The `Branch`
guard forbids an *explicit* strat — the prelude's `if_then_else_fi` declares none. `_=/=_` is the same
`Equality` with `eq`/`neq` swapped.

## 3. Prelude dependency chain + milestone ladder

`TRUTH-VALUE`(33) → `BOOL-OPS`(39) → `TRUTH`(58) → `BOOL`(79) → `EXT-BOOL`(84, leaf) →
`INITIAL-EQUALITY-PREDICATE`(95, leaf) → `NAT`(110) → `INT`(244) → `RAT`(409) → `FLOAT`(542) → `STRING`(687)
→ `CONVERSION`(773) → `QID`(842) → std theories/views `TRIV`/`STRICT-*`/`DEFAULT`(864-1015) →
**`LIST`(1017), `SET`(1177), `MAP`(1498), `ARRAY`(1535)** → … → **`META-TERM`(1677) = the reflective wall**.

| Milestone | Modules | New feature |
|---|---|---|
| **M0** — `BOOL` loads; `red true and false .` byte-identical | TRUTH-VALUE, BOOL-OPS, TRUTH, BOOL | §1 poly, §2 SystemTrue/False, §4 `set` skip |
| **M1** — `NAT` loads; `red 2 + 3 .`/`7 quo 2`/`5 xor 3` byte-identical | NAT | §4 `~>`; NAT codes — `ACU_NumberOpSymbol` `xor`/`&`/`\|`, `CUI_NumberOpSymbol` `sd`, `NumberOpSymbol` `modExp`/`>>`/`<<` |
| **M2** — `LIST{Nat}` loads; `occurs`/`size`/`reverse` byte-identical | LIST (+SET/MAP/ARRAY) | resilient loading (§5); containers reuse only BOOL+NAT+TRIV |

`LIST{X}` `protecting NAT` ⇒ M1 is a hard prerequisite for M2. INT/RAT/FLOAT/STRING/QID are **off the
`LIST{Nat}` path** — defer them.

## 4. Surface-syntax gaps (precise)

1. **`set …`** — add a `"set"` arm to `parse_top_item` consuming through `.` → a benign no-op (the REPL
   already routes interactive `set` before parsing, so no conflict). The prelude has exactly one `set` (a
   no-op for us).
2. **`Universal`** — **no parser change** (it lexes/parses as a sort name); only `build_module` skips
   resolving poly positions (§1). Stop discarding `poly`: parse `poly ( n… )` into `Attrs.poly: Option<Vec<u32>>`.
3. **`var B : [Bool]` / `[Sort]` kind notation** — `sort_name` has no `[…]` form. **Not needed for M0-M2**
   (only EXT-BOOL, a leaf). Follow-up: accept `[ <sort_name> ]` in `sort_name`, resolving to
   `error_sort(kind_of(inner))`. (This is also the `X:[Foo]` kind-variable gap from `gaps.md`.)
4. **`~>` partial arrow** — op-domain loop → `while !at("->") && !at("~>")`, eat whichever; treat `~>` like
   `->` (we don't track partiality for reduction; kind-level results fall out of the sort machinery).

## 5. Wiring the prelude

**Can't just `load_program(prelude.maude)`** — (a) later modules (META-*, RANDOM, LOOP-MODE, CONFIGURATION)
need hooks far beyond this item; (b) `load_program` is all-or-nothing (`parse_source()?` + the build loop
returns `Err` on first failure). **Minimal seam = resilient per-module loading** (mirror the REPL's
`enter_module`: record a per-module build error, keep going). Views validate string-level (no engine build),
so a `Nat` view validates even if INT's build is skipped. No module search path / `in`/`load` directive
needed — the prelude is one self-contained file. For the byte-diff milestones, the lowest-risk path is the
existing fixture idiom: trimmed `conformance/prelude-{bool,nat}.maude` (the relevant modules copied verbatim)
vs `~/Downloads/Maude-3/maude -no-banner`; M2 adds `fmod T is protecting LIST{Nat} . endfm` + reduces (the
import already triggers flatten/instantiation). Bundling the whole prelude into the REPL's `ModuleDb` at
startup is an M3+ convenience, not required for M0-M2.

## 6. Increment order (each self-contained + differentially verifiable)

1. **`set` skip** — parse-and-ignore. *Verify:* prelude:31 no longer errors.
2. **SystemTrue/False markers + anchors** — marker arm + Pass A2 records `true_sym`/`false_sym`. *Verify:*
   `fmod TRUTH-VALUE …` builds; `red true .` echoes `true`.
3. **poly/Universal expansion** — `Attrs.poly` capture; per-kind expansion in Pass A via `error_sort(k)`;
   attach existing `Branch`/`Equality`. *Verify (M0):* `red true and false .` → `Bool: false`, `1 rewrite`;
   `red true == true .` → `true`; `red if true then false else true fi .` → `false`; byte-identical.
   **Refactor caution:** Pass A's body must run once (non-poly) or N times (poly), and the per-instance
   special-attach moves into that loop (Pass B's `op_syms[idx]` assumes 1 symbol/decl).
4. **Bare-condition `= true` desugar** — `split_connective` on no-connective → `ConditionFragment::Equality
   { lhs: cond, rhs: true_sym }`. *Verify:* a `ceq r = … if pred(x) .` fires. Precondition for containers.
5. **`~>` arrow + NAT arithmetic codes** — parser `~>`; extend `NumOp`/`num_op` with `xor`/`&`/`|` (ACU
   bignum bitwise, multiplicity-aware), `sd` (new `CUI_NumberOpSymbol` → CUI fold), `modExp` (3-arg bignum
   modpow), `>>`/`<<` (free bignum shifts). *Verify (M1):* NAT builds; each new op byte-identical.
6. **Container milestone** — resilient loader (§5) or trimmed fixture; `protecting LIST{Nat}`. *Verify (M2):*
   `occurs`/`size`/`reverse` byte-identical.
7. **Follow-ups (non-blocking):** `[Sort]` kind notation + kind vars (EXT-BOOL / the `X:[Foo]` gap);
   `show module` poly print (keep templates, suppress concrete instances — §7); `load_program` resilience as
   a public API; INT/RAT/FLOAT/STRING completions; eventually the MetaLevel layer.

## 7. Gotchas / risks

- **Poly timing.** Expansion *must* run after `close_sorts` (needs kinds/error-sorts) and *within* Pass A
  (instances must flow through `sym_by_profile` to become distinct symbols **and** get `syntax` recorded so
  the grammar builds their productions). Not in `tnk-modules` flatten — no kinds there.
- **`Universal` has no sort.** Never `add_sort("Universal")` / `sort_id("Universal")`. Drive substitution
  from `Attrs.poly` (value `0` → range, value `n` → `domain[n-1]`); poly positions → `error_sort(k)`.
- **Eager-vs-lazy instances** are reduction-identical; the only observable gap is `show module` / symbol
  listing (Maude prints one `… Universal … [poly …]` line and hides instances). Keep a poly *template*
  record for that print path — doesn't affect any `red`/`match`/`search` fixture.
- **`Equality`/`Branch` overlap is a feature, not a conflict** — they already reduce correctly; poly only
  generates the decls. The dead-branch-not-reduced rewrite count stays exact (lazy `strat (1 0)`).
- **`__` + `if _==_ then`** in `LIST{X}`: `__` is AU `id: nil` (wired); `_==_` instantiates over the element
  kind and `if_then_else_fi` over `[Bool]` — both from the same expansion. Confirm `occurs`'s count.
- **NAT bitwise/`sd` semantics** — `xor`/`&`/`|` fold an ACU multiset (duplicate-cancellation parity
  matters — the existing `AcuNumberOp` framework does +/*; bitwise must respect multiplicity); `sd` is a new
  CUI fold (`|m−n|`). Differentially verify each, not from memory.

**Key files (ours):** `crates/tnk-frontend/src/sig/build_sig.rs` (poly expansion, SystemTrue markers, NAT
codes), `crates/tnk-frontend/src/surface/{parser.rs,ast.rs}` (`set`, `poly` capture, `~>`, `[Sort]`),
`crates/tnk-frontend/src/load.rs` (bare-condition desugar), `crates/tnk-core/src/symbol.rs` (`NumOp`),
`crates/tnk-modules/src/load.rs` + `crates/tnk-repl/src/lib.rs` (resilient load). **C++ refs:**
`mixfixModule.{hh:565-578, cc:327-340, 868-957, 520-556}`, `entry.cc:{735-852, 609-640}`,
`makeGrammar.cc:1524-1539`, `specialSymbolTypes.cc:31-32`. **Oracle:** `~/Downloads/Maude-3/prelude.maude`.
