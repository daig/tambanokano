# Bootstrap — A2 + A5: parameterized views + nested / bound instantiation

*Focused design doc for the next session. The hardest remaining piece of Pillar B (the A5 §4 "top risk").
Once A2+A5 lands, fold the durable parts into `gaps.md` + git history and retire this file (as the numbered
phase docs were). Everything you need to start is here.*

## 0. Where we are (don't re-derive)

Pillar B's mechanism (B-i…iv) and Axis-A items A1/A3/A4 are **done and conformance-verified** (commits
`91285d7`…`50625db`; 269 tests, clippy `-D`, fib(22)=186579). The whole module system is a pure
`tnk-modules` `PreModule → PreModule` transform — **the kernel and grammar never change** (a structured sort
name like `List{X}` / `Box{ToColor}` is just a `String`-keyed sort). A2+A5 stays entirely in `tnk-modules` +
the frontend parser.

**What works today (the seams to extend):**
- `surface/ast.rs`: `ModuleExpr::Instantiation(Box<ModuleExpr>, Vec<String>)` — **args are `String` view
  names**; `ViewDecl { name, from, to, sort_maps, op_maps }` — **no params**; `Parameter { name, theory }`;
  `PreModule.params`.
- `surface/parser.rs`: `module_atom` → `instantiation_args` reads bare **names**; `view()` **rejects** a `{`
  after the view name (parameterized view name); `param_list` parses `{X :: T, …}`; `sort_name()` assembles
  structured sorts.
- `tnk-modules/flatten.rs`: `collect_expr`'s `Instantiation` arm → `instantiate()`. Today it handles **only**
  a **module-view, free-parameter, non-parameterized-view** instantiation: for each param, look up the view,
  import its (named) target via `view_target()`, build a `ParamBinding { view_name, sort_image }`, then
  `instantiate_decls` rewrites M's own decls via `inst_sort` (`X$s ↦` view sort-image; `Base{…X…} ↦
  Base{…view…}`) and `subst_ops` (A1 op-maps). `add_parameter_copy` + `module_origin_sorts` build the
  standalone parameter copy (`s ↦ X$s`, theory-declared sorts only).
- `tnk-modules/view.rs`: `validate_view` (sort-target check); `ViewDb`.

## 1. The feature: A2 and A5 are ONE thing

A parameterized view `view List{X :: TRIV} from TRIV to LIST{X} is sort Elt to List{X} . endv` can only be
*exercised* by a nested instantiation — `LIST{List{Nat}}` = instantiate `LIST` with the view `List` applied
to `Nat`. So "parameterized views" (A2) and "nested / bound instantiation" (A5) are the same feature; build
them together.

## 2. The C++ model (this is the part to get right)

`ImportModule::makeInstantiation` (`instantiateModuleWithFreeParameters.cc:34`) runs three phases — one per
**kind of argument** a parameter can be instantiated by. An argument is **a View** (which may itself be
parameterized / be a view *to a theory*) **or a Parameter** (the enclosing module's parameter).

1. **Theory-view** (`handleInstantiationByTheoryView`, `:153`): the argument is a view whose target **is a
   theory** (`toModule->isTheory()`). The parameter **keeps its name, changes its theory** to the view
   target's, and **does not disappear** — the instance is *still parameterized* (an "extra parameter").
   *Prelude:* `STRICT-TOTAL-ORDER from STRICT-WEAK-ORDER to STRICT-TOTAL-ORDER` and the chain views.
2. **By-parameter** (`handleInstantiationByParameter`, `:242`): the argument is a **`Parameter`** from an
   enclosing module — `fmod M{X :: T} is protecting LIST{X} . …` instantiates `LIST` *by the parameter* `X`.
   The instantiated parameter **keeps its theory, changes its name** to `X`, and **becomes bound**. Multiple
   params → same enclosing param collapse to one bound parameter.
   *Prelude:* `LIST-AND-SET{X :: TRIV}` `protecting LIST{X}` / `protecting SET{X}` (line 1247).
3. **Module-view** (`handleInstantiationByModuleView`, `:341`): the argument is a view whose target **is a
   module** — the common case B-iv already does. **But** the argument view may itself be *parameterized*
   (`handleBoundParameters`, `:416`): its bound parameters are added as **bound parameters of the instance**.
   *Prelude:* `LIST{Nat}` (done) and `LIST{List{Nat}}` (the `List{Nat}` argument view is the parameterized
   view `List` instantiated by `Nat`; its target is `LIST{Nat}`).

Then: `handleParameterizedSorts`/`Constants` rename `Sort{X}`/`pconst` per the parameter map;
`handleRegularImports` re-imports M's imports, calling **`instantiateBoundParameters`** on any that still
carry bound parameters (the recursion — `:563`).

**Free vs bound, in one line:** a parameter is **free** when it's being instantiated *now* (by a view), and
**bound** when it's instantiated *by an enclosing parameter* (kind 2) or *inherited from a parameterized
argument view* (kind 3 / `handleBoundParameters`) — bound parameters survive into the instance and get
re-instantiated later by `instantiateBoundParameters`. B-iv only ever produced **free, fully-ground**
instances (no bound parameters), which is why it could be a flat substitution.

## 3. Two worked examples (build self-contained fixtures from these)

**(a) Parameterized view, fully ground** — `/tmp`-probe shape, binary-verified:
```
fth TRIV is sort Elt . endfth
fmod COLOR is sort Hue . op red : -> Hue [ctor] . endfm
view ToColor from TRIV to COLOR is sort Elt to Hue . endv
fmod BOX{X :: TRIV} is
  sort Box{X} .  op wrap : X$Elt -> Box{X} [ctor] .  op peek : Box{X} -> X$Elt .
  eq peek(wrap(E:X$Elt)) = E:X$Elt .
endfm
view BoxV{X :: TRIV} from TRIV to BOX{X} is sort Elt to Box{X} . endv   *** parameterized view
fmod USE is protecting BOX{BoxV{ToColor}} . endfm
red peek(wrap(wrap(red))) .   *** binary: wrap(red) : Box{ToColor}, 1 rewrite
```
Resolution: `BoxV{ToColor}` is the view `BoxV` instantiated by `ToColor` → a derived view `from TRIV to
BOX{ToColor}` with `sort Elt to Box{ToColor}` (the target `BOX{X}` and the map image `Box{X}` both get
`X ↦ ToColor`). Then `BOX{BoxV{ToColor}}` is a module-view instantiation with that derived view:
`X$Elt ↦ Box{ToColor}`, `Box{X} ↦ Box{BoxV{ToColor}}` (the *instance name* uses the *argument's* name).
This case has **no bound parameters** (everything is ground) — so it may be reachable by **recursively
resolving the argument view to a concrete derived view**, then reusing the B-iv flat substitution. Try this
first; it likely covers `LIST{List{Nat}}`.

**(b) By-parameter (bound)** — the genuinely new machinery:
```
fmod LIST-AND-SET{X :: TRIV} is protecting LIST{X} . protecting SET{X} . … endfm
```
`LIST{X}` instantiates `LIST` *by the enclosing parameter* `X` → the imported content has `X$Elt` (LIST's
`Y$Elt` renamed to the enclosing `X$Elt`) and `List{X}` sorts; `LIST-AND-SET` stays parameterized in `X`.
When later `LIST-AND-SET{Nat}` is instantiated, the bound `X` is re-instantiated (the recursion). This is
where free/bound, the parameter map, and `instantiateBoundParameters` all bite.

## 4. What to change

**Parser (tractable — do first, behind its own commit):**
- `ModuleExpr::Instantiation`'s args: `Vec<String>` → `Vec<ModuleExpr>` (an arg can be a name, OR a nested
  instantiation `BoxV{ToColor}`, OR — for kind 2 — a bare enclosing-parameter name). Update
  `instantiation_args` to parse a `module_expr` per arg; update `canonical_key` + `module_expr_str` (REPL).
- `view()`: after the view name, accept an optional `param_list` → `ViewDecl.params: Vec<Parameter>`. The
  `to` is already a `ModuleExpr`, so `to BOX{X}` parses once instantiation args are expressions — but
  `view_target()` must stop rejecting a non-`Named` target.
- Distinguishing kind-2 (bare enclosing-parameter name) from a 0-ary view name is **contextual**: an arg
  that matches an enclosing `PreModule.params` name is a Parameter; else it's a view. Thread the enclosing
  module's parameter names into `instantiate()`.

**flatten (the algebra — the fragile part):**
- Generalize `instantiate()` so an argument is resolved to one of {theory-view, module-view (possibly
  parameterized), by-parameter}. Start with **kind 3 / ground nested** (example a) by recursively resolving
  a parameterized-view argument to a concrete derived view (compose the inner instantiation into the view's
  `to` and `sort_maps`/`op_maps`), then reuse the existing flat path.
- Then **bound parameters** (example b): an instance can *retain* parameters (`PreModule.params` non-empty
  on the flattened result is currently impossible — `flatten` clears them). You'll need a representation for
  "a flattened-but-still-parameterized module" and a re-instantiation step = Maude's
  `instantiateBoundParameters`. This is the deep change; design it before coding.

## 5. Recommended increment order (each its own commit, diffed vs the binary)

1. **Parser**: args-as-expressions + parameterized view names + non-`Named` view targets. No new algebra
   yet — a nested instantiation should *parse* then fail in `instantiate()` with a clear "not yet" error.
2. **Ground nested (example a)**: resolve a parameterized-view argument to a concrete derived view; reuse the
   flat substitution. Fixture: the `BOX{BoxV{ToColor}}` probe. Likely also lights up `LIST{List{Nat}}`.
3. **Theory-views (kind 1)**: parameter keeps name, changes theory; instance stays parameterized.
4. **By-parameter / bound (kind 2, example b)** + `instantiateBoundParameters` recursion. The hard core —
   design the "still-parameterized instance" representation first. Fixture: a hand-rolled `LIST-AND-SET`
   shape.
5. Only after the above: the real prelude containers (needs Axis B `poly`/`Universal` too — separate).

## 6. Conformance

Self-contained hand-rolled fixtures first (no real prelude needed — every example here is). Then differential
against `~/Downloads/Maude-3/prelude.maude`'s `LIST`/`SET`/`LIST-AND-SET`/`MAP` once Axis B lands. Harness as
usual: `~/Downloads/Maude-3/maude -no-banner f.maude </dev/null` vs `./target/debug/tnk-repl f.maude`,
normalizing the `rewrites/second` rate. **Fixture traps (cost real time before):** no `*** (` (opens a
bracketed comment), no non-ASCII (em-dash `—`), and `is_top_level_keyword` must contain every block keyword
or a one-line `… . endX` mis-lexes the `.`.

## 7. Gotchas / risks

- **Instance naming composition** (`Box{X} ↦ Box{BoxV{ToColor}}` *while* `X$Elt ↦ Box{ToColor}`): the
  structured-sort image uses the *argument's printed name*, the parameter-sort image uses the *view's sort
  map*. `inst_sort` already splits these; extend it for expression-valued args.
- **The ill-typed-statement edge** (`gaps.md`): instantiation builds M's statement bubbles only at the
  instance, never building M standalone. Nested instantiation deepens this — watch it.
- **Free/bound is where parity breaks silently**: a wrong free/bound classification gives a *plausible wrong
  sort*, not a crash. Lean on differential tests at every sub-step.
- This is the one place to **prefer a clean design pass over speed**. Sketch the "still-parameterized
  instance" data model and the three-kinds dispatch before writing `instantiate()` v2.
