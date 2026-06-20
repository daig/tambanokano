# A7 — Reflection / meta-level / meta-interpreters + built-in data ops (deep-dive report)

### 1. Functional scope
Maude is reflective: a universal theory `U` is reified inside the object level (manual §17.1, 8685-8697). The prelude builds the tower as ordinary modules — `META-TERM`, `META-CONDITION`, `META-STRATEGY`, `META-MODULE`, `META-VIEW`, `META-LEVEL` (8701-8952) — in which sorts/kinds/terms/strategies/modules/views are metarepresented as `Qid`-subsort data (`Constant`, `Variable`, `_[_]`, …; 8737-8943). On top sit: **level shifts** `upModule/upTerm/downTerm/upView/upImports/upEqs…` (§17.6.1, 8976-9044); **descent functions** `metaReduce/metaNormalize` (9046), `metaRewrite/metaFrewrite` (9102), `metaApply/metaXapply` (9140), `metaMatch/metaXmatch`, `metaSearch/metaSearchPath`, `metaUnify`/variant/narrow, `metaParse/metaPrettyPrint`, plus sort queries `metaSortLeq/metaSameKind/metaLeastSort/metaGlbSorts/…` (full set: `descentSignature.cc:31-89`). **Meta-interpreters** (manual ch19, 10322-10568): the `interpreterManager` external object spawns full nested `Interpreter` instances exchanging messages (`createInterpreter`, `insertModule`, `*Term`…), enabling a stateful reflective tower and remote (subprocess) interpreters. The **BuiltIn FFI seam** binds prelude ops to C++ via `special (id-hook …)` (number/string/float/equality/branch/succ; manual §4.4.10 & ch7 3765-4497; `prelude.maude:35,62,68,118,123`).

### 2. Architecture in C++
**Descent dispatch.** Each metalevel op is a `MetaLevelOpSymbol : public FreeSymbol` (`metaLevelOpSymbol.hh:33`). `attachData` string-matches the op name against an X-macro table (`metaLevelOpSymbol.cc:157-174` over `descentSignature.cc`) to set a **member-function pointer** `descentFunction` (`metaLevelOpSymbol.hh:78,157`). `compileEquations` installs `eqRewriteFast`, which reduces arguments then dispatches `(s->*(s->descentFunction))(d,context)`, falling back to user equations (`metaLevelOpSymbol.cc:277-290`). So there are two indirection layers: `setEqRewrite` function pointer → per-op member pointer table (not vtables).

**Reify/reflect.** The heavy lifting lives in `MetaLevel` (`metaLevel.hh`): ~100 `upXXX` reify methods (`metaLevel.hh:77-270`) and ~120 `downXXX` reflect methods (`metaLevel.hh:272-650`), with bound helper symbols/terms via X-macro `metaLevelSignature.cc` (`metaLevel.hh:654-657`). A typical descent fn (`metaReduce`, `descentFunctions.cc:314-335`) does: `downModule`→`downTerm`→`term2RewritingContext` (normalize, `term2DagEagerLazyAware`, `makeSubcontext(META_EVAL)`; `descentFunctions.cc:98-105`)→run engine→`upResultPair`→`context.builtInReplace`. Returning **false** = "undefined": the redex stays unreduced in the kind — this is how partiality and out-of-band results (`noParse`, `failure`) are realized (manual 8956-8974). `m->protect()/unprotect()` pins the `MetaModule` against GC during the call.

**Caches.** `downModule` builds a `MetaModule` (subclass of `ImportModule`) from a metaterm once, cached LRU (size 4) keyed by the metaterm DagNode (`metaLevel.hh:661`, `metaModuleCache.hh:31,53`). Multi-solution ops (`metaApply`, `metaXapply`, `metaMatch`, `metaSearch`, `metaUnify`…) cache an in-progress search/rewrite **state object** in a `MetaOpCache` keyed by the call term (ignoring trailing solution-number args), so enumerating solutions 0,1,2… is incremental (`metaApply.cc:41`, `metaOpCache.hh:52-56`); a stale parent-context pointer is patched via `beAdoptedBy` (`metaOpCache.hh:151`). `metaParse` similarly caches an `(AliasMap, MixfixParser)` pair (`descentFunctions.cc:442-491`).

**Meta-interpreters.** `InterpreterManagerSymbol : public ExternalObjectManagerSymbol, public PseudoThread` (`interpreterManagerSymbol.hh:34`) holds `Vector<Interpreter*>` + a `RemoteInterpreterMap`. `handleMessage` dispatches by message symbol (`interpreterManagerSymbol.cc:278-304`); `createInterpreter` allocates an `Interpreter` and returns `interpreter(n)` (`...cc:457`). Per-command `mi*.cc` files reuse the same `MetaLevel` up/down (a `shareWith` link shares one `MetaLevel`). Remote interpreters fork a subprocess and stream `Rope` messages over sockets nonblockingly via the `pseudoThread` loop (`interpreterManagerSymbol.hh:65-90`).

**BuiltIn seam.** Symbols bind hook data through `attach{Data,Symbol,Term}` + macros `BIND_OP/BIND_SYMBOL/BIND_TERM` (`bindingMacros.hh:32,35,83,103`). `NumberOpSymbol` packs the op as a 2-char `CODE` int, holds `succSymbol`/`minusSymbol`, and computes with GMP `mpz_class` (`numberOpSymbol.cc:182-472`). `EqualitySymbol` reduces both args and compares DAGs, returning `equalTerm`/`notEqualTerm` (`equalitySymbol.cc:126-137`). `BranchSymbol` (if-then-else) reduces arg0, matches against `testTerms`, returns the chosen branch, with custom lazy `stackArguments` (`branchSymbol.cc:163-185,231`). `SuccSymbol : S_Symbol` wraps bignums (`succSymbol.hh:32`).

### 3. Rust migration
- **Descent dispatch — RETHINK.** Replace the member-pointer + X-macro table with an `enum DescentFn` and one exhaustive `match`, or a `HashMap<OpId, fn(&MetaCtx,&[TermId])->Option<TermId>>` registry. Zero-cost, exhaustiveness-checked.
- **Reify/reflect — ADAPT.** Model as `trait Reify { fn up(&self, &mut Builder)->TermId }` / `trait Reflect: Sized { fn down(t: TermId, m:&Module)->Result<Self,DownErr> }` per Rust type (Sort, Term, Substitution, Module, View…). Partiality becomes `Result/Option`, replacing the "return false → unreduced in kind" convention (the engine maps `Err` back to the kinded/exception term).
- **Metarepresentation — PORT.** META-TERM/MODULE/… are plain prelude modules; only the symbol hooks must be wired. Port the `.maude` files unchanged.
- **Caches — ADAPT.** Module cache → `lru::LruCache<StructHash, Rc<Module>>`. Per-op solution state → store a Rust iterator/`Box<dyn SolutionStream>` keyed by call term; the `beAdoptedBy` pointer hack vanishes when contexts are passed per call.
- **Meta-interpreters — RETHINK.** The `ExternalObjectManagerSymbol + PseudoThread` multiple inheritance → a struct implementing an `ExternalObject` trait holding `SlotMap<InterpId, Interpreter>`; message dispatch by `match` on a message enum. The tower is just nested owned `Interpreter` values. Remote subprocess + socket + `Rope` nonblocking IO → `tokio`/`mio` async tasks (shared with A6's event loop).
- **BuiltIn seam — RETHINK binding, PORT math.** Parse `special(id-hook…)` into a typed `enum SpecialOp { Succ, NumberOp(NumberOp), Equality{eq,neq}, Branch{tests}, StringOp, FloatOp, … }` at module-build time, resolving op-hooks to symbol Ids; the `CODE` int trick → real enums. Arithmetic on `rug`/`malachite` bignums instead of gmpxx. Builtin reduction is an arm of the symbol's `reduce`, not a `setEqRewrite` pointer.
- **Does NOT translate:** the member-function-pointer descent table + X-macro codegen; `setEqRewrite` indirection; `InterpreterManagerSymbol` multiple inheritance; raw `DagNode*`/`CacheableState*` + `safeCast` caches; manual `protect()/unprotect()` GC pinning (ownership/`Rc` instead); `CODE()` packed ints; gmpxx.

### 4. Hardest parts / risks / open questions
- The reify/reflect surface is huge and must round-trip faithfully (`metaUp.cc`, `metaDown.cc` ~42k each; `metaUpModule.cc` ~35k): AC flattening, reduce-before-`upTerm`, on-the-fly variable decls, fixed statement/attribute ordering (manual 9020-9100).
- Incremental solution-state caching semantics (idempotent "give me solution n", `purge<T>` on theory reload) → faithful Rust iterators.
- Partiality-as-kind vs `Result`: must preserve user-visible distinction between `noParse(n):ResultPair?` and an unreduced `metaParse(...)` in the kind (8956-8974).
- Variable-family naming for unify/variant/narrow up-conversion.
- Meta-interpreter concurrency model + remote wire protocol.
- Open: keep `MetaModule` as a `Module` subtype (builder) or build a normal `Module` directly? Reuse the full `Interpreter` recursively, or a lighter meta-context?

### 5. Proposed Rust module layout
```
crate meta/
  repr.rs            # Reify/Reflect traits; Qid-subsort helpers; up/down Sort,Term,Cond,Subst
  up_module.rs / down_module.rs
  descent/           # one file per family, each fn(&MetaCtx,..)->Option<TermId>
    reduce.rs rewrite.rs apply.rs matcher.rs search.rs
    unify.rs variant.rs narrow.rs syntax.rs sortops.rs
    dispatch.rs      # enum DescentFn + table
  cache.rs           # module LRU + per-op solution-stream cache
  interpreter/{manager.rs, local.rs, remote.rs}
crate builtin/
  hooks.rs           # parse special(id-hook…) -> typed SpecialOp; resolve op/term hooks
  number.rs equality.rs branch.rs string.rs float.rs sort_test.rs
  bignum.rs          # rug/malachite wrapper (succ/minus/division/counter/random)
```
