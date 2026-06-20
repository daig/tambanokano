# A5 — Module system, parameterization, command interpreter (deep-dive report)

### 1. Functional scope
Covers: the named-module database and module kinds (`fmod/mod/fth/sth/oth/omod/smod`, manual §3.2); module importation in `protecting`/`extending`/`including`(/`generated-by`) modes with default conventions (§6.1); module expressions — summation `+`, renaming `*(...)`, instantiation `{...}` (§6.2); **parameterized programming** — theories, views, parameterized modules, instantiation, parameterized views and views-with-parameters (§6.3, §7.12–7.16); module & view caches; and the interactive interpreter — current module/view selection, the full command set (`reduce/rewrite/search/match/unify/...`), `set`/`show` options, `select`, `in`/`load`/`continue`/`loop`, control-C (§2.2, Ch.23).

### 2. Architecture in C++
`Module` (`Core/module.hh:35`) is the engine-level signature/statement container (Vectors of `Sort*`,`Symbol*`,`Equation*`,`Rule*`,…) with a monotone `Status` lifecycle `closeSortSet→closeSignature→closeFixUps→closeTheory→stackMachineCompile` (`module.hh:40-57`). Every contained object back-references its module via `ModuleItem` (`Core/moduleItem.hh:32`).

The front end splits a module into three layers. `ModuleDatabase` is `map<int,PreModule*>` keyed by name token, plus auto-import/oo-include maps (`moduleDatabase.hh:53`, `moduleDatabase.cc:55`). `PreModule` (`preModule.hh:33`) is the abstract "description"; `SyntacticPreModule` (`syntacticPreModule.hh:41`) holds the parsed surface syntax and lazily builds a flattened `VisibleModule` via `getFlatSignature()/getFlatModule()` (`syntacticPreModule.cc:147-192`), caching it in `flatModule`. The flattening driver `process()` (`process.cc:28`) runs the phased pipeline: `processImports → importSorts/processSorts → closeSortSet → importOps/processOps → closeSignature → importStrategies → fixUpImportedOps → closeFixUps → processStatements → closeTheory`.

`ImportModule` (`importModule.hh:34`) is the workhorse and inherits from **four** bases (`MixfixModule`, `Entity`, `Entity::User`, `EnclosingObject`). `ImportMode` is a bitfield (`NO_JUNK|NO_CONFUSION`, `importModule.hh:43-52`); `Origin` records how the module was built (`TEXT/SUMMATION/RENAMING/PARAMETER/INSTANTIATION`, `:54-61`). Flattening is done by **donation**: each import/parameter theory copies its sorts, ops, strategies and statements *into* the importer (`importModule.cc:382-902`), guarded by a per-module `Phase` enum so the DAG of imports is traversed once. Provenance counters (`nrImportedSorts`, `nrSortsFromParameters`, `nrUserSymbols`, …, `importModule.hh:321-385`) record where each item came from so renamings/views know what may be mapped. Statement donation deep-copies terms through an `ImportTranslation` (`importTranslation.hh:33`, a `SymbolMap` carrying a list of renamings+targets, caching symbol translations, and returning a null symbol to trigger op→term mappings).

Module expressions are an AST `ModuleExpression`/`ViewExpression` (`moduleExpression.hh:31`, `viewExpression.hh:35`). `Interpreter::makeModule()` (`interpreter.cc:797`) recursively evaluates it, delegating to a content-addressed `ModuleCache` (`moduleCache.hh:31`, `moduleCache.cc`) whose key is the **canonical Rope name** produced by `Renaming::makeCanonicalName()` (`renaming.hh:123`). `Renaming` (`renaming.hh:40`) stores sort/label/op(multimap)/strat/class/attr maps and computes a module-specific canonical form. Instantiation (`instantiateModuleWithFreeParameters.cc:34`) builds a canonical `Renaming` + `ParameterMap` in three phases — `handleInstantiationByTheoryView/ByParameter/ByModuleView` — then `handleParameterizedSorts/Constants`, `handleRegularImports`, `finishCopy`; it distinguishes **free vs bound** parameters and supports nested `instantiateBoundParameters`. A theory used as parameter `X` is turned into a parameter copy `X :: T` with sorts `X$Elt` via `Token::makeParameterInstanceName` (`parameterization.cc:27-113`). `View` (`view.hh:35`) is *also* six-way multiply-inherited (incl. `Renaming`, `Argument`, `EnclosingObject`) with `fromTheory/toModule`, `opTermMap`, `stratExprMap`, and an `INITIAL/PROCESSING/GOOD/BAD/STALE` status with `evaluate()` running `checkSorts/checkOps/checkStrats` (`view.cc:355,557`). `ViewDatabase`/`ViewCache`/`ParameterDatabase` mirror the module side.

`Interpreter` (`interpreter.hh:40`) is a single global object (`global.cc:83`) that multiply-inherits Environment + all the databases/caches + `PrintSettings`. State: a `flags` bitset (`:65-139`), `currentModule/currentView`, continuation state for `continue` (`savedState/savedModule/continueFunc`), and `selected/traceIds/breakIds/excludedModules` sets. Commands resolve via `setCurrentModule()` (`interpreter.cc:211` — note: command-line module *expressions* are not supported, only a named module) then `currentModule->getFlatModule()`.

**Dispatch pattern:** `virtual` Module lifecycle hooks; pervasive **multiple inheritance**; `dynamic_cast` for control flow (`Argument`→`View`/`Parameter`, `ConditionFragment` subtypes, `ModuleExpression` by `getType()`); and a raw-pointer **dependency graph** via `Entity`/`Entity::User::regretToInform` (`entity.hh:31`) that cascades `deepSelfDestruct()` and uses a manual `protectCount` to defer freeing modules still in use (`importModule.cc:316-377`).

### 3. Rust migration
- **ModuleExpression/ViewExpression AST — PORT.** Plain `enum` + `Box`; `dynamic_cast`/`getType()` becomes `match`. Trivial win.
- **Module databases — PORT.** `HashMap<Symbol, …>` (interned ids). Drop the `Interpreter` god-object multiple inheritance into composed fields (`struct Interpreter { modules, views, params, caches, settings, current_module, … }`).
- **Caches + canonical naming — ADAPT.** Keep content-addressed caching but key on a structured `CanonicalKey` (hashable enum) rather than a reconstructed Rope string; back with `HashMap`. Rationale: avoids string round-trips and ambiguity.
- **Entity::User dependency graph + protectCount — RETHINK.** This raw back-pointer/manual-refcount/`regretToInform` machinery does **not** translate. Replace with `Rc`/`Arc` ownership of cached modules + an explicit dependency/dirty-set invalidation (or generational ids + a validity epoch). The "defer deletion while in use" need disappears once lifetimes are reference-counted.
- **ImportModule flattening ("donation") — RETHINK.** The in-place mutation that copies raw `Term*` trees between modules via `ImportTranslation` is the riskiest piece. Model flattening as a pure function `flatten(pre_module, &cache) -> FlatModule` producing fresh owned `Term`s (arena/`id`-indexed), with provenance recorded as explicit ranges/enums instead of `nrImported*` counters. `ImportTranslation` becomes a `SymbolMap` trait object or an enum of remappings; op→term mapping (the "return null symbol" hack) becomes an explicit `enum OpImage { Symbol(..), Term(..) }`.
- **Renaming/View — ADAPT.** Keep the map-of-maps but as typed structs; replace `View`'s six-base inheritance + `Renaming` subclassing with composition (`struct View { renaming: Renaming, from, to, op_term_map, … }`) and a `Status` enum. Bubble parsing in `SyntacticView` stays behind A4's parser.
- **process() pipeline — PORT** as an explicit state machine returning `Result`, replacing `markAsBad()`/bad-flag plumbing with `Result`/error accumulation.
- **Interpreter/REPL — ADAPT.** Command set as an `enum Command` dispatched in a loop; continuations (`continue`) as an explicit saved-state struct; control-C via a signal flag/`AtomicBool`. Concrete crates: `rustyline` (REPL), `id-arena`/`slotmap` (modules & terms), `indexmap` for ordered maps.

**Does NOT translate:** multiple inheritance (Interpreter, ImportModule, View), the `Entity::User`/`regretToInform`/`protectCount` manual GC of cached modules, `dynamic_cast`-driven dispatch, in-place donation with shared raw `Term*`, and Rope-string cache keys.

### 4. Hardest parts / risks / open questions
- **Cache coherence:** the current design rebuilds derived modules on any dependency change. Choosing `Rc`+dirty-propagation vs. immutable-rebuild-everything is the central architectural call; over-eager invalidation kills incremental performance.
- **Parameterization corner cases:** bound vs free parameters, theory-views vs module-views vs parameters-from-enclosing-object, parameterized sorts `X$Elt`/pconst, parameterized views, and nested `instantiateBoundParameters` are deeply entangled (`instantiateModule*WithBoundParameters.cc`, `parameterization.cc`). Achieving parity here is the bulk of the work and needs a thorough conformance test suite from `prelude.maude`.
- **Provenance tracking** (what may be renamed/mapped) is currently index-range arithmetic; a wrong boundary silently corrupts views. Needs explicit tagging.
- **Term ownership across modules:** donation shares structure; Rust forces a decision (deep-copy vs interned/shared-arena) that interacts with A1's term representation. [INFERRED] coordinate the FlatModule term arena with A1.
- **OO modules** (`ooTransform`/`ooSorts`) inject sorts/ops mid-pipeline; keep as a pre-pass producing ordinary declarations.

### 5. Proposed Rust module layout
```
crate maud-modules/
  ast.rs            // ModuleExpression, ViewExpression
  database.rs       // ModuleDatabase, ViewDatabase, ParameterDatabase
  flat.rs           // FlatModule (engine signature+statements), Status pipeline
  flatten.rs        // import/donation as pure functions, provenance tags
  importing.rs      // ImportMode, Origin, import DAG traversal
  translation.rs    // SymbolMap/ImportTranslation, OpImage enum
  renaming.rs       // Renaming + canonical form / cache key
  parameter.rs      // Parameter, parameter copies (X::T, X$Elt), pconst
  view.rs           // View, SyntacticView, evaluate()/checks
  instantiate.rs    // free/bound instantiation phases
  cache.rs          // content-addressed module/view caches + invalidation
crate maudue-repl/
  interpreter.rs    // Interpreter state (composed), flags, current module/view
  command.rs        // Command enum + dispatch, continuations
  show.rs / set.rs  // show/set option handlers
```
