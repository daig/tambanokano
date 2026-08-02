# Strict Rust reducers — Stage 1 design and acceptance record

**Status:** Implemented on 2026-08-02; retained as the selected design and acceptance record
**Feature record:** [TNK-DEV-017](issues/TNK-DEV-017-typed-rust-reducers.md)
**Current language contract:** [`docs/manual.md` §3.2, §16.1.1, and Appendix G.3](../manual.md#1611-strict-rust-reducers)

## 1. Review objective

This document specifies the first supported path for a TNK operator to invoke host-provided Rust computation during equational reduction. It is intentionally narrower than general host-defined specials:

> A strict Rust reducer is a pure, deterministic equational function invoked once after TNK has normalized every argument under the standard eager strategy.

The design was reviewed for reduction soundness, API lifetime safety, cache validity, sort/theory coherence, crate boundaries, and compatibility with a later strategy-aware control-extension protocol. Sections written in future tense record the constraints against which the shipped Stage 1 implementation was accepted; the current user contract is the linked Reference.

The companion TNK-DEV-017 issue records the broader intent and unresolved general-control questions. Stage 1 implements the concrete choices in this record. A future strategy-aware control extension remains a distinct, unselected feature.

## 2. Decision summary

Stage 1 uses the following selected design:

1. Source declarations bind through `special (id-hook HostFunctionSymbol (KEY) ...)`.
2. `KEY` names a capability in an immutable, host-owned `HostFunctionCatalog`; it is not a Rust path or dynamic-library symbol.
3. Registration completes before module construction. Missing and duplicate capabilities are explicit errors.
4. Built signatures store dense binding IDs, not closures or mutable host state, in `SpecialOp::HostFunction`.
5. Stage 1 accepts only fixed-arity, free-theory root operators using the normalized standard left-to-right eager strategy.
6. TNK invokes Rust once at the final top attempt after reducing every direct argument.
7. Rust receives scoped `NormalDag` argument wrappers, a scoped `RedexDag`, resolved hooks, and a narrow `StrictReduceCtx`; it never receives `&mut Engine`.
8. `NormalDag` proves current-epoch reduction state only. It does not prove groundness, recursively eager descendants, or native decodability.
9. Native value decoding is explicit and fallible. Typed adapters sit above the lower-level strict reducer protocol.
10. Rust returns `Decline` or a same-context `BuiltDag`; reducer faults remain distinct from domain decline.
11. TNK checks result sort compatibility, counts and traces one outer host-function step, and normalizes the returned term itself.
12. The catalog and module bindings are immutable for an engine's lifetime. Changing capabilities rebuilds affected engines rather than mutating live bindings.
13. Stateful, nondeterministic, asynchronous, I/O, lazy, and staged control behavior is outside this contract.
14. Names, IDs, wrapper foundations, and dispatch remain role-specific so a later `HostControlSymbol`/`HostControlBindingId` protocol can be added without changing `StrictReducer`.

## 3. Non-goals

Stage 1 does not provide:

- arbitrary callbacks with `&mut Engine` access;
- host-defined evaluation strategies or short-circuit control;
- callbacks over partially reduced direct arguments;
- stateful counters, randomness, clocks, filesystem access, network access, or other observable effects;
- asynchronous execution or cancellation;
- live function replacement;
- a process-global registry;
- a C ABI, dynamic library loader, plugin manifest, sandbox, or panic-isolation boundary;
- source-preserving quotation;
- automatic conversion of every TNK sort into a Rust type;
- a replacement for existing bespoke `SpecialOp` variants.

Existing `Branch`, `Counter`, SMT, META descent, stream managers, and interpreter managers retain their current semantic roles. They must not be forced through this strict interface for architectural uniformity.

## 4. Current reduction insertion point

Today a symbol owns an optional `SpecialOp`. At a `Top` evaluation instruction, `Runtime::try_rewrite_top`:

1. checks the symbol's special;
2. calls `Runtime::try_special`;
3. uses a successful result before considering user equations;
4. falls through to ordinary equations when the special declines;
5. counts a successful result in the outer normalization loop;
6. restarts evaluation from the result's own strategy;
7. stamps only the eventual normal form with the current equation epoch.

The strict host dispatch belongs in this existing path:

```rust
SpecialOp::HostFunction(binding) => {
    self.reduce_host_function(sig, redex, binding)
}
```

It must not add a second reduction loop or bypass existing tracing, rewrite accounting, memberships, normal-form forwarding, or result normalization.

## 5. Source attachment

### 5.1 Proposed spelling

Illustrative declaration:

```maude
op sha256 : String -> String
  [special (
    id-hook HostFunctionSymbol (crypto.sha256)
    op-hook stringSymbol (<Strings> : ~> String)
  )] .
```

`HostFunctionSymbol` is the strict/eager contract. `crypto.sha256` is a stable registry key. The shipped grammar is exactly one token matching `^[a-z](?:[a-z0-9-]*[a-z0-9])?(?:\.[a-z](?:[a-z0-9-]*[a-z0-9])?)+$`: every segment begins lowercase, contains only lowercase ASCII letters, digits, and interior hyphens, never ends in a hyphen, and at least one dot separates segments.

Supporting `op-hook` and `term-hook` references retain their current meaning:

- they resolve to module-relative `SymbolId`s during signature construction;
- renaming updates those referenced TNK symbols structurally;
- the host-function key does not change under module renaming;
- the callback sees a `ScopedHostHooks<'ctx>` view whose lookups return opaque
  `HostSymbol<'ctx>` construction capabilities, never raw supporting-hook IDs or source tokens.

### 5.2 Build behavior

Module construction must reject atomically:

- a missing key;
- a duplicate or malformed key in the catalog;
- a missing required hook purpose;
- a hook with the wrong operator profile;
- a non-free attached root theory;
- a nonstandard evaluation strategy;
- an unsupported declaration/overload profile;
- inconsistent host-function keys among declarations merged into one symbol.

A missing host capability is not an inert ordinary operator and is not a runtime decline. This deliberately improves on the current silent behavior for unknown ordinary id-hook classes.

### 5.3 Future namespace

Reserve a separate source class:

```maude
id-hook HostControlSymbol (...)
```

Stage 1 does not parse this class as a strict function, alias it to `HostFunctionSymbol`, or consult the strict catalog for it. `HostControlSymbol` is reserved and Unsupported: it installs no control or strict binding and leaves the operator ordinary/inert even when its data token equals a registered `HostFunctionKey`. A generic runtime-selected `HostSymbol` remains prohibited.

## 6. Catalog ownership and lifecycle

### 6.1 Public construction

Proposed host path:

```rust
let functions = HostFunctionCatalog::builder()
    .register("crypto.sha256", Sha256Reducer, sha256_descriptor())?
    .register("text.case-fold", CaseFoldReducer, case_fold_descriptor())?
    .build();

let mut session = Session::builder()
    .host_functions(functions)
    .build();
```

`Session::new()` remains equivalent to a builder with an empty catalog.

A lower-level syntax-free/module-builder path must accept the same immutable catalog. There must be one semantic implementation, not separate Session and `Engine` callback mechanisms.

### 6.2 Immutability

`HostFunctionCatalog::build()` freezes:

- key-to-ID assignments;
- descriptors;
- reducer implementations;
- immutable reducer configuration.

A built Session or Engine cannot register, unregister, or replace functions. To change capabilities, the host creates a new catalog and rebuilds affected modules/engines. No DAG or normal-form cache crosses that rebuild boundary.

This policy avoids requiring callback code identity to participate in the current node reduction stamp. If live replacement is added later, it must first introduce a normalization-semantic epoch that includes reducer bindings.

### 6.3 Concurrency posture

The catalog should be `Arc`-backed and reducers should implement:

```rust
StrictReducer: Send + Sync + 'static
```

Current engine state may remain thread-confined. Requiring immutable thread-safe reducer objects avoids baking non-transferable captured state into the API before the separately planned concurrent Session work.

`&self` does not prove semantic purity because interior mutability remains possible. Purity and deterministic decline/result behavior are trusted extension obligations. Internal memoization is permitted only when it cannot change semantic outputs.

## 7. Catalog IDs and module bindings

Use two dense identity domains:

```rust
pub struct HostFunctionId(u32); // one immutable catalog
pub struct HostBindingId(u32);  // one built signature
```

### 7.1 Catalog entry

```rust
struct HostFunctionEntry {
    key: HostFunctionKey,
    descriptor: StrictReducerDescriptor,
    reducer: Arc<dyn StrictReducer>,
}
```

### 7.2 Signature binding

```rust
struct ResolvedHostBinding {
    function: HostFunctionId,
    hooks: ResolvedHostHooks,
    declaration_contract: BoundDeclarationContract,
}
```

The signature owns a dense table of `ResolvedHostBinding`s. The symbol stores only:

```rust
SpecialOp::HostFunction(HostBindingId)
```

The reducer implementation remains in the shared immutable catalog. Module-relative symbols remain in the signature binding. This prevents engine-relative IDs from leaking into a globally shared reducer object.

## 8. Descriptor and Stage 1 admission rules

A descriptor is immutable registration metadata:

```rust
pub struct StrictReducerDescriptor {
    pub arity: usize,
    pub required_op_hooks: &'static [OpHookRequirement],
    pub required_term_hooks: &'static [TermHookRequirement],
}
```

Stage 1's theory and strategy are fixed by the attachment class, not configurable descriptor flags:

- root theory: `Free` only;
- arity: exact declared fixed arity;
- strategy: standard eager only;
- invocation: one final top attempt.

Keeping those properties fixed avoids a descriptor accidentally opting into control semantics.

### 8.1 Why free roots only

Associative root nodes can flatten a binary declaration into an arbitrary physical arity, and CUI/identity/idempotence roots can collapse during construction. Stage 1 does not need that complexity. A strict function can consume a canonical associative collection as one ordinary argument:

```maude
op nativeBagHash : Bag -> Hash .
```

A later strict, still-eager extension may add an explicitly reviewed `CanonicalVariadicReducer` contract. That addition is independent from strategy-aware control.

### 8.2 Overloads

When overload declarations share one runtime symbol:

- every contributing declaration must resolve to the same host-function key and compatible hook binding;
- the descriptor arity must match the shared declared arity;
- the runtime call carries the actual argument sorts and selected structural result range;
- returned sort validation uses that selected range;
- incompatible declarations reject the module rather than using declaration-order last-wins behavior.

## 9. Eager strategy validation

The only accepted normalized schedule is:

```text
Argument(0), Argument(1), ..., Argument(n-1), Top(final)
```

In the current signature representation this is `strategy == None`. An explicitly written equivalent source strategy is normalized to the same representation and may be accepted.

Reject every schedule containing:

- a top attempt before all arguments;
- more than one top attempt;
- an omitted argument;
- a repeated/incremental attempt;
- a lazy or semi-eager associative classification;
- a nonstandard permutation, for Stage 1.

The first release intentionally rejects even an all-argument permutation such as `strat (2 1 0)`. It offers little value to a pure function and makes divergence order part of the extension contract. Supporting eager permutations later would be additive if a concrete compatibility requirement appears.

## 10. Evaluation-state types

### 10.1 Shared private foundation

Use one private provenance-bearing base:

```rust
struct ScopedDag<'ctx> {
    id: DagId,
    _scope: PhantomData<&'ctx ReductionScope>,
}
```

Public state wrappers have private fields:

```rust
pub struct NormalDag<'ctx>(ScopedDag<'ctx>);
pub struct RedexDag<'ctx>(ScopedDag<'ctx>);
pub struct BuiltDag<'ctx>(ScopedDag<'ctx>);
```

The exact implementation may use another lifetime token, but callers must be unable to construct wrappers from arbitrary IDs or detach an ID from its engine/reduction scope.

### 10.2 `NormalDag`

`NormalDag` proves that TNK reduction returned this direct argument at the current normalization epoch. Creation follows current valid normal-form forwarding before wrapping the result.

It does not prove:

- groundness;
- a particular constructor family;
- native decodability;
- absence of variables;
- recursively strict descendants;
- source-level canonical spelling.

An inner lazy operator can be a normal form under its own strategy while retaining suspended descendants. Consequently, structural child traversal from `NormalDag` returns a weaker read-only `DagRef`/`DagView`, not `NormalDag` automatically.

### 10.3 `RedexDag`

`RedexDag` proves:

- same-engine provenance;
- structurally canonical root construction;
- an attached validated strict host binding;
- normal direct arguments.

It does not claim that the root application is normal; the host function and equations have not yet been tried.

### 10.4 `BuiltDag`

`BuiltDag` proves:

- same callback/engine provenance;
- construction through TNK's theory-aware node builders or safe reuse of an input;
- no forged sort, reduction stamp, or normal-form forwarding metadata.

It does not claim equational normality. TNK consumes it immediately after the callback and restarts ordinary normalization.

### 10.5 Reserved future state

The private foundation must permit a later sibling:

```rust
pub struct SuspendedDag<'ctx>(ScopedDag<'ctx>);
```

Stage 1 does not expose or construct it for strict reducers.

## 11. Callback API

The semantic shape is:

```rust
pub trait StrictReducer: Send + Sync + 'static {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault>;
}

pub struct StrictCall<'ctx> {
    redex: RedexDag<'ctx>,
    arguments: Vec<NormalDag<'ctx>>,
    argument_sorts: Vec<SortId>,
    result_range: SortId,
    hooks: ScopedHostHooks<'ctx>,
}

pub enum StrictOutcome<'ctx> {
    Decline,
    Reduced(BuiltDag<'ctx>),
}
```

The fields above record the owned semantic contents; the shipped fields remain private and the accessor signatures in `tnk_core::host` are authoritative. These semantic properties are binding:

- immutable reducer receiver;
- one callback per final strict top attempt;
- proof-bearing direct arguments;
- separate redex state;
- callback-scoped, immutable supporting-hook capabilities;
- distinct decline, result, and fault outcomes;
- scoped result provenance.

`StrictCall` uses accessors to preserve representation and scope invariants. `argument(position)` panics when `position` is outside the descriptor-validated argument range. `hooks()` returns a copyable `ScopedHostHooks<'ctx>`; `op_symbol(purpose)` and `term_symbol(purpose)` return invariant-lifetime `HostSymbol<'ctx>` capabilities and panic for a purpose absent from the successfully bound descriptor.

## 12. Strict context surface

`StrictReduceCtx` exposes read-only inspection and safe construction only.

Representative inspection:

```rust
impl<'ctx> StrictReduceCtx<'ctx> {
    pub fn top(&self, dag: DagRef<'ctx>) -> SymbolId;
    pub fn sort(&self, dag: DagRef<'ctx>) -> SortId;
    pub fn repr<'a>(&'a self, dag: DagRef<'ctx>) -> DagView<'a, 'ctx>;
    pub fn children<'a>(&'a self, dag: DagRef<'ctx>) -> ChildView<'a, 'ctx>;
    pub fn is_ground(&self, dag: NormalDag<'ctx>) -> bool;
}
```

Representative construction:

```rust
impl<'ctx> StrictReduceCtx<'ctx> {
    pub fn constant(
        &mut self,
        symbol: HostSymbol<'ctx>,
    ) -> Result<BuiltDag<'ctx>, BuildError>;
    pub fn app(
        &mut self,
        symbol: HostSymbol<'ctx>,
        args: &[DagRef<'ctx>],
    ) -> Result<BuiltDag<'ctx>, BuildError>;
    pub fn make_string(
        &mut self,
        symbol: HostSymbol<'ctx>,
        bytes: &[u8],
    ) -> Result<BuiltDag<'ctx>, BuildError>;
    pub fn reuse(&self, dag: NormalDag<'ctx>) -> BuiltDag<'ctx>;
}
```

`app` dispatches through the active Signature's theory-aware rebuild rather than a free-only constructor. A declaration-arity application therefore receives the canonical free, ACU, AU, or CUI representation, including applicable associative flattening, commutative ordering, multiplicity/idempotence handling, and identity removal or collapse.

The final API should add scalar builders only as required by supported codecs. It must not expose:

- `&mut Engine` or mutable `Signature`;
- `reduce`, rewriting, search, or recursive host dispatch;
- arbitrary collection;
- mutation of counters, traces, roots, or reduction stamps;
- raw `DagNode` mutation;
- cross-engine materialization;
- a stable unscoped `DagId` escape hatch.

Reducers may allocate through context builders. GC must not run at an unsafe callback point; the redex, arguments, resolved hook references, and newly built result remain discoverable until the callback returns.

Stage 1 callbacks cannot retain DAGs between calls. A later API may add explicit rooting/revalidation, but it is unnecessary for pure strict functions and would permit hidden state too early.

## 13. Native value decoding and typed adapters

Normality and native value shape remain separate. Provide explicit fallible decoders:

```rust
impl StrictReduceCtx<'_> {
    pub fn decode_string<'a>(&'a self, dag: NormalDag<'a>) -> Option<&'a [u8]>;
    pub fn decode_qid<'a>(&'a self, dag: NormalDag<'a>) -> Option<&'a str>;
    pub fn decode_float(&self, dag: NormalDag<'_>) -> Option<f64>;
    pub fn decode_integer<'a>(&'a self, dag: NormalDag<'a>) -> Option<IntegerRef<'a>>;
}
```

Decoder failure is an ordinary domain mismatch and normally produces `Decline`. It never requests more argument evaluation.

Decoders should borrow existing scalar storage and avoid copies. Integer/rational adapters should avoid exposing backend-specific types when TNK already has an abstraction. Encoding necessarily allocates when constructing a new result.

### 13.1 Ergonomic typed registration

Build typed helpers over `StrictReducer`, not a second dispatch path:

```rust
catalog.register_typed1(
    "crypto.sha256",
    codecs::string(),
    codecs::string(),
    |bytes: &[u8]| sha256(bytes),
)?;
```

A typed adapter owns the descriptor/hook schema and implements:

1. borrow each requested decoded byte-string payload directly as `&[u8]`, without cloning the backing bytes or allocating an input buffer;
2. return `Decline` on a documented representation mismatch, invoking no callback unless every argument decoded successfully;
3. invoke the Rust function synchronously with those borrowed inputs;
4. receive an owned `Vec<u8>` result and encode a new TNK string through the descriptor-required, resolved `stringSymbol`;
5. return the resulting `BuiltDag`.

The lower-level trait remains available for trusted reducers that legitimately inspect or construct symbolic normal forms.

## 14. Outcome and error semantics

### 14.1 Domain decline

```rust
Ok(StrictOutcome::Decline)
```

means the reducer is intentionally undefined for this canonical argument combination. TNK proceeds to ordinary equations and then `[owise]` according to the existing top-rewrite order.

Examples:

- a concrete-only reducer receives a symbolic normal form;
- a normal term of the declared sort does not use the registered native representation;
- a partial mathematical function receives an out-of-domain value.

### 14.2 Reducer fault

```rust
Err(ReducerFault)
```

means the implementation cannot uphold its registered execution contract. It aborts the current semantic operation and never falls through to equations.

Examples:

- impossible required-hook absence after successful binding;
- rejected safe construction;
- explicit implementation-level failure that is not part of the function's declared domain.

The kernel currently exposes infallible reduction APIs. Implementation review must choose one migration path before coding:

1. introduce fallible internal reduction and public `try_*` operations, retaining existing infallible methods as programmer-oriented panic wrappers; or
2. initially make registered reducers infallible beyond `Decline`/`Reduced`, treating all contract violations as programmer errors.

**Recommendation:** choose the first path if its propagation through rewrite/search/session operations is bounded and can remain complete. Never map faults to `Decline`. A half-propagated fault path is worse than an explicit trusted-code panic boundary.

### 14.3 Panic

A panic is a host programming bug. Stage 1 does not catch or translate callback panics and promises no `catch_unwind`, process survival, TNK-owned semantic rollback, callback-side-effect rollback, or sandboxing; the embedding's Rust panic policy governs unwind or abort. This is distinct from a returned `ReducerFault`, whose owning fallible operation restores the documented semantic checkpoint. Callback execution is synchronous and has no cancellation token, timeout, async yield, or preemption point. A reducer can diverge, block, or exhaust CPU/memory, so reducer authors own termination/resource bounds and hosts must use outer process isolation when interruption or untrusted execution is required.

## 15. Result validation and normalization

After `Reduced(result)`, TNK must:

1. recover the engine-local ID from `BuiltDag` inside the same scope;
2. verify the result kind equals the selected declaration range kind;
3. require the result sort to be below or equal to the selected result range;
4. reject an error-sort result unless an explicitly reviewed policy permits it;
5. record the host key/binding in the built-in trace identity;
6. return the result to the existing outer normalization loop;
7. let that loop count exactly one successful outer rewrite;
8. begin the result symbol's evaluation strategy from step zero;
9. stamp only the eventual normal form.

A same-context wrapper prevents cross-engine IDs but does not prove result sort compatibility; the dispatcher performs that check.

Returning an unchanged or freshly rebuilt equivalent redex can diverge. This is the same progress obligation as a self-reproducing equation and remains a reducer/module correctness responsibility.

## 16. Cache and signature validity

A strict reducer's output and decline decision must be stable for:

```text
(canonical redex, built signature, immutable catalog binding)
```

The catalog cannot change in place. Module redefinition or capability changes rebuild the engine.

Low-level APIs currently allow `set_special` and `set_strategy` mutation. Host-function attachment must be constrained to the pre-reduction signature-build phase. Focused implementation review should decide whether to:

- add an explicit signature sealing state; or
- retain documented mutation ordering preconditions and ensure the frontend/Session path cannot violate them.

An eventual mutable semantic API should replace equation-only cache terminology with a normalization-semantic epoch advanced by every mutation that can change normal forms. Stage 1 must not implement live catalog mutation without that work.

## 17. Purity and coherence obligations

The Rust type system cannot prove all required semantics. A registered reducer is trusted to satisfy:

- deterministic, referentially transparent result and decline behavior for the canonical redex, immutable signature, and binding;
- no externally visible side effects;
- no dependence on time, I/O, randomness, nondeterministic services, or mutable result-affecting host state;
- invariance under the declared argument representations and structural theories;
- sort-correct results;
- compatibility with any overlapping user equations;
- acceptable termination, progress, CPU, and memory behavior under a synchronous non-cancellable call.

Operational precedence is unchanged:

```text
successful host function
  before ordinary equations
  before owise equations
```

If a host function and equation overlap, TNK guarantees order, not confluence. The module/library author owns semantic agreement.

## 18. Trace and accounting

A successful strict host reduction is one host-function rewrite:

- callback code does not increment the outer counter;
- `Decline` counts zero;
- a fault counts no successful host rewrite;
- normalizing the returned term contributes its ordinary subsequent counts;
- structured identity is `TraceEvent::Rewrite { kind: RewriteKind::HostFunction, host_key: Some(canonical_key), ... }`, while every other `TraceEvent::Rewrite` has `host_key: None`;
- rendered trace output includes the canonical key; a catalog/signature-relative dense ID is never the sole user-facing identity, and renaming changes only rendered TNK terms;
- exact aggregate totals remain subject to the existing diagnostic-count contract.

Stage 1 reducers cannot report arbitrary nested rewrite counts because they cannot re-enter semantic operations.

## 19. Crate boundaries

### `tnk-core`

Owns:

- catalog interfaces and dense IDs;
- reducer descriptor and trait;
- scoped DAG/context/outcome types;
- module-relative resolved binding table representation;
- `SpecialOp::HostFunction`;
- final-top dispatch, result validation, tracing, counting, and normalization integration.

It must not name `Session`, frontend AST types, or module databases.

### `tnk-frontend`

Owns:

- recognition of `HostFunctionSymbol` in `SpecialSpec`;
- key extraction;
- strategy/theory/arity/overload validation during signature build;
- resolution and validation of declared op/term hooks;
- creation of `ResolvedHostBinding` entries;
- explicit build diagnostics.

It receives the immutable catalog/capability view through its build inputs.

### `tnk-modules`

Owns preservation of host attachments and hook references through flattening, import, renaming, instantiation, and dependent rebuild. Capability keys remain unchanged while referenced TNK symbols follow existing structural transformations.

### `tnk-session`

Owns:

- `SessionBuilder` host catalog injection;
- catalog lifetime for all built modules;
- atomic reporting of missing/invalid capabilities;
- rebuilding dependent modules against the same immutable catalog;
- rendering propagated reducer faults if the fallible path is selected.

### `tnk-repl`

Adds no reducer semantics. It uses the default empty catalog unless an embedding executable explicitly constructs a configured Session.

## 20. Future strategy-aware compatibility

Stage 1 must leave room for this separate conceptual extension:

```rust
SpecialOp::HostControl(HostControlBindingId)

ArgumentState::Normal(NormalDag)
ArgumentState::Suspended(SuspendedDag)

ControlDecision::Reduced(BuiltDag)
ControlDecision::DemandArgument(usize)
ControlDecision::DeclineFinal
```

No Stage 1 public name should imply that strict reducers cover all host-defined specials. In particular:

- keep `HostFunctionSymbol` role-specific;
- keep `HostFunctionCatalog` capable of becoming one field of a broader immutable `HostCapabilities` container;
- use `HostBindingId`, not a universal callback ID;
- keep `ScopedDag` private and state wrappers distinct;
- do not expose raw `DagId` callbacks;
- do not add suspended-state variants to `StrictCall`;
- do not reuse `StrictOutcome` for evaluator demand/deferral;
- validate strategy class at module binding, before runtime dispatch;
- do not teach strict reducers about early versus final top attempts.

A future control protocol may share safe DAG inspection/construction internals while retaining different scheduling, invocation, cache, and decline semantics.

## 21. Implementation sequence

Implementation should proceed in dependency order, with each step retaining a compilable workspace:

1. Add `tnk-core` catalog, key/ID, descriptor, and immutable builder types with no reducer dispatch.
2. Add scoped DAG wrappers and a construction/inspection context exercised by core-only tests.
3. Add `SpecialOp::HostFunction`, signature binding storage, and final-top strict dispatch for programmatic Engine construction.
4. Add frontend recognition and atomic binding validation for `HostFunctionSymbol`.
5. Thread the immutable catalog through lower-level build inputs and module rebuild paths.
6. Add `SessionBuilder`, preserving `Session::new()` as the empty-catalog default.
7. Add native scalar decoders/builders and typed registration adapters required by the first real reducer fixture.
8. Complete reducer-fault propagation or explicitly select/document the trusted panic boundary before exposing the public API.
9. Add tracing, diagnostics, API documentation, manual hook catalogue, feature matrix, and Rust API map updates.
10. Run end-to-end configured Session scenarios, then cleanup and close the Stage 1 gate in TNK-DEV-017.

Do not begin future `HostControlSymbol` implementation as part of Stage 1.

## 22. Required verification

### 22.1 Catalog and build

- duplicate registration is rejected;
- missing registration rejects the module atomically;
- malformed key and hook schema are diagnosed;
- the default empty Session cannot load a module requiring a host function;
- imports, renaming, instantiation, and dependent rebuild preserve the key and correctly transform hook references;
- inconsistent overload bindings are rejected.

### 22.2 Strategy and theory

- standard implicit eager strategy is accepted;
- explicitly equivalent standard eager strategy is accepted after normalization;
- reordered, top-first, intermediate-top, omitted-argument, lazy, and semi-eager strategies are rejected;
- ACU, AU, CUI, and iter root attachments are rejected in Stage 1;
- a free host operator successfully consumes a canonical ACU value as one argument.

### 22.3 Evaluation states

- every direct callback argument is current-epoch normal;
- normal-form forwarding is followed before wrapping;
- symbolic normal arguments are delivered without being mislabeled concrete;
- a normal lazy inner term does not cause its suspended child to be exposed as `NormalDag`;
- wrappers cannot be constructed externally or retained beyond their scope through safe APIs.

### 22.4 Decoding and outcomes

- concrete native values decode without avoidable input copies;
- undecodable normal values produce `Decline` through typed adapters;
- `Decline` falls through to ordinary and `[owise]` equations in existing priority order;
- a successful reducer suppresses overlapping equations;
- a returned input is accepted when sort-correct;
- returned terms are normalized further by TNK.

### 22.5 Invariants and failures

- wrong-kind and out-of-range results are rejected as faults/contract violations, never declines;
- cross-engine and forged-result construction is impossible through the safe API;
- callback allocation remains GC-safe with in-reduction GC enabled;
- reducer faults take the selected abort path through reduce, rewrite, search, and Session;
- callback panic behavior matches the documented trusted-code boundary.

### 22.6 Cache, trace, and counts

- repeated reduction reuses the cached normal form without reinvoking the reducer;
- module/engine rebuild against a different immutable catalog cannot reuse the old DAG cache;
- successful host reduction counts exactly one outer rewrite;
- decline counts zero;
- trace output identifies the host binding and returned term;
- normalizing a returned term adds its ordinary subsequent counts.

## 23. Focused review questions

Review must resolve these questions before implementation begins:

1. Is `HostFunctionSymbol` the right durable source-level name, distinct enough from future control and external roles?
2. What exact token grammar and canonical display should `KEY` use?
3. Is free-theory, fixed-arity, standard left-to-right eager-only the correct initial admission boundary?
4. Should the low-level symbolic `StrictReducer` trait be public in Stage 1, or should only typed adapters be public initially?
5. Does the proposed `NormalDag` guarantee accurately describe normality under nested custom strategies?
6. Is callback-scoped, non-retainable DAG access sufficient for every selected initial use case?
7. Can `Result<StrictOutcome, ReducerFault>` be propagated completely through all semantic drivers in the Stage 1 change, or should Stage 1 select an explicit infallible trusted boundary?
8. Should signature sealing be implemented now, or is immutable catalog plus pre-reduction attachment discipline sufficient?
9. Are `Send + Sync` reducer requirements appropriate before Session concurrency exists?
10. Which one real reducer should serve as the end-to-end fixture and force the first codec/hook design without introducing an incidental external dependency?
11. Does storing module-relative binding data in the signature and implementations in the shared catalog preserve all rebuild and engine-isolation invariants?
12. Do the reserved names and wrapper foundations leave a genuinely additive path to `HostControlSymbol`, rather than merely postponing a breaking redesign?

## 24. Review acceptance gate

This design is ready for implementation only when focused review records:

- accept/revise decisions for all twelve review questions;
- one selected end-to-end reducer fixture;
- the error propagation policy;
- the signature/catalog immutability policy;
- the exact public versus crate-private API surface;
- confirmation that Stage 1 changes required by TNK-DEV-017 remain compatible with a distinct future strategy-aware control protocol.

Implementation completion remains governed by the broader gate in TNK-DEV-017 and by the user-facing Reference updates required when the capability ships.

## 25. Implementation completion and end-to-end acceptance

This section is the Stage 1 implementation gate. The examples are acceptance fixtures, not sketches:
the feature is incomplete until equivalent code compiles through the public embedding API and the
observable scenarios below pass without test-only dispatch paths.

### 25.1 Final codebase validation

A final pass over the current implementation found no architectural blocker:

- `Runtime::reduce` already separates the shared `Signature` from the mutable DAG arena, reaches one
  final `Top` under the standard strategy, forwards argument normal forms, counts a successful special
  in the outer loop, and restarts that loop on the returned term.
- `Signature::strat_action` represents the accepted standard schedule as `strategy == None`, so the
  Stage 1 admission check does not need to infer eagerness dynamically.
- the safe-point collector runs at reduction-loop heads, including nested identity normalization entered
  by callback construction. The implementation therefore keeps the callback redex, normal arguments,
  resolved hook targets, and every protected `BuiltDag` in explicit callback-scope roots until exit.
- `SpecialSpec` already retains id-, op-, and term-hook source data; module renaming already rewrites
  op- and term-hook references while leaving id-hook data unchanged; and reflected modules preserve the
  hook list. Host bindings can use those paths rather than adding a parallel attachment format.
- crate dependency direction is already suitable: `tnk-core` can own the callback protocol,
  `tnk-frontend` can bind it, `tnk-modules` can transform it, and `tnk-session` can supply the immutable
  catalog without introducing a dependency cycle.

The pass also identified required cross-cutting work. These are implementation obligations, not
blockers or permitted omissions:

1. Catalog input must be threaded through every real module-build entry point, including homed builds,
   view validation, reflected/meta builds, dependent rebuilds, and local child Sessions. None of those
   paths may silently substitute the empty catalog for a configured Session.
2. Parameter/view instantiation must transform special op-hook signatures and term-hook terms just as
   it transforms declarations, identities, and statement bubbles. The routing fixture below is the
   regression test for that seam.
3. Host identity must be added to structured and rendered built-in traces; the current
   `RewriteKind::BuiltIn` alone cannot identify a registered function.
4. Reducer faults require a deliberately fallible semantic path. The present kernel reduction,
   rewriting, search, descent, and Session paths are predominantly infallible and must be migrated
   completely rather than translating a fault into `Decline`.
5. Low-level host attachment must become a one-way validated build operation. The current general
   `set_special`, `set_strategy`, and overload mutators are not by themselves a safe live binding API.

For this gate, the following policies are fixed:

- A key is exactly one id-hook data token matching
  `^[a-z](?:[a-z0-9-]*[a-z0-9])?(?:\.[a-z](?:[a-z0-9-]*[a-z0-9])?)+$`. Registration and source parsing use the same validator and
  preserve the matching bytes as the canonical display. Uppercase, `_`, `/`, whitespace, empty
  segments, segment-final hyphens, leading/trailing punctuation, and multiple data tokens are errors.
- Stage 1 adopts the fallible policy from §14.2. Core exposes fallible `try_*` semantic operations;
  existing infallible convenience methods may remain only as documented panic wrappers. Session and
  all internal semantic drivers use the fallible path. A `ReducerFault` aborts the operation, never
  tries equations, never records a successful host rewrite, and is never retained as a resumable
  continuation.
- A catalog is installed when an Engine/Session build context is created and cannot be replaced.
  Host bindings may be created only before that Engine begins a semantic operation. Beginning the first
  reduction, rewrite, search, narrowing, or descent seals host binding. Once a symbol is bound,
  mutations of its declarations, strategy, theory, or special attachment are rejected. Changing a
  capability or binding rebuilds the Engine.
- `StrictReducer`, the catalog builder, descriptors, scoped read/build types, outcomes, faults, hook
  accessors, and the initially supported codecs are public embedding APIs. Dense IDs, binding tables,
  wrapper constructors, raw scoped IDs, and the `ScopedDag` foundation remain private or opaque.

If focused review changes one of these policies, it must update this section and its fixtures in the
same change; weakening or skipping the affected acceptance case is not an implementation.

### 25.2 Normative Rust fixtures

The initial fixture set uses only `std` and TNK crates. `text.normalize-tag` is the selected primary
typed fixture. `path.join` covers fixed arity greater than one. `routing.prefer-configured` exercises
the lower-level symbolic protocol, resolved hooks, safe construction, decline, and post-return
normalization.

The final API may make mechanical naming adjustments, but it must support this code without exposing
`DagId` or `&mut Engine`. Any naming adjustment must update the checked-in compiling fixture and this
block together.

```rust
use tnk_core::host::{
    codecs, HookSort, HostFunctionCatalog, HostFunctionRegistrationError, ReducerFault,
    StrictCall, StrictOutcome, StrictReduceCtx, StrictReducer, StrictReducerDescriptor,
};
use tnk_session::Session;

/// Convert an arbitrary byte tag to a stable lowercase ASCII slug.
///
/// Runs of non-ASCII-alphanumeric bytes become one `-`; leading and trailing runs disappear.
pub fn normalize_tag(input: &[u8]) -> Vec<u8> {
    let mut output = Vec::with_capacity(input.len());
    let mut separator_pending = false;

    for &byte in input {
        if byte.is_ascii_alphanumeric() {
            if separator_pending && !output.is_empty() {
                output.push(b'-');
            }
            output.push(byte.to_ascii_lowercase());
            separator_pending = false;
        } else {
            separator_pending = !output.is_empty();
        }
    }

    output
}

fn trim_edge_slashes(mut value: &[u8]) -> &[u8] {
    while value.first() == Some(&b'/') {
        value = &value[1..];
    }
    while value.last() == Some(&b'/') {
        value = &value[..value.len() - 1];
    }
    value
}

/// Join two relative byte paths with exactly one separator at their boundary.
pub fn join_path(left: &[u8], right: &[u8]) -> Vec<u8> {
    let left = trim_edge_slashes(left);
    let right = trim_edge_slashes(right);
    let needs_separator = !left.is_empty() && !right.is_empty();
    let mut output = Vec::with_capacity(left.len() + right.len() + usize::from(needs_separator));

    output.extend_from_slice(left);
    if needs_separator {
        output.push(b'/');
    }
    output.extend_from_slice(right);
    output
}

#[derive(Clone, Copy, Debug, Default)]
pub struct PreferConfigured;

impl StrictReducer for PreferConfigured {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        let first = call.argument(0);
        let second = call.argument(1);
        let first_is_ground = ctx.is_ground(first);

        // A symbolic but normal route uses the safe fallback. A concrete route is handled by Rust
        // only when it is the module-provided preferred constant; every other concrete route declines
        // to the module equations.
        let chosen = if !first_is_ground {
            second
        } else {
            let preferred = call.hooks().term_symbol("preferredTerm");
            if !preferred.matches(ctx.top(first.as_ref())) {
                return Ok(StrictOutcome::Decline);
            }
            first
        };

        let selected = call.hooks().op_symbol("selectedSymbol");
        let result = ctx.app(selected, &[chosen.as_ref()])?;
        Ok(StrictOutcome::Reduced(result))
    }
}

pub fn prefer_configured_descriptor() -> StrictReducerDescriptor {
    StrictReducerDescriptor::builder(2)
        .require_op_hook(
            "selectedSymbol",
            &[HookSort::Argument(0)],
            HookSort::Result,
        )
        .require_constant_term_hook("preferredTerm", HookSort::Argument(0))
        .build()
}

pub fn fixture_catalog(
) -> Result<HostFunctionCatalog, HostFunctionRegistrationError> {
    Ok(HostFunctionCatalog::builder()
        .register_typed1(
            "text.normalize-tag",
            codecs::string(),
            codecs::string(),
            normalize_tag,
        )?
        .register_typed2(
            "path.join",
            codecs::string(),
            codecs::string(),
            codecs::string(),
            join_path,
        )?
        .register(
            "routing.prefer-configured",
            PreferConfigured,
            prefer_configured_descriptor(),
        )?
        .build())
}

pub fn configured_session(
) -> Result<Session, HostFunctionRegistrationError> {
    Ok(Session::builder()
        .host_functions(fixture_catalog()?)
        .build())
}
```

The fixture-facing API above establishes these minimum semantics:

- `StrictCall::argument` returns a copyable, scoped `NormalDag` and bounds-checks or has an explicitly
  documented panic contract backed by the descriptor's exact arity.
- `as_ref` weakens a proof wrapper only to a scoped read-only `DagRef`; it never exposes a raw ID.
- required callback hook accessors return scoped `HostSymbol` construction capabilities without
  raw-ID exposure or per-call module lookup; they panic only when the callback requests a purpose
  absent from the successfully bound descriptor.
- `HookSort::Argument(i)` and `HookSort::Result` validate the supporting hook profile against the bound
  declaration. In this fixture, `selectedSymbol` is unary from argument 0's kind to the host call's
  selected result kind, and `preferredTerm` is a ground constant accepted at argument position 0.
- `BuildError` from `StrictReduceCtx::app` converts to `ReducerFault` for `?`; it cannot become
  `Decline`.
- `codecs::string()` requires and resolves the `stringSymbol` op-hook, borrows native input bytes, owns
  the encoded output, and declines before invoking the Rust function if any input is not a native
  string node.

### 25.3 Typed scalar and renaming fixture

The configured Session must load both modules. Renaming changes TNK operator and supporting-hook names
but not catalog keys.

```maude
fmod HOST-SCALARS is
  sort String .
  op <Strings> : -> String
    [ctor special (id-hook StringSymbol)] .
  op opaque : -> String [ctor] .

  op rawTag : -> String .
  op leftPart : -> String .
  op rightPart : -> String .
  eq rawTag = "  TNK / Reducers  " .
  eq leftPart = "api/" .
  eq rightPart = "/v1" .

  op normalizeTag : String -> String
    [special (
      id-hook HostFunctionSymbol (text.normalize-tag)
      op-hook stringSymbol (<Strings> : ~> String)
    )] .

  op joinPath : String String -> String
    [special (
      id-hook HostFunctionSymbol (path.join)
      op-hook stringSymbol (<Strings> : ~> String)
    )] .

  eq normalizeTag(opaque) = "opaque-fallback" [owise] .
endfm

fmod HOST-SCALARS-RENAMED is
  protecting HOST-SCALARS * (
    op <Strings> to <HostStrings>,
    op normalizeTag to slug,
    op joinPath to _join_
  ) .
endfm
```

### 25.4 Symbolic, parameter, view, and hook-transformation fixture

This fixture is intentionally generic before instantiation. It proves that a capability key remains
stable while a parameter constant term-hook, structured sorts in an op-hook, and the referenced result
operator are transformed through parameter copying, a view, instantiation, import flattening, and a
later renaming.

```maude
fth ROUTABLE is
  sort Elt .
  op preferred : -> Elt [pconst] .
endfth

fmod ROUTING{X :: ROUTABLE} is
  sort Decision{X} .
  op none : -> Decision{X} [ctor] .
  op hostLost : -> Decision{X} [ctor] .
  op selected : X$Elt -> Decision{X} [ctor] .

  op prefer : X$Elt X$Elt -> Decision{X}
    [special (
      id-hook HostFunctionSymbol (routing.prefer-configured)
      op-hook selectedSymbol (selected : X$Elt ~> Decision{X})
      term-hook preferredTerm (X$preferred)
    )] .

  vars A B : X$Elt .
  eq prefer(X$preferred, B) = hostLost .
  eq selected(X$preferred) = none .
  eq prefer(A, B) = none [owise] .
endfm

fmod COLORS is
  sort Color .
  ops red blue green : -> Color [ctor] .
endfm

view ColorView from ROUTABLE to COLORS is
  sort Elt to Color .
  op preferred to red .
endv

fmod COLOR-ROUTING is
  protecting ROUTING{ColorView} .
endfm

fmod COLOR-ROUTING-RENAMED is
  protecting COLOR-ROUTING * (
    op prefer to choose,
    op selected to picked
  ) .
endfm
```

### 25.5 Required observable end-to-end scenarios

Run these through `Session::builder().host_functions(fixture_catalog()?).build()`, the normal source parser/module database,
the selected module's command parser, and the ordinary semantic driver. Directly constructing
`SpecialOp::HostFunction`, injecting a `DagId`, or calling a reducer from a test is not an end-to-end
substitute.

1. **Typed unary success after argument normalization and renaming**

   ```maude
   reduce in HOST-SCALARS-RENAMED : slug(rawTag) .
   ```

   The result is `String: "tnk-reducers"` with exactly two equational rewrites. Structured trace order
   is the `rawTag` equation followed by one host event identified as `text.normalize-tag`. The trace
   shows the renamed `slug` redex; the host key remains unchanged.

2. **Typed binary success and strict left-to-right arguments**

   ```maude
   reduce in HOST-SCALARS-RENAMED : leftPart join rightPart .
   ```

   The result is `String: "api/v1"` with exactly three equational rewrites. Trace order is the
   `leftPart` equation, the `rightPart` equation, then one `path.join` host event. This is the
   end-to-end proof that every direct argument was normalized once, left-to-right, before the callback.

3. **Typed representation decline and equation fallback**

   ```maude
   reduce in HOST-SCALARS-RENAMED : slug(opaque) .
   ```

   `opaque` is a normal value of sort `String` but not a native string node. The adapter does not call
   `normalize_tag`, returns `Decline`, and the renamed `[owise]` equation produces
   `String: "opaque-fallback"`. The command reports exactly one rewrite and no successful host trace
   event.

4. **Low-level ground success, host precedence, and returned-term normalization**

   ```maude
   reduce in COLOR-ROUTING-RENAMED : choose(red, green) .
   ```

   The resolved `preferredTerm` is `red` and `selectedSymbol` is the renamed `picked`. Rust returns
   `picked(red)`; TNK then applies the renamed instance of `selected(X$preferred) = none`. The final
   result is `Decision{ColorView}: none` with exactly two rewrites: first a
   `routing.prefer-configured` host event, then the equation event. The overlapping
   `choose(red, green) = hostLost` equation does not run.

5. **Low-level symbolic normal input**

   ```maude
   reduce in COLOR-ROUTING-RENAMED : choose(X:Color, blue) .
   ```

   The callback receives `X:Color` as a `NormalDag`, observes that it is not ground, and safely builds
   `picked(blue)`. The result is `Decision{ColorView}: picked(blue)` with exactly one host rewrite and
   no equation fallback. This scenario must work with in-reduction GC enabled.

6. **Low-level domain decline**

   ```maude
   reduce in COLOR-ROUTING-RENAMED : choose(green, blue) .
   ```

   The first argument is ground but is not the resolved preferred constant. Rust returns `Decline`;
   the `[owise]` equation produces `Decision{ColorView}: none`. The command reports exactly one
   equation rewrite, zero successful host rewrites, and no host trace event.

7. **Dependent rebuild with the same immutable catalog**

   After the six commands pass, redefine `COLORS` with the same existing declarations plus
   `op yellow : -> Color [ctor] .`. The Session must rebuild the `ColorView` dependents,
   `COLOR-ROUTING`, and `COLOR-ROUTING-RENAMED` against the same catalog. Re-running scenarios 4–6
   produces the same results, counts, and stable host key. No binding or DAG from the replaced Engines
   is reused.

8. **Configured reflected and child execution**

   Reuse the same fixtures through a configured Session's META reduction path and through a local child
   interpreter created by that Session. Both builds resolve the same catalog entries and produce the
   same semantic results. An empty-catalog fallback, inert host operator, or missing-capability
   diagnostic in either nested path fails this gate.

### 25.6 Mandatory acceptance matrix

The scenarios above are necessary but not sufficient. All cases below are required automated checks.

#### Catalog, construction, and diagnostics

- The three Rust fixtures compile from an integration test using only public `tnk-core` and
  `tnk-session` APIs. The same catalog can be shared by multiple Engines, and compile-time assertions
  establish that its reducers are `Send + Sync + 'static`.
- Registration accepts the three canonical keys above. Duplicate registration, every invalid key class
  listed in §25.1, duplicate hook purposes, and an internally inconsistent descriptor return typed
  errors without producing a catalog.
- `Session::new()` and `Session::builder().build()` are equivalent empty-catalog paths. Loading
  `HOST-SCALARS` through either reports a missing `text.normalize-tag` capability and leaves the prior
  module database, current selection, continuations, and built Engines unchanged.
- A catalog containing only one of the two scalar functions rejects `HOST-SCALARS` atomically and names
  the missing key and operator. A catalog containing all three accepts both fixture families.
- The configured lower-level frontend/module build and syntax-free Engine path use the same core
  catalog and binding implementation as Session; neither has a callback-only shortcut.
- `HostControlSymbol` never resolves through the strict catalog, even when its data token matches a
  registered strict key.
- The stock REPL uses that same empty catalog and emits the missing-capability diagnostic; it never
  treats a host-attached operator as inert. An embedding executable must opt into a configured Session.

#### Attachment admission and transformation

- Binding validates exact key count, descriptor arity, every required hook purpose, hook
  constant/operator shape, hook sort profile, declaration result kind, fixed arity, free root theory,
  and standard normalized eager strategy before installing `SpecialOp::HostFunction`.
- Implicit standard strategy and an explicitly equivalent normalized strategy bind. Reordered,
  top-first, intermediate-top, repeated, omitted-argument, lazy, semi-eager, ACU, AU, CUI, and iter
  roots fail module construction with diagnostics that name the host operator and violated contract.
- A free zero-arity host operator also binds: it receives an empty argument view once at its sole final
  `Top`, and its result follows the same validation, counting, tracing, and normalization path. The
  binary fixture proves the greater-than-one arity path.
- Declarations merged into one runtime symbol bind only when key, descriptor, hook targets, arity, and
  structural result profiles are compatible. Declaration order cannot select a winner. A `ditto`
  declaration inherits and validates the same attachment. A compatible multi-overload test passes the
  actual argument sorts and the structurally selected result range to the callback, then validates the
  returned sort against that range rather than the first declaration.
- Plain imports and diamonds preserve one semantic binding. Renaming updates referenced TNK operators
  and sorts but not the key. The complete parameter/view/instantiation/rename fixture in §25.4 builds
  and resolves `preferredTerm` to `red` and `selectedSymbol` to `picked`.
- Up/down reflection preserves `HostFunctionSymbol`, the exact key token, hook purposes, hook
  signatures, and term-hook terms. Rebuilding a reflected module binds against the configured catalog,
  not a process-global or empty registry.
- Each dependent is fully rebuilt and validated before its Engine is replaced. A successful replacement
  invalidates its continuations and makes no old binding or normal-form cache executable. If a dependent
  cannot rebuild, its old Engine and continuations are removed or otherwise made unselectable before
  control returns; the Session never executes a stale dependent against changed source definitions.
- After host binding, an attempted catalog replacement, second binding, special replacement, strategy
  change, or overload-profile change is rejected. Attempting the first host bind after any semantic
  operation returns a sealed-build error.

#### Callback state, decoding, and construction

- A core callback-boundary test checks every `NormalDag` against the active equation epoch and follows
  `nf` forwarding before wrapping it. The callback is invoked exactly once and only at the final
  standard `Top`.
- A normal symbolic variable reaches `PreferConfigured` without being called concrete. A normal lazy
  inner application may be inspected as a `DagRef`, but its suspended child cannot be obtained as a
  `NormalDag`.
- The string adapter borrows the existing `Rc<[u8]>` payload as `&[u8]` without cloning the backing
  bytes or allocating an input buffer. Unary and binary adapters invoke the Rust function only after
  every input decode succeeds, then encode the owned `Vec<u8>` result as a new TNK byte string through
  the resolved, descriptor-required `stringSymbol`.
- Safe APIs can build constants, theory-aware free/ACU/AU/CUI applications, and native strings; can
  reuse a sort-correct input; and canonicalize associativity, commutativity, idempotence, and identities
  through the active Signature. Returned nodes carry no forged reduction epoch or normal-form
  forwarding metadata.
- Compile-fail or equivalent API tests prove that external code cannot construct proof wrappers,
  extract an unscoped `DagId`, retain a wrapper in a `'static` reducer, mix DAGs from Engines, invoke
  reduction recursively, mutate the Signature, or initiate collection through `StrictReduceCtx`.

#### Outcomes, faults, sorts, and precedence

- Scenarios 3 and 6 establish both typed and low-level decline. Additional tests distinguish fallthrough
  to an ordinary equation from fallthrough to `[owise]`; successful host reduction suppresses both.
- Returning a sort-correct input is accepted. Returning a newly built reducible term produces one host
  step and then ordinary normalization from the result symbol's strategy step zero.
- Dispatcher validation rejects a different result kind, a same-kind sort not below the selected range,
  and the kind's error sort as `ReducerFault`/contract violation before recording or counting a
  successful host rewrite. None can become `Decline`.
- A reducer that explicitly returns `ReducerFault` aborts direct reduction, a rewrite successor,
  search expansion, condition evaluation, narrowing/variant paths that normalize terms, META descent,
  local child interpretation, and Session command execution. Each public fallible operation returns
  the same fault identity/cause; Session renders one error and stores no continuation.
- For every reducer-fault path, the owner restores its pre-call TNK operation state,
  aggregate/breakdown counts, and trace append state, attempts no ordinary or `[owise]` fallback, and,
  when resumable, remains faulted so every later advance returns the same fault.
- Infallible convenience wrappers panic with the reducer fault as documented. A callback panic follows
  the separately documented trusted-code boundary and is not mislabeled a domain error.

#### GC, cache, trace, and accounting

- With the GC interval set to one allocation, each successful fixture can allocate multiple callback
  nodes and finish without reclaiming the redex, normal arguments, resolved hooks, intermediate built
  nodes, result, or trace data. Collection after the callback keeps only normally rooted reachable
  values.
- A test-only observational reducer counts invocations without changing semantic output. Reducing the
  same original DAG twice invokes Rust once; the second call follows the current-epoch normal-form cache
  and adds zero rewrites.
- Building a new Engine against a catalog whose same key has a different implementation invokes the new
  implementation and cannot accept a DAG or cache entry from the old Engine. Live replacement on the
  original Engine is unavailable.
- The exact counts and event order in §25.5 are asserted. `Decline` and faults add zero successful host
  rewrites. Normalization of a returned term contributes its own subsequent equation/special counts.
- Structured host trace identity is
  `TraceEvent::Rewrite { kind: RewriteKind::HostFunction, host_key: Some(canonical_key), ... }`;
  every other `TraceEvent::Rewrite` has `host_key: None`. Rendered host trace output includes that same
  canonical key. Renaming changes displayed TNK terms only; dense catalog/binding IDs never replace the
  user-facing identity.

#### Release gate

- The fixture tests pass in the default workspace with `cargo test --workspace`; all public examples and
  compile-fail contracts are included in that command, and `cargo check --workspace --all-targets`
  remains clean.
- The manual hook catalogue, reduction semantics, Rust API map, feature matrix, panic/fault contract,
  purity obligations, and configured Session example are updated from “planned” to the shipped
  behavior.
- TNK-DEV-017 records the chosen public surface, fallible error policy, host-binding seal, primary
  `text.normalize-tag` fixture, and evidence for this matrix. No required case may be ignored, marked
  expected-failure, or replaced solely by a unit test that bypasses parsing, module construction, and
  Session dispatch.

Stage 1 is complete only when every item in §22 and §25 passes. Passing the three Rust functions in
isolation, or supporting direct programmatic callbacks without the configured module/Session paths,
does not constitute the feature.

## 26. Shipped decision and evidence

Stage 1 shipped with these selected boundaries:

- **Public surface:** the shipped `tnk_core::host` symbols are:
  - registration/identity: `HostFunctionCatalog`, `HostFunctionCatalogBuilder`,
    `HostFunctionKey`, opaque `HostFunctionId`, and `HostFunctionRegistrationError`;
  - descriptors/build-time binding: `StrictReducerDescriptor`,
    `StrictReducerDescriptorBuilder`, `HookSort`, `OpHookRequirement`, `TermHookRequirement`,
    `ResolvedHostHooks`, `ResolvedHostHooksBuilder`, opaque `HostBindingId`, and
    `HostBindingError`;
  - callback protocol: `StrictReducer`, `StrictCall`, `StrictReduceCtx`, `ScopedHostHooks`,
    `HostSymbol`, `NormalDag`, `RedexDag`, `DagRef`, `DagView`, `ChildView`, `BuiltDag`,
    `StrictOutcome`, `ReducerFault`, and `BuildError`;
  - typed support: `codecs`, `codecs::StringCodec`, `codecs::string`, and
    `HostFunctionCatalogBuilder::{register,register_typed1,register_typed2,build}`.
  `ResolvedHostHooks` supplies build-time binding data, but raw lookup is crate-private; callbacks
  receive scoped `HostSymbol` capabilities instead. Outer embedding entry points are
  `Session::{builder}` / `SessionBuilder::{host_functions,build}`,
  `Engine::{with_host_functions,host_functions,validate_host_function_binding,bind_host_function,try_prepare_identities,try_normalize_for_unify,try_symbol_identity_dag}`,
  `tnk_frontend::load::{load_source_with_host_functions,build_loaded_module_with_host_functions,try_build_loaded_module_with_host_functions,build_loaded_module_with_host_functions_and_inline_statements,try_build_loaded_module_with_host_functions_and_inline_statements,build_loaded_module_homed_with_host_functions,build_loaded_module_homed_traced_with_host_functions,try_build_loaded_module_homed_traced_with_host_functions,LoadedModuleBuildError}`,
  and `tnk_modules::{load::{flatten_and_build_with_host_functions,load_program_with_host_functions},view::validate_view_with_host_functions,meta::MetaDescent::with_host_functions}`.
- **Error/trust policy:** native decode miss and explicit `Decline` are ordinary fallthrough; invalid source attachment is an atomic build diagnostic; callback/result-contract failures are `ReducerFault`. On that fault, the owning operation restores TNK-owned state, aggregate/breakdown counts, and trace append state, attempts no equation fallback, and poisons a resumable owner to return the same error thereafter. Session renders one fault and clears continuation state; fallible lower-level drivers return it; documented infallible convenience methods panic. Arbitrary callback panics are not caught, translated, or promised rollback. Callbacks remain pure deterministic synchronous code and receive no cancellation, timeout, callback-controlled transaction, callback-side-effect rollback, or resource bound.
- **Immutability seal:** a catalog is immutable after `build`; a signature stores dense catalog/binding IDs; attachments are rejected after semantic execution starts; replacing an implementation requires a new Engine/Session.
- **Reserved control boundary:** `HostControlSymbol` is Unsupported and inert/nonbinding; it never resolves through the strict catalog even when its token matches a registered key.
- **Primary fixture:** `text.normalize-tag` in `crates/tnk-session/tests/strict_rust_reducers.rs`, alongside typed binary `path.join`, low-level symbolic `routing.prefer-configured`, and explicit `testing.fail`.
- **Integration coverage:** the Session fixture exercises parsing, source attachment, strict argument reduction, typed decoding, low-level DAG inspection/construction, ordinary and `[owise]` fallthrough, result re-normalization, trace/count identity, invalid strategies/theories/arity/hooks/overloads, module sums, renaming, parameters, views, instantiation, dependent rebuilds, reflection, child interpreters, faults, and empty-catalog rejection. Core tests cover callback proof boundaries, GC pressure, cache/epoch sealing, sort/provenance validation, panic policy, and fallible semantic owners. Rustdoc compile-fail examples enforce wrapper non-forgeability and non-escape.

The completion gate is enforced by:

```sh
cargo test --workspace
cargo check --workspace --all-targets
cargo check --workspace --all-targets --all-features
```

The shipped normative behavior is in Reference §16.1.1, §20–22, Appendix G.3, Appendix I, and the `TNK-HOST-*` clauses. General strategy-aware Rust control, stateful callbacks, dynamic loading, sandboxing, and a stable plugin ABI remain outside Stage 1.