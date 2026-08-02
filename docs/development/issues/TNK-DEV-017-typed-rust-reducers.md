# TNK-DEV-017 — Typed Rust reducers and future control extensions

**Status:** Closed — Stage 1 implemented on 2026-08-02; future control extensions remain unselected
**Type:** Runtime and public extension API
**Current contract:** [`docs/manual.md` §3.2, §16.1.1, and Appendix G.3](../../manual.md#1611-strict-rust-reducers)
**Focused Stage 1 design:** [`strict-rust-reducers-design.md`](../strict-rust-reducers-design.md)

## Purpose

TNK supports Rust-defined strict equational functions. TNK normalizes every argument before invoking the Rust reducer, invokes it at one final top-reduction point, and normalizes any returned term through the ordinary reduction loop.

This first class must not make host-defined lazy or staged control operators impossible. A later design may distinguish normal arguments from suspended DAGs at the Rust type boundary and allow a trusted control extension to participate in argument-demand decisions. That general facility is not yet specified or selected for implementation. This issue records the compatibility boundary that Stage 1 must preserve while those decisions remain open.

This issue is not a commitment to arbitrary Rust callbacks. Any extension class must uphold the reduction, sorting, theory, caching, GC, and accounting invariants appropriate to its semantic role.

## Current behavior

Hosts construct an immutable `tnk_core::host::HostFunctionCatalog` before module construction. `Session::builder().host_functions(...)`, catalog-aware frontend/module loaders, and `Engine::with_host_functions` carry that capability set into built signatures. Source operators bind an exact canonical key through `special (id-hook HostFunctionSymbol (KEY) ...)`; descriptor-declared `op-hook` and `term-hook` references are resolved and sort-checked while the signature is built. A key matches `^[a-z](?:[a-z0-9-]*[a-z0-9])?(?:\.[a-z](?:[a-z0-9-]*[a-z0-9])?)+$`: every segment begins lowercase, contains only lowercase ASCII letters/digits/interior hyphens, never ends in a hyphen, and at least one dot separates segments.

Only fixed-arity free root operators with the standard eager strategy are admitted. Each direct argument is current-epoch normal before one final callback. `StrictOutcome::Decline` falls through to ordinary equations and then `[owise]`; `Reduced(BuiltDag)` is provenance/sort checked, counts one host step, and re-enters ordinary normalization. A successful structured trace is `TraceEvent::Rewrite { kind: RewriteKind::HostFunction, host_key: Some(canonical_key), ... }`, every other `TraceEvent::Rewrite` has `host_key: None`, and rendered host traces include that same key. `ReducerFault` aborts the owning semantic operation. Session renders one error and saves no continuation; lower-level fallible drivers return the fault. A catalog is immutable once built, and signature attachments seal when semantic execution begins; changing an implementation requires a new catalog and a newly built Engine/Session.

The callback receives scoped proof wrappers and a narrow `StrictReduceCtx`, never raw `DagId` values or `&mut Engine`. `StrictCall::hooks()` returns `ScopedHostHooks<'ctx>`; a purpose lookup produces an opaque `HostSymbol<'ctx>` that can be used for same-callback construction but cannot expose or escape as a raw supporting-hook ID. The context may inspect `DagView`/`ChildView`, test groundness, fallibly decode native values, and construct constants, native strings, or theory-aware free/ACU/AU/CUI applications with declared identity canonicalization. It cannot mutate the signature, re-enter reduction, initiate collection, forge reduction metadata, mix Engines, or retain callback-scoped values. Typed string adapters borrow existing byte payloads as `&[u8]` without input cloning/allocation, invoke Rust only after every argument decodes, and encode the owned `Vec<u8>` output through the resolved `stringSymbol`. Catalogs propagate through module composition, dependent rebuilds, META descent, and child interpreters. Existing TNK-owned `SpecialOp` variants keep their bespoke behavior.

Unsupported non-host id-hook classes remain tracked by [TNK-DEV-014](TNK-DEV-014-unsupported-hooks.md). A missing `HostFunctionSymbol` capability is different: it is an explicit module-build error, not an inert ordinary operator. `HostControlSymbol` is a reserved, Unsupported future boundary: it never consults the strict catalog or installs a binding, and its operator remains ordinary/inert even when its data token matches a registered strict key.

Runtime normality is metadata, not a distinct DAG representation. Every runtime term is an engine-relative `DagId`. A node records the equation epoch at which it was proved canonical and may forward to an out-of-place normal form. Unreduced applications and normal forms use the same `NodeTerm` representations. Structural construction has already canonicalized declared axioms such as associativity, commutativity, identity, and iteration even when equational reduction is still pending.

Normality, groundness, and native decodability are independent:

- a ground term can still be reducible;
- a symbolic term can be a normal form;
- a normal form of sort `Int` need not be a canonical integer representation that Rust can decode;
- a suspended DAG is not source quotation because parsing layout and theory-erased structure may already be gone.

## Accepted staged direction

### Stage 1 — strict eager Rust reducers

The implemented Rust extension class models a pure equational function over canonical argument normal forms.

At minimum its contract is:

1. Registration is resolved before the containing module/signature is used for reduction and remains stable for the relevant signature epoch.
2. The attached operator uses an eager evaluation schedule accepted by the extension contract.
3. TNK normalizes every physical argument before invoking Rust.
4. Rust is invoked once at the final top-reduction point for that redex state.
5. Inputs are scoped wrappers proving current-engine, current-epoch normality rather than unqualified `DagId`s.
6. Symbolic normal forms remain legal inputs. Native decoding is an explicit fallible refinement, not an implication of normality or sort.
7. Rust may decline, allowing ordinary equations to run, or return a same-engine, structurally valid, well-sorted term.
8. The returned term need not already be normal; TNK normalizes it through the ordinary loop.
9. A successful return is counted and traced centrally as one outer host-function rewrite. The reducer does not charge that step itself.
10. The reducer is deterministic and referentially transparent with respect to the canonical redex and immutable attachment/signature state. Ordinary reduction cannot depend on time, I/O, randomness, mutable result-affecting host state, nondeterministic services, or externally visible side effects.
11. Rust cannot mutate the active signature, forge DAG metadata, initiate collection at an unsafe point, retain unrooted IDs/capabilities, mix engines, or re-enter the mutably borrowed engine.
12. Callback panics are not caught or translated to `ReducerFault`; they follow the embedding's Rust unwind/abort policy.
13. Execution is synchronous and supplies no cancellation, timeout, async yield, preemption, callback-controlled transaction, or resource bound. A returned `ReducerFault` restores TNK-owned operation state, aggregate/breakdown counts, and trace append state, attempts no equation fallback, and leaves a resumable owner returning the same fault; callback-authored external side effects and arbitrary panics have no rollback guarantee. Reducer authors own termination and CPU/memory behavior; interruptible or untrusted execution requires outer process isolation.
14. Stateful, externally observable, nondeterministic, or I/O operations use a rewrite-, external-object-, or descent-level contract instead of this equational reducer class.

Standard left-to-right eager evaluation is the conservative initial policy. Whether Stage 1 may also admit a permutation that still evaluates every argument before one final top attempt is an explicit decision below; implementations must not accidentally accept early-top or omitted-argument schedules.

### Reserved future — strategy-aware control extensions

A future trusted extension class may define short-circuiting, conditionals, lazy destructors, staged symbolic dispatch, or other evaluator-control operations. It may need to observe that some arguments are normal while others are deliberately suspended and to request additional argument evaluation before a later top attempt.

This is a different semantic role from a strict foreign function. It must be represented as a separate attachment and Rust trait/protocol rather than weakening every strict reducer to accept partially evaluated inputs.

The motivating distinctions are conceptually:

```rust
NormalDag<'ctx>       // canonical for the current engine equation epoch
SuspendedDag<'ctx>    // structurally valid current-engine term, not promised E/M/H-normal
GroundNormalDag<'ctx> // normal and variable-free
BuiltDag<'ctx>        // safely constructed result, not promised normal
Decoded<'ctx, T>      // a recognized native value view, obtained fallibly
```

Names and exact shapes are provisional. Constructors for proof-bearing wrappers must remain engine-controlled. Lifetimes must prevent values from escaping the callback unless explicitly rooted and revalidated.

A control protocol may eventually need an argument-state sum and explicit scheduling outcomes, for example:

```rust
ArgumentState::Normal(NormalDag)
ArgumentState::Suspended(SuspendedDag)

ControlDecision::Reduced(BuiltDag)
ControlDecision::DemandArgument(position)
ControlDecision::DeclineFinal
```

This sketch records required semantic distinctions only. It does not select callback-driven demand over source-declared `strat (...)`, does not define the meaning of an early decline, and is not a public API proposal.

## Why the distinction matters

A strict reducer is a function over argument normal forms. It has one meaningful call point and can base native decoding and sort checks on stable inputs.

A strategy-aware control extension is part of the evaluator. The same redex may be presented repeatedly as arguments transition from suspended to normal. It must distinguish at least:

- “reduce argument `i` and ask me again”;
- “I am inapplicable at this final state; try equations”;
- “return this suspended argument without evaluating the others”;
- “remain stuck without forcing omitted arguments.”

Conflating those outcomes with one `Option<DagId>` would make fallthrough, callback multiplicity, caching, and termination ambiguous.

Strict evaluation intentionally cannot implement behavior such as:

```text
if true then 42 else diverge fi  -> 42
false and diverge                -> false
first(x, diverge)                -> x
```

TNK's existing `Branch` special is an evaluator-control primitive: it evaluates the condition, attempts selection, and evaluates remaining branches only after failed selection. It must remain outside the strict reducer contract. Preserving a separate future control-extension namespace is how Stage 1 avoids claiming that all specials are strict functions.

## Stage 1 type and API boundary

Stage 1 exposes proof-bearing callback types rather than pretending that normal forms are necessarily concrete values. The exact shipped signatures are authoritative in `tnk_core::host`; the shape below records the design distinction that selected them:

The shipped `tnk_core::host` public symbol set is:

- registration and identity: `HostFunctionCatalog`, `HostFunctionCatalogBuilder`,
  `HostFunctionKey`, opaque `HostFunctionId`, and `HostFunctionRegistrationError`;
- descriptors and build-time binding: `StrictReducerDescriptor`,
  `StrictReducerDescriptorBuilder`, `HookSort`, `OpHookRequirement`, `TermHookRequirement`,
  `ResolvedHostHooks`, `ResolvedHostHooksBuilder`, opaque `HostBindingId`, and
  `HostBindingError`;
- callback protocol: `StrictReducer`, `StrictCall`, `StrictReduceCtx`, `ScopedHostHooks`,
  `HostSymbol`, `NormalDag`, `RedexDag`, `DagRef`, `DagView`, `ChildView`, `BuiltDag`,
  `StrictOutcome`, `ReducerFault`, and `BuildError`;
- typed string support: `codecs`, `codecs::StringCodec`, and `codecs::string`.

`ResolvedHostHooks` is build-time Engine binding data; its raw lookup is crate-private. Callback
lookups are available only through `ScopedHostHooks` and return callback-scoped `HostSymbol`
capabilities. The catalog-aware outer entry points are `SessionBuilder::host_functions`,
`Engine::{with_host_functions,host_functions,validate_host_function_binding,bind_host_function,try_prepare_identities,try_normalize_for_unify,try_symbol_identity_dag}`,
the public `tnk-frontend` configured entry points
`load::{load_source_with_host_functions,build_loaded_module_with_host_functions,try_build_loaded_module_with_host_functions,build_loaded_module_with_host_functions_and_inline_statements,try_build_loaded_module_with_host_functions_and_inline_statements,build_loaded_module_homed_with_host_functions,build_loaded_module_homed_traced_with_host_functions,try_build_loaded_module_homed_traced_with_host_functions,LoadedModuleBuildError}`; and
`tnk-modules::{load::{flatten_and_build_with_host_functions,load_program_with_host_functions},
view::validate_view_with_host_functions,meta::MetaDescent::with_host_functions}`.

```rust
trait StrictReducer: Send + Sync + 'static {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault>;
}

enum StrictOutcome<'ctx> {
    Decline,
    Reduced(BuiltDag<'ctx>),
}
```

The design preserves these separations:

- `NormalDag` proves evaluation state, not groundness or native value shape;
- `decode_*` operations perform fallible representation recognition;
- `BuiltDag` proves provenance/construction invariants, not normality;
- missing registration, invalid attachment, reducer failure, and ordinary domain decline are distinct outcomes;
- a reducer registry identity is signature/cache state, not hidden mutable process-global state.

## Future-compatibility requirements for Stage 1

Stage 1 implementation must observe these rules even before the general control design exists:

1. **Do not publish bare `DagId` callbacks as the stable reducer API.** Use scoped context/wrapper types so later argument-state distinctions do not require breaking every reducer.
2. **Do not define “Rust special” as synonymous with “strict reducer.”** Give the strict attachment and trait a role-specific name, leaving a separate namespace for control, rewrite-state, descent, and external capabilities.
3. **Do not place closures or mutable host state directly in cloneable signature metadata.** Store a stable registry key/ID; keep implementation state in a host-owned registry with explicit lifetime and invalidation rules.
4. **Do not let `Decline` absorb capability or implementation errors.** A future control protocol needs decline to retain a precise reduction meaning.
5. **Do not expose `&mut Engine` to reducers.** A narrow context must remain extensible enough to add proof-bearing suspended views later without permitting signature mutation, reentrant reduction, or unsafe collection.
6. **Do not promise that `NormalDag` is a value, ground, or decodable.** Those refinements must remain separate.
7. **Do not use “quoted” to mean source-preserving syntax.** A suspended DAG is already structurally canonicalized. Explicit term-as-data/reflection remains the mechanism for genuine quotation.
8. **Keep result normalization outside the callback.** Future strict and control extensions must return safely built terms to the same outer normalization machinery.
9. **Version or classify attachment contracts explicitly.** Module build must know whether an operator requests strict eager reduction or evaluator control and validate its strategy accordingly.
10. **Keep current internal specials free to use their existing bespoke roles.** Stage 1 must not retrofit `Branch`, `Counter`, SMT markers, META descent, or external managers into the strict API merely to unify dispatch.

## Decisions required before Stage 1 implementation

### Source and registration

- Choose the source attachment spelling and whether it extends `special (id-hook ...)` or introduces an explicit host-hook subdirective/class.
- Define registry ownership: `Session`, lower-level module builder, `Engine`, or a shared immutable capability set.
- Define key naming, collision policy, registration lifetime, replacement behavior, and module rebuild behavior.
- Decide whether registered implementations are trusted in-process Rust only or whether any ABI/plugin mechanism is in scope. A dynamic binary ABI is not implied by this issue.
- Define missing-registration diagnostics and their atomic effect on module construction.

### Accepted eager strategy

- Decide whether only the standard left-to-right schedule is accepted.
- If eager permutations are accepted, define their observable divergence/order behavior and confirm the callback is still invoked once.
- Define behavior for associative operators whose flattened physical arity exceeds declaration arity.
- Reject top-first, intermediate-top, omitted-argument, and lazy schedules for strict reducers rather than silently rewriting their meaning.

### Evaluation-state proofs

- Define how `NormalDag` follows normal-form forwarding and records or borrows the current equation epoch.
- Define its relationship to least-sort membership refinement at the normal-form point.
- Decide whether wrappers are callback-only or can be rooted and retained with later revalidation.
- Define groundness checks and native value views without avoidable traversal or allocation.
- Decide whether a strict reducer receives the whole redex as well as normalized arguments and, if so, with what proof type.

### Sort and theory coherence

- Validate reducer arity, declaration profiles, result kind/sort, accepted structural theories, and supporting hook symbols at attachment time.
- Decide the runtime validation applied to returned terms: same engine, result kind, declared range compatibility, and error-sort policy.
- Require results to be invariant under the attached operator's structural theory. Canonical DAG input removes source bracketing/order but does not prove semantic compatibility.
- Define overlap responsibility when a successful reducer and user equation both define the same redex. Current special precedence alone does not prove confluence or coherence.

### Runtime behavior

- Specify panic containment and typed reducer errors separately from domain decline.
- Specify tracing identity, diagnostics, outer and nested rewrite accounting, and profiling.
- Specify cache invalidation when registry contents or reducer configuration change. Normal-form cache validity cannot depend only on the equation epoch if reducer semantics can change independently.
- Specify GC rooting and allocation rules during callbacks.
- Specify thread confinement and `Send`/`Sync` requirements without pre-committing the later concurrent Session design.
- Define resource and cancellation boundaries for a synchronous reducer. Purity does not guarantee prompt termination.

## Decisions deferred for a strategy-aware control extension

Before selecting a control extension, decide:

1. whether scheduling is source-declared through `strat (...)`, callback-driven through `DemandArgument`, or split into separately auditable descriptor and handler;
2. the exact type states visible at early and final top attempts;
3. whether suspended arguments may be inspected structurally, returned directly, rooted, or compared;
4. whether control callbacks may be invoked more than once per redex and what state they may retain between invocations;
5. the difference between early deferral, demand, final decline, stuckness, and implementation failure;
6. how custom control interacts with user equations, `[owise]`, memberships, tracing, and normal-form forwarding;
7. how associative flattening limits position-sensitive demand;
8. how to prevent a control extension from observing erased source syntax as if a DAG were a quotation;
9. what termination/progress obligations apply to repeated demand or unchanged-result cycles;
10. whether this power remains a sealed trusted API even if strict reducers become broadly registerable.

## Constraints and non-goals

- Stage 1 does not add stateful, asynchronous, nondeterministic, or I/O-performing reduction functions.
- Stage 1 does not make `Session` or `Engine` globally mutable and does not create a process-global reducer registry.
- Stage 1 does not promise a stable C ABI, dynamic library loader, sandbox, or panic-safe untrusted plugin boundary.
- Stage 1 does not redefine explicit META-LEVEL quotation or engine-neutral `MetaEnvelope` transport.
- Stage 1 does not remove or generalize existing `SpecialOp` variants solely for architectural uniformity.
- The future control sketch does not commit TNK to user-defined lazy operators; it preserves an intentional design opening.
- Observable Stage 1 behavior is normative in the Reference. Any future control extension requires its own selection record and Reference update.

## Stage 1 selection and completion gate

Before implementation is selected, record decisions for the Stage 1 source/registration, eager-strategy, type-proof, result-validation, cache-invalidation, diagnostics, and GC boundaries above.

Stage 1 is complete only when:

1. a host can register a strict reducer through the supported embedding path;
2. a module can bind an operator to it with validated eager strategy, arity, theory, and sort profiles;
3. the reducer receives only scoped current-epoch normal-form arguments and can fallibly decode supported native values;
4. domain decline falls through to equations, while missing capability and implementation errors are explicit;
5. successful results are provenance/sort checked, counted once, traced as specified, and normalized by TNK;
6. registry mutation cannot leave valid-looking stale normal-form cache entries;
7. tests cover concrete, symbolic-normal, undecodable, partial-domain, equation-fallback, wrong-sort/error, GC, and cache-invalidation behavior;
8. tests reject every prohibited lazy, omitted-argument, and early-top strategy shape;
9. the public types and source attachment preserve the future-compatibility requirements in this issue;
10. the Reference and Rust API map describe the shipped capability and its limits.

A strategy-aware control extension requires its own later selection record and completion gate. Stage 1 completion must not claim that general Rust-defined specials are supported.

## Stage 1 selected decisions and completion evidence

- **Source/registration:** `HostFunctionSymbol (KEY)` with the canonical segment grammar above into a host-owned immutable catalog; duplicate registration and missing capability are errors. Reserved `HostControlSymbol` is inert/nonbinding and never resolves through that catalog.
- **Accepted strategy/theory:** fixed arity, free root theory, non-polymorphic declaration, and only the normalized standard left-to-right eager schedule; lazy, omitted, repeated-top, early-top, and permuted schedules are rejected.
- **Type proof:** callback-scoped `NormalDag`, `RedexDag`, `DagRef`, `DagView`/`ChildView`, `ScopedHostHooks`, opaque `HostSymbol`, and `BuiltDag`; fallible zero-copy decoders and theory-aware builders through `StrictReduceCtx`; no raw-ID or Engine escape.
- **Results/faults/trust:** `Decline` means equation fallthrough only; a returned term is same-engine and selected-range checked; `ReducerFault` propagates through fallible semantic drivers and Session; documented infallible wrappers panic on faults. Trusted callback panics are not caught or mislabeled. Callbacks remain pure deterministic synchronous code with no cancellation/resource boundary.
- **Cache/lifecycle:** catalogs cannot mutate; signature attachments seal on first semantic execution; new semantics require a newly built Engine, invalidating any old engine-relative DAG/cache state by construction.
- **GC/accounting/trace:** callback live values remain in the active reduction root set; successful host return contributes exactly one `RewriteKind::HostFunction` event carrying/rendering the canonical host key; decline and faults contribute none, and every other `TraceEvent::Rewrite` carries no host key.
- **Primary fixtures:** `text.normalize-tag`, `path.join`, `routing.prefer-configured`, and `testing.fail` in `crates/tnk-session/tests/strict_rust_reducers.rs`. Core contracts and compile-fail proofs are in `crates/tnk-core/tests/strict_rust_reducers.rs` and `tnk_core::host` rustdoc.
- **Acceptance commands:** `cargo test --workspace`, `cargo check --workspace --all-targets`, and `cargo check --workspace --all-targets --all-features`.

The mandatory matrix in the focused design is implemented without ignored or expected-failure cases. Strategy-aware argument demand, stateful/nondeterministic reducers, external I/O, dynamic libraries, sandboxing, and a stable plugin ABI remain outside the shipped feature. Any such evaluator-control work must use a new issue and completion gate; it must not weaken `StrictReducer`.
