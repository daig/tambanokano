# TNK-DEV-014 — Unsupported special hooks and LOOP-MODE

**Status:** Known gap  
**Type:** Hook and library surface  
**Current contract:** [`docs/manual.md` Appendix G/K](../../manual.md#appendix-g--built-in-hook-catalogue)

## Current behavior

A recognized or unknown `id-hook` class without a TNK implementation attaches no `SpecialOp`; the operator remains ordinary and the condition is currently silent. `MatrixOpSymbol`, `LoopSymbol`, and other unlisted hook classes therefore do not acquire built-in semantics. LOOP-MODE is not a supported runtime capability.

## Missing work

There are two independent concerns:

1. unsupported hooks need a clear diagnostic or typed unsupported outcome, tracked with TNK-DEV-009;
2. any hook implementation needs its own selected feature issue and source-derived contract.

LOOP-MODE in particular would require an explicit host/session input-output state model rather than attaching an isolated reduction hook.

## Constraints

- Never bind an unknown class to a superficially similar operation.
- An inert operator may still reduce by user equations; diagnostics must not imply the declaration is unusable.
- Host interaction cannot introduce global mutable runtime state.
- LOOP-MODE, if selected, must define Session ownership, input injection, output extraction, continuation, and cancellation interaction.

## Selection gate

First make unsupported hook handling explicit without changing ordinary operator behavior. Select individual hook families only with declarations, runtime semantics, failure behavior, library prerequisites, and public-path tests. Listing a class here does not commit TNK to implementing it.
