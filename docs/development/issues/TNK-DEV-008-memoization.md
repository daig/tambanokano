# TNK-DEV-008 — Memoization semantics

**Status:** Known gap  
**Type:** Runtime feature  
**Current contract:** [`docs/manual.md` §24 and Appendix F/K](../../manual.md#24-unsupported-and-intentionally-absent-behavior)

## Current behavior

The `[memo]` operator attribute is parsed and retained as metadata, with a warning, but it does not cache reductions. Memo controls such as `set memo`, `set clear memo`, and `do clear memo` warn and have no effect. Reflected memo attributes remain part of TNK-DEV-001's boundary coverage.

## Missing work

A real implementation requires decisions about:

- cache key identity under axioms and overloaded symbols;
- result rooting, GC interaction, and invalidation;
- module/view redefinition and dependent rebuilds;
- rewrite counts for cache hits;
- interaction with stateful built-ins, conditions, strategies, and reflected modules;
- control commands and cache inspection/clearing;
- whether memoization is per Engine, loaded module, or Session.

## Constraints

- Do not treat construction deduplication or normal-form forwarding as memo semantics.
- A cache cannot retain unrooted or cross-engine DAG IDs.
- Redefinition must not expose values computed under an obsolete signature or equation set.
- Stateful or context-sensitive operations must not be cached accidentally.
- Enabling memoization cannot silently change semantic values or Session isolation.

## Selection gate

Before implementation, record the cache lifetime, eligibility rules, count contract, invalidation graph, and observable control behavior. Add tests for hit/miss equivalence, GC, redefinition, independent Sessions, reflected declarations, and clear controls.
