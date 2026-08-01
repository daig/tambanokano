# TNK-DEV-011 — Unsupported unification theories

**Status:** Known gap  
**Type:** Symbolic feature  
**Current contract:** [`docs/manual.md` §12 and Appendix K](../../manual.md#12-order-sorted-unification)

## Current behavior

TNK rejects non-ground unification under idempotent CUI operators and associative operators with one-sided identity where no supported solver applies. Low-level readiness reports unsupported; the current Session presentation may emit only the command echo, which is separately tracked by TNK-DEV-009. AU/nonlinear unification can also be sound but incomplete and exposes that distinction at the low-level API.

## Missing work

Potential extensions must be selected per theory:

- idempotent non-ground CUI unification;
- associative one-sided-identity unification;
- broader or more complete AU/nonlinear word solving.

These are algorithmic capability changes, not diagnostic fixes.

## Constraints

- Never turn unsupported or incomplete into `No unifier.`
- Every emitted substitution must remain sound, sort-correct, and theory-canonical.
- Completeness must be machine-readable where the algorithm cannot close the search space.
- Variant and narrowing callers must receive the same unsupported/incomplete signal.
- Ground canonicalization and matching support do not imply non-ground unification support.

## Selection gate

Each theory extension needs a source-derived semantic contract, finite/infinite-family analysis, low-level readiness behavior, direct and composed tests, and explicit completeness propagation through variant/narrowing and Session presentation.
