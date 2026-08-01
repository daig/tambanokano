# TNK-DEV-010 — Conditional narrowing rules

**Status:** Known gap  
**Type:** Symbolic feature  
**Current contract:** [`docs/manual.md` §13 and §24](../../manual.md#13-variants-and-narrowing)

## Current behavior

A conditional rule carrying `[narrowing]` is diagnosed and dropped. The enclosing buildable module and later valid statements remain installed. Unconditional narrowing rules remain supported within the documented completeness boundary.

## Missing work

Conditional narrowing requires a symbolic condition solver that composes each fragment with the narrowing state's accumulated substitution, fresh-variable family, reducibility constraints, folding/history, and incompleteness signal. It cannot reuse ordinary ground condition evaluation without defining symbolic solution enumeration.

## Constraints

- Do not retain a conditional narrowing rule as if it were unconditional.
- Every condition-produced binding must compose into the narrowed result and path history.
- Equation, membership, matching, and rewrite condition fragments need explicit supported scopes.
- Nested unifier or variant incompleteness must propagate to the public low-level result.
- Folding/subsumption must compare states after condition substitutions are applied.

## Selection gate

Characterize the upstream semantics and choose an initial complete condition subset. Add object-level and metalevel cases for success, finite failure, multiple condition solutions, folding, paths, bounds, and incompleteness. Update the Reference only for the subset implemented end to end.
