# TNK-DEV-007 — Strategy-language completion

**Status:** Known gap  
**Type:** Strategy feature  
**Current contract:** [`docs/manual.md` §11](../../manual.md#11-strategies)

## Current behavior

`xmatchrew` and conditional strategy definitions (`csd`) parse but are rejected during strategy resolution. Unconditional definitions, `matchrew`, `amatchrew`, strategy tests including `xmatch`, module imports, transforms, and recursive parameterized calls remain separate supported surfaces.

## Missing work

The two gaps have different implementation roots and should be split when either is selected:

### Extension match-rewrite

`xmatchrew` needs the strategy executor to retain the extension match's matched portion and residue, rewrite the selected variables, and reconstruct the enclosing associative/AC subject without losing canonicalization or bindings.

### Conditional strategy definitions

`csd` needs runtime evaluation of definition conditions under the matched call substitution, including condition-produced bindings that flow into the body. Compile-time parameter-token substitution is insufficient.

## Constraints

- Do not weaken resolution-time rejection until a form is complete end to end.
- Preserve fair and depth-first scheduler behavior.
- Keep extension residue, variable bindings, and reconstructed value semantically consistent.
- Conditional execution must use the shared condition semantics rather than a strategy-only evaluator.
- Imported, renamed, instantiated, and reflected definitions must carry the same behavior as local definitions.

## Completion gate

For a selected form, add direct and module-composed cases covering success, failure, multiple solutions, conditions, counts/state, and parser recovery after rejection. Update `TNK-STRAT-003` only when the form no longer rejects.

## Provenance

Both gaps remained explicit after the completed strategy-import goal. They are current unsupported boundaries, not regressions in the shipped unconditional strategy surface.
