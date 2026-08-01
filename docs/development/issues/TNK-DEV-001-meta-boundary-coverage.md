# TNK-DEV-001 — Re-home META boundary coverage

**Status:** Selected  
**Type:** Coverage  
**Current contract:** [`docs/manual.md` §16.2 and Appendix K](../../manual.md#162-reflection)

## Current behavior

TNK implements the reflected operations listed in the Reference and deliberately leaves unsupported or unresolved operations inert or represented by the loaded facade's failure value. Release cleanup removed a probe that covered several supported and unsupported boundary cases; retained tests do not represent every case.

## Work

Add permanent behavior-level coverage for:

- proper-residue `metaXmatch` and `metaXapply`;
- partial-AC whole-pattern `metaXmatch` and `metaXapply`, including bindings, values, and contexts;
- conditioned `metaMatch` and `metaXmatch`;
- conditional-rule `metaApply` and `metaXapply`;
- `metaParseStrategy` and `metaPrettyPrintStrategy`;
- `upModule` and literal reflected-module memo attributes.

This issue is about accurately pinning the current boundary. It does not authorize implementing every unsupported operation in the list. Feature changes belong in TNK-DEV-006 or a narrower issue.

## Constraints

- Test the public `Session` or REPL path, not source text or internal dispatch tables.
- Supported operations must retain their semantic results.
- Unsupported operations must remain recoverable and inert rather than dispatching to an unrelated operation.
- Historical Maude differential output is provenance, not a new TNK compatibility promise.
- Tests must distinguish unsupported, no-result, malformed, and successful outcomes where the public surface exposes that distinction.

## Completion gate

- Every listed boundary has retained behavior-level coverage.
- Each test fails for a plausible dispatch, residue, condition, context, or recovery regression.
- The Reference is updated only if the observed user-visible boundary changes.

## Provenance

Migrated from the former root `TODO.md` and the deleted `conformance/probes/meta-recognized-boundaries.maude` coverage note.
