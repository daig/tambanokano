# TNK-DEV-006 — META/reflection completion

**Status:** Known gap  
**Type:** Metalevel feature  
**Current contract:** [`docs/manual.md` §16.2 and Appendix G/K](../../manual.md#162-reflection)

## Current behavior

The supported reflection/descent families are enumerated in the Reference. Known boundaries include:

- conditional constraints in reflected `metaMatch` are unsupported;
- `metaNarrow2` state-only dispatch is recognized but inert;
- unknown META operation codes remain inert;
- some flat-module up-mapping involving `special` or `poly` declarations may return a deferred/failure value;
- strategy parse/pretty-print and conditional match/apply cases need permanent boundary coverage under TNK-DEV-001.

## Missing work

Potential implementation work is intentionally not bundled into one phase. Before selecting a slice, characterize it independently:

1. conditional reflected matching and rule application through a reusable condition-evaluation seam;
2. complete flat reflected-module up-mapping for supported `special`, `poly`, and retained attributes;
3. Strategy-to/from-surface translation for `metaParseStrategy` and `metaPrettyPrintStrategy` without losing strategy sugar;
4. an explicit decision on `metaNarrow2` state-only semantics;
5. diagnostics or typed unsupported outcomes for recognized inert dispatch.

## Constraints

- An unsupported or malformed operation must never fall through to another `MetaOp`.
- Source and flat reflection are distinct contracts; do not fabricate source structure from a flat module.
- Up/down translation must not carry engine-local IDs across module or child-Session boundaries.
- Multi-solution caches must preserve request identity and continuation semantics.
- Implement one complete family at a time with public-path behavior tests.

## Selection gate

A selected subissue must define its exact request signatures, success/failure values, caching behavior, rewrite-count boundary where applicable, and Reference update. TNK-DEV-001 coverage lands before or with any behavior change.

## Provenance

Consolidates still-current META gaps from the historical audit and implementation plans. Completed local interpreter work is not part of this issue; concurrency belongs to TNK-DEV-002.
