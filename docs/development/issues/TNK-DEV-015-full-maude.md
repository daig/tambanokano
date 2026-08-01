# TNK-DEV-015 — Full Maude library support

**Status:** Decision needed  
**Type:** Feature scope  
**Current contract:** No Full Maude capability is claimed by the 0.1.0 Reference.

## Background

Historical migration plans treated Full Maude as a metalevel `.maude` library to run on top of reflection, module composition, and strategy metaprogramming rather than as Rust engine code. Object-oriented syntax already has a native frontend desugaring path and must not be conflated with Full Maude support.

## Decision

Decide whether running a specified Full Maude library is an intended TNK capability.

Before approval, characterize:

- the exact library version and license/distribution boundary;
- required META-LEVEL and strategy parse/print operations;
- module/view reflection and compiled-statement requirements;
- unsupported external I/O or LOOP-MODE dependencies;
- what “support” means: loadability, selected workflows, or broader compatibility.

## Constraints

- Ship the library as data if licensing permits; do not port the metaprogram into bespoke Rust semantics.
- Do not claim Full Maude based only on object-module syntax support.
- Missing reflective prerequisites must remain explicit rather than receiving fixture-specific shortcuts.
- This decision depends on TNK-DEV-003 and parts of TNK-DEV-006/007, but those issues do not imply approval.

## Decision gate

Record one of:

1. Full Maude is out of scope;
2. support a pinned library and enumerated workflows;
3. pursue a broader compatibility target with prerequisite issues and a separate acceptance contract.

## Provenance

Carried forward because the recovered roadmap described it as intended feature work, but no current release document promises it. Its presence in the index records an unresolved scope decision, not a commitment.
