# TNK-DEV-004 — Import-mode protection semantics

**Status:** Decision needed  
**Type:** Language semantics  
**Current contract:** [`docs/manual.md` §6](../../manual.md#6-module-expressions-and-composition)

## Current behavior

`protecting`, `extending`, and `including` donate the same executable closure. Source mode tags remain available to reflection, but TNK does not enforce Maude-style no-junk/no-confusion protection obligations. The Reference classifies the semantic distinction as Experimental.

## Decision

Choose whether import modes should remain documentary/reflection metadata or acquire enforceable semantic obligations.

A decision to enforce them must define:

- what is checked and at which build/instantiation boundary;
- behavior for parameterized modules and views;
- whether violations reject a definition, warn, or mark it unusable;
- interaction with sums, renaming, redefinition, and reflection;
- what completeness claim is possible for the checks.

## Constraints

- Current successful composition cannot silently change meaning.
- A partial checker must not present an unchecked module as fully protecting.
- Failed definitions must preserve the prior database and dependent build state.
- Source mode tags must survive every supported module transform regardless of enforcement policy.

## Decision gate

Record one of:

1. keep import modes as permanent metadata-only syntax and stabilize that behavior;
2. implement a precisely bounded protection checker;
3. defer enforcement while retaining the current Experimental classification.

## Provenance

The gap is user-visible in the current Reference and descends from the migration audit's module-algebra review. It is separate from TNK-DEV-003: compiled statements may help enforcement, but choosing a statement representation does not itself define protection semantics.
