# TNK-DEV-013 — Ordinary search tracing

**Status:** Known gap  
**Type:** Tooling  
**Current contract:** [`docs/manual.md` §24](../../manual.md#24-unsupported-and-intentionally-absent-behavior)

## Current behavior

`set trace on` does not trace rule applications performed by ordinary breadth-first `search`. Search graph and path inspection remain available, and tracing in other execution contexts does not imply search tracing.

## Missing work

Search tracing needs an event boundary over generated transitions, condition work, reductions, state deduplication, and accepted solutions. The design must decide which events are emitted and how tracing interacts with retained search continuations.

## Constraints

- Tracing is observational: it must not alter state discovery, deduplication, result sets, bounds, counts, or continuation behavior.
- Trace selection/exclusion, if added, must filter events rather than execution.
- Event data must remain rooted while rendered without retaining the entire graph accidentally.
- Human trace prose is Experimental; semantic event ownership and state identity must be deterministic enough for debugging.

## Selection gate

Define the event model and selection semantics before presentation work. Cover transitions with conditions, duplicate-state suppression, bounded continuation, no-solution search, and graph/path agreement. Update the Reference when ordinary search tracing becomes available.
