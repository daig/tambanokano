# TNK-DEV-016 — Timing measurement

**Status:** Known gap  
**Type:** Presentation and tooling  
**Current contract:** [`docs/manual.md` §24 and Appendix H/K](../../manual.md#24-unsupported-and-intentionally-absent-behavior)

## Current behavior

Timing measurement is unavailable. `set show timing on` warns and does not enable timing rows. Rewrite totals exposed elsewhere are semantic/diagnostic records, not elapsed-time measurements.

## Missing work

A timing feature needs a host-owned clock boundary and a presentation contract for elapsed, CPU, and throughput fields. It must distinguish measured work from parsing, loading, rendering, and continuation intervals.

## Constraints

- Timing cannot become semantic input to evaluation or scheduling.
- No exact timing value or cross-machine performance is a compatibility guarantee.
- Library code should receive a clock/measurement adapter or return counters; it should not acquire terminal policy.
- Continuations need an explicit per-call versus cumulative measurement rule.
- The default disabled path should avoid unnecessary clock calls and formatting work.

## Selection gate

Define measured intervals, fields, enable/disable state, continuation accumulation, and host API before implementation. Tests should use an injected deterministic clock for record shape and state transitions; performance claims require separate benchmarks, not unit-test thresholds.
