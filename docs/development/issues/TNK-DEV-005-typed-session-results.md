# TNK-DEV-005 — Typed Session result and diagnostic API

**Status:** Decision needed  
**Type:** Public API  
**Current contract:** [`docs/manual.md` §§17 and 20](../../manual.md#17-session-state-machine)

## Current behavior

`Session::eval` returns `Eval { output: String, exit: bool }`. The text is presentation output, not a typed semantic event stream. It does not expose structured diagnostics, completion, unsupported capability, resource exhaustion, backend status, continuation identity, or symbolic incompleteness. Clients needing typed semantic data must use lower-level APIs.

## Decision

Decide whether the primary embedding boundary should remain presentation-oriented or gain a typed result/event API alongside `eval`.

The design must settle:

- event versus aggregate-result shape;
- typed success, finite failure, unsupported, incomplete, backend-unknown, and resource outcomes;
- command echo and human rendering ownership;
- continuation and request identity;
- diagnostics with stable category/state effect but non-stable prose;
- compatibility and allocation costs for hosts that only need text.

## Constraints

- Do not parse the existing output string to manufacture typed results.
- Preserve `eval` behavior unless a deliberate API cutover is approved.
- Lower-level engine IDs and roots must not escape Session ownership.
- A typed API must represent partial result streams and retained continuations without claiming exhaustion.
- Cancellation outcomes, if introduced by TNK-DEV-002, must compose with this model but cannot force an executor dependency.

## Decision gate

Approve either:

1. no typed Session API; lower-level crates remain the typed boundary;
2. a parallel typed operation/event API with rendering as an adapter;
3. a clean replacement during a declared breaking API transition.

The selected design requires end-to-end examples for success, unsupported input, incomplete enumeration, backend `Unknown`, and continuation.
