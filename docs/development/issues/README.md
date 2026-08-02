# Developer issue index

This directory tracks unresolved engineering work without imposing a roadmap or execution order. Each issue owns one decision, known gap, or intended feature. Listing an issue records knowledge; it does not by itself select the work or promise a release.

The user-facing contract remains in [`docs/manual.md`](../../manual.md). Issue records may link to that contract, but must not redefine current behavior. When implementation changes observable behavior, update the manual and the issue in the same change.

## Status vocabulary

| Status | Meaning |
|---|---|
| **Selected** | Approved current work with a defined completion condition. |
| **Planned** | Intended feature with an accepted design, not yet selected for implementation. |
| **Decision needed** | The gap is known, but scope or direction requires a recorded decision. |
| **Known gap** | Current behavior is understood; implementation is neither selected nor promised. |
| **Closed** | Decision or implementation is complete; retain only when its rationale is still needed. |

## Selected work

| ID | Issue | Type | User-facing boundary |
|---|---|---|---|
| TNK-DEV-001 | [Re-home META boundary coverage](TNK-DEV-001-meta-boundary-coverage.md) | Coverage | Reference §16.2 and Appendix K |

## Planned work

| ID | Issue | Type | User-facing boundary |
|---|---|---|---|
| TNK-DEV-002 | [Phase I-C concurrent runtime](TNK-DEV-002-ic-concurrent-runtime.md) | Feature | Reference §17, §24, Appendix K.1 |
| TNK-DEV-017 | [Typed Rust reducers and future control extensions](TNK-DEV-017-typed-rust-reducers.md) ([focused Stage 1 design](../strict-rust-reducers-design.md)) | Runtime/API feature | Reference §3.2, §16.1, and Appendix G |

## Pending decisions

| ID | Issue | Type | User-facing boundary |
|---|---|---|---|
| TNK-DEV-003 | [Compiled, import-stable module statements](TNK-DEV-003-module-statement-representation.md) | Architecture | Reference §§5–6 and Appendix K.3 |
| TNK-DEV-004 | [Import-mode protection semantics](TNK-DEV-004-import-mode-semantics.md) | Language semantics | Reference §6 and Appendix K.3 |
| TNK-DEV-005 | [Typed Session result and diagnostic API](TNK-DEV-005-typed-session-results.md) | Public API | Reference §§17, 20 and Appendix H/I/K |
| TNK-DEV-015 | [Full Maude library support](TNK-DEV-015-full-maude.md) | Feature scope | No current release capability |

## Known gaps

| ID | Issue | Type | User-facing boundary |
|---|---|---|---|
| TNK-DEV-006 | [META/reflection completion](TNK-DEV-006-meta-reflection-gaps.md) | Metalevel | Reference §16.2 and Appendix G/K |
| TNK-DEV-007 | [Strategy-language completion](TNK-DEV-007-strategy-language-gaps.md) | Strategy | Reference §11 and §24 |
| TNK-DEV-008 | [Memoization semantics](TNK-DEV-008-memoization.md) | Runtime | Reference §24 and Appendix F/K |
| TNK-DEV-009 | [Diagnostics and invalid-input recovery](TNK-DEV-009-diagnostics-and-recovery.md) | Correctness/UX | Reference §0.5 and Appendix H.3–H.4 |
| TNK-DEV-010 | [Conditional narrowing rules](TNK-DEV-010-conditional-narrowing.md) | Symbolic | Reference §13 and §24 |
| TNK-DEV-011 | [Unsupported unification theories](TNK-DEV-011-unification-theory-gaps.md) | Symbolic | Reference §12 and Appendix K |
| TNK-DEV-012 | [SMT search and result-reporting gaps](TNK-DEV-012-smt-gaps.md) | SMT | Reference §14 and Appendix H/K |
| TNK-DEV-013 | [Ordinary search tracing](TNK-DEV-013-search-tracing.md) | Tooling | Reference §24 |
| TNK-DEV-014 | [Unsupported special hooks and LOOP-MODE](TNK-DEV-014-unsupported-hooks.md) | Hook surface | Reference Appendix G/K |
| TNK-DEV-016 | [Timing measurement](TNK-DEV-016-timing.md) | Presentation/tooling | Reference §24 and Appendix H/K |

## Explicitly not tracked as intended core work

These historical proposals are not open feature issues unless their triggering decision changes:

- an in-engine FILE/SOCKET/PROCESS reactor: superseded by host-owned I/O;
- an OS-process interpreter backend: reconsider only for a concrete sandboxing or per-child resource-isolation requirement;
- the experimental C++ FullCompiler port;
- exact Maude output, warning prose, timing, or inter-message scheduling parity as a blanket compatibility goal.

## Record format

Every issue except the verbatim recovered I-C plan should state:

1. status and issue type;
2. current user-visible behavior, linked to the Reference;
3. the developer-only question or missing implementation;
4. constraints and non-goals;
5. a decision or completion gate;
6. provenance where historical research matters.

Update this index whenever an issue is added, selected, split, or closed. Do not accumulate a second backlog in `TODO.md`, the manual, or release notes.
