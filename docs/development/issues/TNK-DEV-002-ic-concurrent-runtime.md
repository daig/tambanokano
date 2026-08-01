# 06 — Sessions and meta-interpreters (Phase I-S / I-C; roadmap G5)

**Status: I-S COMPLETE in the working tree (2026-07-24).** I0/D12 and
I-S0–I-S3 are closed. `tnk-session::Session` owns persistent semantic state,
local children, and command evaluation; `tnk-repl` is the thin
color/wrapping/terminal adapter. The selected implementation goal has stopped
at the mandatory I-S boundary. **Phase I-C has not begun and remains a
separate later goal.** The closure commit hash is to be appended when this
working tree is committed.

This split is binding. No cancellation, worker-thread, channel, `newProcess`, or async
adapter work belongs in I-S. I-C may not begin until I-S has a recorded closure commit
with all retained gates green.

---

## 0. Authority, scope, and the serial cursor

Authority, in order:

1. Current code and live harness results.
2. `docs/migration/subsystems-goal.md`, especially §§1–2 and the Phase-I ledger.
3. Decisions D1, D5, D11, and D12 in `docs/migration/03-open-decisions.md`, including
   D12's 2026-07-23 phase-boundary clarification.
4. This implementation plan.
5. Maude 3.5.1 source and the live reference binary for observable local-mode behavior.

`reports/A7-meta-builtins.md` is useful C++ anatomy, but its old `tokio`/`mio` proposal is
superseded by D5/D12. The reactor and FILE/SOCKET/PROCESS material retained in
`objects-io-plan.md` is a shelved design, not Phase-I scope.

The serial cursor is:

```text
I0      D12 concurrency decision                         DONE
  |
  v
I-S0    protocol ledger + frozen local fixture manifest NEXT
  |
  v
I-S1    extract reusable Session; rebuild thin REPL
  |
  v
I-S2    external-message boundary + one real local slice
  |
  v
I-S3    close the supported local protocol
  |
  +---- CLOSE I-S, record the gate, and STOP
  |
  v
I-C1    cooperative cancellation                        LATER GOAL
  |
  v
I-C2    thread-confined child workers
  |
  v
I-C3    deterministic local-vs-thread differential gate
```

A closed I-S is a valid selected-goal completion and a durable shipping boundary even
though the wider subsystem umbrella remains open until I-C. Concurrent coordination is
an adapter over I-S; it is not allowed to become a second implementation of interpreter
semantics.

---

## 1. The two proof authorities

### 1.1 I-S: reference-oracle parity

Local synchronous mode is the semantic implementation. Its authority is the Maude 3.5.1
binary and source:

- message constructors, replies, and lifecycle behavior;
- returned terms, sorts, solution order, and exhaustion;
- per-request rewrite counts;
- module/view insertion, selection, redefinition, and continuation state;
- the external-message next-pass boundary.

`conformance/subsystems/I*.maude` is the durable I-S gate. Every fixture is generated
from a live oracle run; the denominator may grow but may not shrink or weaken without a
recorded user decision.

### 1.2 I-C: differential self-check against closed I-S

Reference Maude does not specify a portable concurrent completion order. I-C therefore
uses the closed local implementation as its semantic authority. Cargo tests drive an
identical request script through:

1. local synchronous children; and
2. thread-confined children under a deterministic test schedule.

They compare request/reply correlation, reply sets, values, sorts, per-request counts,
child state, cancellation outcomes, and failures. Wall-clock timing and natural
inter-message completion order are explicitly not conformance targets.

This separation makes failures attributable: an I-S failure is a semantic/reference
problem; an I-C failure is coordination, cancellation, isolation, or lifecycle.

---

## 2. Bound architectural constraints

### 2.1 Crate and ownership direction

The planned reusable boundary is a dedicated `tnk-session` library crate:

```text
tnk-core
    ^
tnk-frontend / tnk-modules
    ^
tnk-session
    ^
tnk-repl
```

`tnk-session` owns session semantics and depends downward on the existing libraries.
`tnk-repl` owns terminal concerns and may depend on `rustyline`. Neither `tnk-core` nor
`tnk-session` gains a Tokio, `mio`, socket, process, or terminal dependency. An async
runtime adapter, if ever wanted by an embedding host, stays above the core Session API.

A `Session` owns:

- the persistent interner;
- module and view databases and built-module cache;
- dependency invalidation and entry order;
- current-module selection;
- reflection/meta caches;
- command evaluation and typed command operations;
- resumable rewrite/search/variant/narrowing state;
- semantic settings and load/include state;
- local child-interpreter registry once I-S2 begins.

The REPL retains line editing, history, prompts, banners, terminal wrapping/color policy,
and CLI argument handling. Filesystem lookup is host/tool policy: Session owns the
observable load/include state transition, while the REPL supplies the filesystem-backed
source loader. I-S1 must preserve D11 behavior exactly.

### 2.2 Engine/session dependency inversion

Today `Engine::erewrite_pass` recognizes external stream-manager messages inside
`tnk-core` and buffers replies for the next pass. A child interpreter cannot be handled
there because a child is a `Session`; `tnk-core -> tnk-session` would create the forbidden
upward dependency.

I-S2 introduces the smallest external-message pump needed to let the owning Session:

1. observe a manager request after the parent Engine borrow ends;
2. decode it against the parent signature;
3. execute it against a child Session;
4. encode an owned reply in the parent engine; and
5. inject that reply at the existing next-pass boundary.

The exact Rust API is settled by the I-S0 seam spike, but these invariants are binding:

- `tnk-core` never names `Session` or a child registry;
- host/session code cannot re-enter the mutably borrowed parent Engine;
- no external manager means no change to `erewrite` ordering, counts, or hot-path work;
- this is not a generic reactor and adds no OS I/O;
- unknown or out-of-scope managers retain graceful inert behavior.

### 2.3 Cross-engine transport

Every child has a separate Engine, arena, signature, module database, and cache. No
transport/request/reply type may retain a parent or child `DagId`, `SymbolId`, `SortId`,
`RootGuard`, or engine-owned `Rc`. Requests and replies cross through an owned,
engine-neutral meta representation and are down/up-converted at the boundary.

The tests must deliberately create equal numeric handles with different meanings in two
engines. A result that happens to work because both engines allocated the same IDs is a
failure, not a shortcut.

### 2.4 One semantic implementation

Text commands, local interpreter requests, and later threaded requests call the same
typed Session operations. Rendering and protocol encoding are adapters around those
operations. There must not be separate implementations of reduction, search, module
insertion, or continuation behavior for the REPL and the interpreter manager.

---

## 3. Pre-I-S substrate and risk concentration (historical)

At the start of I-S, the required computation already existed: reduction, rewriting,
search, unification, variants, narrowing, SMT, model checking, module/view construction,
reflection up/down, and object-message `erewrite`. The REPL still owned the state that
would become Session: `ModuleDb`, `ViewDb`, built modules, dependency maps, current
module, `MetaState`, load/include state, and every continuation type.

The concentrated implementation risks were therefore not missing algorithms. They were:

1. extracting the large, output-coupled `Repl` without behavior drift;
2. creating the core-to-Session external-message boundary without a dependency cycle or
   reentrant borrow;
3. translating terms/modules across genuinely separate engines;
4. reproducing the broad, stateful manager protocol and its count/cache conventions;
5. preventing I-C scheduling concerns from contaminating the oracle-comparable I-S path.

Before I-S2, `InterpreterManagerSymbol` was recognized but deliberately inert. The
implemented protocol was derived from `interpreterManagerSymbol.cc`,
`interpreterSignature.cc`, `miModule.cc`, `miRewrite.cc`, `miMatch.cc`, `miApply.cc`,
`miSearch.cc`, `miSort.cc`, `miSyntax.cc`, `miUnify.cc`, `miVariant*.cc`, and
`miNarrow*.cc`. `remoteInterpreter*.cc` still documents the backend that D12 excludes.

---

## 4. Phase I-S — synchronous Session and local interpreters

### I-S0 — characterize and freeze before production code

Produce and commit all of the following before I-S1:

1. **Protocol ledger.** One row per request symbol: exact arity and argument meaning,
   reply/error/exhaustion constructors, child state read and changed, reduction-before-
   decode behavior, rewrite-count reset/report boundary, solution-cache behavior,
   deterministic ordering, and the reference source handler.
2. **Fixture manifest.** Enumerate `tests/Meta/metaInt*` and non-`Proc`
   `russianDolls*`, the manual examples, and fresh minimal probes. Freeze applicable
   sources as `I*` fixtures.
3. **Enumerated exclusions.** List every local fixture blocked by a deliberately excluded
   surface such as LOOP-MODE interaction, diagnostics text, or an unclaimed reflection
   operation. `metaProc*` and `*Proc*` remain excluded by D5/D12.
4. **Walking-skeleton fixture.** A minimal live-oracle program that creates a local
   interpreter, inserts a tiny module, reduces one term, receives the exact result/count,
   and deletes the interpreter.
5. **External-seam spike.** Prove the request-yield/reply-injection boundary, borrow
   shape, rooting, and next-pass behavior without implementing protocol breadth. Record
   the chosen API and delete non-production scaffolding.

**I-S0 gate:** the oracle self-diffs the full proposed local manifest; every exclusion is
named; the walking skeleton has frozen output; the external seam requires no upward core
dependency or cross-engine handle.

### I-S1 — Session extraction, no manager behavior

Create `tnk-session` and move the existing state and method bodies mechanically. Keep the
current rendered evaluation path while ownership moves; do not redesign output,
continuations, loaders, or command results in the same change. Rebuild `tnk-repl` as the
thin terminal adapter only after the state move itself is green.

Then expose typed Session operations incrementally as I-S2/I-S3 protocols need them. The
text command and manager adapter must converge on each typed operation before the next
protocol family lands.

**I-S1 gate:** F1–F4 and every U/V/N/T/M scoreboard pass with zero output drift. `tnk-core`
has no new upward or runtime dependency. No cancellation, thread, channel, or
`newProcess` code exists.

### I-S2 — external seam and first real vertical slice

Land the production external-message pump and bind `InterpreterManagerSymbol` only for
the complete walking skeleton:

```text
create local child -> insert module -> select if needed -> reduce -> reply -> delete
```

Use real object messages, real meta up/down conversion, a real child Session, and the
real oracle fixture. No mock child, string-command shortcut, fake transport, or
placeholder request handler is accepted. A manager reply must enter the parent soup on
the same pass boundary and with the same accounting as the oracle.

Add isolation probes with two children defining the same module/operator names
differently and with colliding raw handle numbers.

**I-S2 gate:** the walking skeleton and isolation probes are byte-exact; direct child
Session execution and manager-mediated execution agree on value, sort, state, and count;
all retained gates pass.

### I-S3 — close the supported local protocol

Add one complete protocol family at a time, in this order unless I-S0 source evidence
establishes a dependency:

1. lifecycle and malformed/stale IDs;
2. module/view insertion, selection, and redefinition;
3. single-result reduce/rewrite/frewrite/sort/syntax operations;
4. match/xmatch and apply/xapply;
5. stateful search/path and continuation requests;
6. unification, variant, and narrowing enumerators;
7. SMT-backed requests and exact default-backend degradation where in scope.

For each family: fixture first, decode, one typed Session operation, reply encoding,
direct-vs-manager check, retained gates. A request is either completely implemented or
remains explicitly out of scope and inert; no partial success path lands.

### I-S stopping gate — close and yield before I-C

I-S is complete only when all of these hold on the same tree:

- the frozen `I*` local scoreboard passes against live Maude 3.5.1;
- `metaInterpreter.maude` loads from the repository and all claimed local entry points
  compute;
- direct Session and manager-mediated scripts agree on value, sort, solution order,
  state transitions, and rewrite counts;
- multi-child isolation, deletion, stale-ID, error, GC/root, and continuation probes pass;
- F1–F4, U, V, N, default and optional-z3 T, and M all remain green;
- the status ledger and this plan record the closure commit and exact fixture denominator;
- there is still no cancellation, worker-thread, channel, or async-adapter implementation.

**Mandatory boundary:** stop the selected implementation goal here. Review the closed
synchronous architecture and outputs before opening I-C. A failure discovered during
I-C must reproduce in local mode before any Session semantics are changed; otherwise it
is an I-C coordination bug.

---

## 5. Phase I-C — cancellation and concurrent coordination (later goal)

### Entry gate

I-C may start only from a closed I-S commit. The local mode remains permanently available
and is the executable semantic specification for every concurrent request. I-C may add
coordination adapters but may not fork or duplicate Session operations or protocol
encoders.

### I-C1 — cooperative cancellation

Add a per-request token checked at amortized safe points: reduction loop head, matcher /
solution enumeration, condition evaluation, search, variants, narrowing, and other
long-running loops demonstrated by focused probes. Define explicit queued, running,
completed, cancelled, and failed request outcomes.

Cancellation checks stay outside atomic module/view commits and result publication. A
cancelled continuation is either documented-resumable or deliberately discarded; it
must never be accidentally half-valid. Tests trigger each safe point with deterministic
instrumentation, not sleeps.

**I-C1 gate:** cancellation leaves the Session reusable, does not leak roots or corrupt
counts/state, and ordinary reduce throughput remains within D12's existing ≤2% bar. All
I-S and retained gates stay green.

### I-C2 — thread-confined child workers

Implement D12's `newProcess` compatibility on a thread backend:

- each worker constructs and permanently owns its Session on that thread;
- only owned engine-neutral requests/replies cross channels;
- one child processes its requests serially;
- a Send-capable handle owns channel endpoints and lifecycle state, never the Session;
- delete, shutdown, channel close, abandonment, and worker panic have explicit outcomes;
- the unwinding-panic setting needed for containment is pinned and verified;
- no OS-process, memory-limit, or hard-abort isolation is claimed.

### I-C3 — deterministic differential closure

Drive identical scripts through local and threaded modes under controlled barriers and
rewrite-quantum delivery points. Do not use wall-clock sleeps. Compare replies by request
identity and assert equal result sets, values, sorts, counts, child state, cancellation,
and failure outcomes. Do not assert unspecified natural completion order.

### I-C stopping gate

I-C is complete only when:

- the deterministic local-vs-thread differential suite passes;
- every I-S oracle fixture and retained gate remains green unchanged;
- cancellation and panic-containment probes pass with reusable unaffected Sessions;
- the documented D12 deltas are visible in user-facing/embedding API documentation;
- no executor, reactor, FILE/SOCKET/PROCESS manager, or OS-process backend entered core
  or Session code;
- the status ledger records the closure commit.

Only this gate closes the umbrella Phase I.

---

## 6. Proof matrix

Every claimed protocol family needs focused coverage across the applicable axes:

| Axis | Required cases |
|---|---|
| execution | direct Session; local manager; later thread manager |
| lifecycle | create; use; delete; stale use; recreate |
| isolation | one child; two children; parent/child name and raw-ID collisions |
| outcome | success; no solution; exhaustion; malformed; unsupported |
| state | stateless request; continuation; redefinition/invalidation |
| accounting | value; sort; deterministic order; per-request rewrites |
| memory | collection between request/reply; child teardown with retained parent |
| interruption | before start; at each safe point; after published result |

The full Cartesian product is unnecessary. Isolation, accounting, stateful enumeration,
and cancellation must each be deliberately combined rather than inferred from happy-path
coverage.

---

## 7. Stop conditions and rollback boundaries

Stop the active slice and correct the design if any of these occurs:

- `tnk-core` needs to import or own a Session/child registry;
- a request, reply, or channel payload stores an engine-local ID or root;
- manager handling re-enters the parent Engine while it is borrowed;
- the no-manager `erewrite` path changes order/counts without an oracle fixture;
- local semantics and concurrent coordination change in the same implementation step;
- a second command implementation appears instead of a shared typed Session operation;
- a frozen fixture is weakened or removed to make progress;
- generic reactor, FILE/SOCKET/PROCESS, Tokio, or process-sandbox work appears;
- a thread test depends on sleeps or unspecified completion order.

The I-S/I-C split is also the rollback boundary. I-S must remain useful and shippable if
I-C is postponed or removed. I-C may be reverted without reverting Session extraction or
local meta-interpreter semantics.

---

## 8. Explicit non-goals

- OS-process/remote interpreters and the `metaProc*` fixture family.
- Memory, crash, or per-child resource isolation.
- FILE/SOCKET/PROCESS managers and the shelved in-engine reactor.
- Tokio or another executor in `tnk-core` or `tnk-session`.
- Exact concurrent timing or inter-message completion ordering.
- The general embedding-I/O drain/inject API beyond the minimum synchronous manager seam.
- LOOP-MODE interaction, diagnostics text, Full Maude, and unrelated strategy/meta or
  tool-surface completion unless I-S0 records a specific unavoidable fixture dependency.

---

## 9. I-S0 frozen characterization (2026-07-23)

This section is the source-derived contract consumed by I-S1--I-S3. It is not a
status estimate. The declarations are from repository `metaInterpreter.maude`;
dispatch and behavior are from Maude 3.5.1
`src/Meta/{interpreterManagerSymbol,remoteInterpreter2,mi*}.cc`; cache behavior is
from `src/Meta/metaOpCache.{hh,cc}`. All request messages use argument 0 as target
and argument 1 as requester. Every successful or error reply swaps those two
arguments. The canonical request declarations below are the post-equational forms:
the deprecated short overloads at `metaInterpreter.maude:283-310` reduce to these
before manager dispatch.

### 9.1 Complete local protocol ledger

`payload` lists arguments after the two `Oid`s. `C` means a solution cursor stored
in the addressed module's four-entry `MetaOpCache`; the key is the request symbol
and all arguments except target and the final solution number. A cached cursor is
reused only when its stored index is not greater than the requested index;
otherwise it is discarded and enumeration restarts. Successful and exhausted
enumerations report the cumulative child-context count while transferring only
new work into the enclosing object context. This is byte-visible in I02--I04 and
I10--I17.

| Request | Payload (exact declared types) | Success / exhaustion | State, count, and ordering | Handler | Frozen fixture |
|---|---|---|---|---|---|
| `createInterpreter` | `InterpreterOptionSet` | `createdInterpreter(Oid)` | `none` allocates the lowest free index and registers it; no rewrite count | `interpreterManagerSymbol.cc` | I01--I27 |
| `insertModule` | `Module` | `insertedModule` | replace by header name; compile before commit; replacement cleans dependent module/view and operation caches | `miModule.cc` | I01--I21, I23--I25, I27 |
| `insertView` | `View` | `insertedView` | replace by view name; replacement cleans dependent caches | `miModule.cc` | I06, I08, I09, I19--I21, I23, I25 |
| `showModule` | `Qid Bool` | `showingModule(Module)` | read only; `Bool` selects flattened vs source form | `miModule.cc` | I25 |
| `showView` | `Qid` | `showingView(View)` | read only | `miModule.cc` | I25 |
| `printTerm` | `Qid VariableSet Term PrintOptionSet QidSet` | `printedTerm(QidList)` | temporarily swaps alias/parser state and restores it; no count | `miSyntax.cc` | I07 |
| `printTermToString` | same as `printTerm` | `printedTermToString(String)` | same temporary alias discipline; no count | `miSyntax.cc` | I25 |
| `parseTerm` | `Qid VariableSet QidList Type?` | `parsedTerm(ResultPair?)`; parse failure is `noParse`/ambiguity inside the reply | caches alias-map/parser by module + requester + variable set, deliberately ignoring token list and type | `miSyntax.cc` | I05 |
| `getLesserSorts` | `Qid Type` | `gotLesserSorts(SortSet)` | read only; module lattice order | `miSort.cc` | I11 |
| `getMaximalSorts` | `Qid Kind` | `gotMaximalSorts(SortSet)` | read only; declaration/component order | `miSort.cc` | I11 |
| `getMinimalSorts` | `Qid Kind` | `gotMinimalSorts(SortSet)` | read only; declaration/component order | `miSort.cc` | I11 |
| `compareTypes` | `Qid Type Type` | `comparedTypes(Bool Bool Bool)` | same-kind, first≤second, second≤first | `miSort.cc` | I11 |
| `getKind` | `Qid Type` | `gotKind(Kind)` | read only | `miSort.cc` | I11 |
| `getKinds` | `Qid` | `gotKinds(KindSet)` | read only; user-component order | `miSort.cc` | I11 |
| `getGlbTypes` | `Qid TypeSet` | `gotGlbTypes(TypeSet)` | read only; maximal common subsorts | `miSort.cc` | I11 |
| `getMaximalAritySet` | `Qid Qid TypeList Sort` | `gotMaximalAritySet(TypeListSet)` | read only; operator declaration order | `miSort.cc` | I11 |
| `normalizeTerm` | `Qid Term` | `normalizedTerm(Term Type)` | structural/theory normalization only; no rewrite count | `miSort.cc` | I11 |
| `reduceTerm` | `Qid Term` | `reducedTerm(RewriteCount Term Type)` | fresh child subcontext; full equational reduction; count transferred on reply | `miRewrite.cc` | I06, I08, I09, I22, I24 |
| `rewriteTerm` | `Bound Qid Term` | `rewroteTerm(RewriteCount Term Type)` | resets rule cursors, runs rule-fair order; reference saves no continuation | `miRewrite.cc` | I23 |
| `frewriteTerm` | `Bound Nat Qid Term` | `frewroteTerm(RewriteCount Term Type)` | nonzero limit/gas; resets rules; position-fair order; computes true sort; no continuation | `miRewrite.cc` | I25 |
| `erewriteTerm` | `Bound Nat Qid Term` | `erewroteTerm(RewriteCount Term Type)` | nonzero limit/gas; EXTERNAL object mode; computes true sort; no continuation | `miRewrite.cc` | I18--I21 |
| `srewriteTerm` | `Qid Term Strategy SrewriteOption Nat` | `srewroteTerm(RewriteCount Term Type)` / `noSuchResult(RewriteCount)` | `C`; fair or depth-first strategy order selected by option | `miRewrite.cc` | I12 |
| `getSearchResult` | `Qid Term Term Condition Qid Bound Nat` | `gotSearchResult(RewriteCount Term Type Substitution)` / `noSuchResult(RewriteCount)` | `C`; graph/search order and condition work are cumulative | `miSearch.cc` | I10 |
| `getSearchResultAndPath` | same | `gotSearchResultAndPath(RewriteCount Term Type Substitution Trace)` / same exhaustion | separate `C` because request symbol differs; retained predecessor trace | `miSearch.cc` | I10 |
| `getMatch` | `Qid Term Term Condition Nat` | `gotMatch(RewriteCount Substitution)` / `noSuchResult(RewriteCount)` | `C`; matcher enumeration order | `miMatch.cc` | I02 |
| `getXmatch` | `Qid Term Term Condition Nat Bound Nat` | `gotXmatch(RewriteCount Substitution Context)` / same exhaustion | `C`; depth/extension order; reconstructs one-hole context | `miMatch.cc` | I02 |
| `applyRule` (arity 7) | `Qid Term Qid Substitution Nat` | `appliedRule(RewriteCount Term Type Substitution)` / `noSuchResult(RewriteCount)` | `C`; top-only labelled rule application, result reduction, one rule count | `miApply.cc` | I01 |
| `applyRule` (arity 9) | `Qid Term Qid Substitution Nat Bound Nat` | `appliedRule(RewriteCount Term Type Substitution Context)` / same exhaustion | `C`; position/depth order plus one-hole context | `miApply.cc` | I01 |
| `getUnifier` | `Qid UnificationProblem Qid Nat` | `gotUnifier(Substitution Qid)` / `noSuchResult(Bool)` | `C`; complete flag is `!isIncomplete`; unification carries no rewrite count | `miUnify.cc` | I13 |
| `getDisjointUnifier` | same | `gotDisjointUnifier(Substitution Substitution Qid)` / `noSuchResult(Bool)` | `C`; left/right variable spaces are disjoint | `miUnify.cc` | I13 |
| `getIrredundantUnifier` | same | `gotIrredundantUnifier(Substitution Qid)` / `noSuchResult(Bool)` | `C`; irredundant filter preserves reference order | `miUnify.cc` | I13 |
| `getIrredundantDisjointUnifier` | same | `gotIrredundantDisjointUnifier(Substitution Substitution Qid)` / `noSuchResult(Bool)` | `C`; disjoint + irredundant | `miUnify.cc` | I13 |
| `getVariant` | `Qid Term TermList Bool Qid Nat` | `gotVariant(RewriteCount Term Substitution Qid Parent Bool)` / `noSuchResult(RewriteCount Bool)` | `C`; layer/parent order, family alternation, irredundant flag, completeness | `miVariant.cc` | I14 |
| `getVariantUnifier` | `Qid UnificationProblem TermList Qid VariantOptionSet Nat` | `gotVariantUnifier(RewriteCount Substitution Qid)` / `noSuchResult(RewriteCount Bool)` | `C`; accepts only `delay`/`filter`; variant-unifier order | `miVariantUnify.cc` | I16, I17 |
| `getDisjointVariantUnifier` | same | `gotDisjointVariantUnifier(RewriteCount Substitution Substitution Qid)` / same exhaustion | `C`; disjoint variable spaces | `miVariantUnify.cc` | I16, I17 |
| `getVariantMatcher` | `Qid MatchingProblem TermList Qid VariantOptionSet Nat` | `gotVariantMatcher(RewriteCount Substitution)` / `noSuchResult(RewriteCount Bool)` | `C`; only empty option set; subject reduced before matching | `miVariantMatch.cc` | I15 |
| `getOneStepNarrowing` | `Qid Term TermList Qid VariantOptionSet Nat` | `gotOneStepNarrowing(RewriteCount Term Type Context Qid Substitution Substitution Qid)` / `noSuchResult(RewriteCount Bool)` | `C`; frozen-respecting one-step order; counts a new narrowing step only when advancing, not on cached replay | `miNarrow.cc` | I03 |
| `getNarrowingSearchResult` | `Qid Term Term Qid Bound Qid VariantOptionSet Nat` | `gotNarrowingSearchResult(RewriteCount Term Type Substitution Qid Substitution Qid)` / `noSuchResult(RewriteCount Bool)` | `C`; search/fold/variant order and accumulated substitutions | `miNarrowSearch.cc` | I04 |
| `getNarrowingSearchResultAndPath` | same | `gotNarrowingSearchResultAndPath(RewriteCount Term Type Substitution NarrowingTrace Substitution Qid)` / same exhaustion | separate `C`; forces history retention and returns initial renaming + exact path | `miNarrowSearch.cc` | I04 |
| `quit` | none | `bye` | deletes local child, unregisters its external Oid, destroys DB/caches/continuations; stale target stays inert; index becomes lowest-free candidate | `interpreterManagerSymbol.cc` | I22, I24, I26 |

Exact failure replies are `interpreterError(requester,target,String)`. The handler
strings are:

- lifecycle/dispatch: `Unsupported message.` for an unknown message addressed to
  a live child; malformed create options and stale/non-interpreter targets are
  unhandled and stay in the soup; `interpreterExit` is remote-process-only;
- module lookup: `Bad module name.`, `Nonexistent module.`, or `Bad module.`;
  insertion uses `Bad module.`; views analogously use `Bad view name.`,
  `Nonexistent view.`, and `Bad view.`;
- syntax: `Bad option.`, `Bad concealed set.`, `Bad variable declarations.`,
  `Bad term.`, `Bad token list.`, and `Bad kind.`;
- sort queries: `Bad type.`, `Bad type set.`, `Bad operator name.`,
  `Bad type list.`, `Bad target sort.`, `Nonexistent operator.`, and `Bad term.`;
- rewriting/enumeration: `Bad limit.`, `Bad gas.`, `Bad option.`,
  `Bad solution number.`, `Bad strategy.`, `Bad search.`,
  `Bad matching problem.`, `Bad rule application.`, and `Aborted.`;
- symbolic: `Bad variable family.`, `Bad unification problem.`, `Bad flag.`,
  `Bad reducibility constraint.`, `Bad matching problem.`,
  `Bad narrowing problem.`, and `Bad narrowing search problem.`.

The enclosing configuration is equationally reduced before external delivery.
Handlers then decode in the left-to-right order shown in their source; operations
that create an object context apply the additional reductions stated in the
table. A handled external message itself is not a rule rewrite. Child work is
added to the enclosing context; the requester rules that consume replies remain
ordinary outer rule rewrites. I24 freezes this pass/accounting boundary.

There is no local-manager SMT request constructor in the shipped
`META-INTERPRETER` API. SMT descent is therefore not silently invented for I-S3;
the optional-z3 T gate is retained regression coverage only.

### 9.2 Frozen fixture manifest and exclusions

The proposed local denominator is **27 fixtures**.

- Upstream local reference-suite lifts, all included:
  `metaIntApply`, `metaIntMatch`, `metaIntNewNarrow`,
  `metaIntNewNarrowSearch`, `metaIntParse`, `metaIntPrelude`,
  `metaIntPrint`, `metaIntReplace`, `metaIntReplace2`, `metaIntSearch`,
  `metaIntSort`, `metaIntStrategy`, `metaIntUnify`, `metaIntVariant`,
  `metaIntVariantMatch`, `metaIntVariantUnify`, and
  `metaIntVariantUnify2` are I01--I17.
- The manual's Russian-dolls family is fully represented by
  `russianDollsFlat`, `russianDollsNonFlat`, `russianDollsNonFlat2`, and
  `russianDollsNonFlat3` as I18--I21.
- The additional local reference test `meta-oo-list-2.maude` is I23.
- Fresh live-oracle probes are I22 (create/insert/reduce/quit walking
  skeleton), I24 (bounded next-pass/count boundary), I25 (the four request
  symbols absent from the upstream local corpus), I26
  (unsupported/error/delete/stale/reuse), and I27 (two child databases with
  conflicting definitions under the same module name).

No `metaInt*` or non-`Proc` Russian-dolls source is omitted. The other files in
`tests/Meta` exercise functional META-LEVEL descent and are covered by the
existing F/audit corpus; they do not create a manager child and are not local
manager candidates.

The following **21 remote/process fixtures are explicitly excluded by D5/D12**:
`metaProcApply`, `metaProcMatch`, `metaProcNarrow`,
`metaProcNarrowSearch`, `metaProcParse`, `metaProcPrelude`,
`metaProcPrint`, `metaProcReplace`, `metaProcReplace2`, `metaProcSearch`,
`metaProcSort`, `metaProcStrategy`, `metaProcUnify`, `metaProcVariant`,
`metaProcVariantMatch`, `metaProcVariantUnify`,
`metaProcVariantUnify2`, `russianDollsFlatProc`,
`russianDollsNonFlatProc`, `russianDollsNonFlatProc2`, and
`russianDollsNonFlatProc3`. They request `newProcess` and test
serialization, sockets, process death, or OS isolation, none of which is a
local-mode semantic dependency.

Manual §19.3's MiniMaude execution environment is also not a frozen I-S
fixture: it is a mixed interactive STD-STREAM/tool example assembled across
manual chapters rather than a maintained local-manager source file. Its local
protocol operations are covered componentwise by I05--I09 and I25; its
scripted stream behavior remains in the retained F/objects-I/O gate. The
exclusion is only from the `I*` denominator, not permission to weaken either
component gate. LOOP-MODE, diagnostics wording, Full Maude, and
FILE/SOCKET/PROCESS examples remain the explicit §8 non-goals.

All 27 files self-diff against the live Maude 3.5.1 oracle before I-S1.
`metaInterpreter.maude` is pinned from the same installation and copied into
the repository; its SHA-256 at this freeze is
`9da39cd94099139514bdbf22f633fbb36371568a2d99b944c8f050710c9074c6`.

### 9.3 External-message seam decision

The seam spike and I24 establish the following API shape:

1. `Rewriting` suspends an object-message pass at a manager delivery and
   returns an **opaque token**, never a `DagId`/`SymbolId`/`RootGuard`.
   Scheduler continuation state and GC roots remain private to `tnk-core`.
2. Session reborrows the parent engine only inside a decode closure. The
   closure converts the pending DAG to an owned, engine-neutral request and
   returns it; no engine handle escapes.
3. The parent borrow ends. Session then mutates the selected child Session.
4. Session reborrows the parent only inside an encode/inject closure. The
   owned reply is built in the parent arena and enters the existing incoming
   mailbox. The suspended pass resumes, preserving queue order.
5. Active child Oids are registered internally with the parent object-system
   scheduler. Deletion unregisters before the pass resumes, so later queued
   messages to that stale Oid remain unhandled exactly as in the reference.

The compile-only ownership spike exercised `parent decode -> borrow ends ->
child mutation -> parent encode/inject`; I24 proved that reference replies are
not visible until the next `erewrite` pass and that child counts transfer only
when each request is handled. The production API must preserve this split. A
callback that executes child code while holding `&mut parent Engine`, a public
request carrying engine-local handles, or a generic reactor is rejected.

The integration point is the no-local-object branch of
`Engine::erewrite_pass`; the ordinary no-manager branch remains unchanged.
Pending scheduler state is rooted internally, so a collection between
request and reply is safe without exposing a root to `tnk-session`.

---

## 10. Status ledger

- [x] I0 — D12 recorded (2026-07-05); synchronous/concurrent boundary clarified
  2026-07-23.
- [x] I-S0 — source-derived protocol ledger; 27-fixture manifest and exclusions;
  I22/I24–I27 live-oracle probes; ownership spike compiled; `tools/subsystems-scoreboard.sh -p I`
  with the oracle as `TNK_BIN` reported `SUBSYSTEMS 27/27 PASS` on 2026-07-23.
- [x] I-S1 — `tnk-session::Session` extraction and thin `tnk-repl` adapter
  (2026-07-23): direct host-session test; release suite 439/439; audit 77/77;
  legacy 87/87; U 27/27, V 21/21, N 16/16, optional-z3 T 11/11, M 10/10.
- [x] I-S2 — production external-message suspension/resumption, owned request/reply
  translation, local child registry, walking skeleton, pass-boundary accounting, isolation,
  and GC-safe teardown (working tree 2026-07-24).
- [x] I-S3 — lifecycle/module/view, reduce/rewrite/sort/syntax, match/apply/search,
  unification/variant/narrowing, continuation, and error/exhaustion protocol closure;
  I-S stopping gate closed in the working tree on 2026-07-24.
- [ ] I-C1 — cooperative cancellation.
- [ ] I-C2 — thread-confined workers / `newProcess` compatibility.
- [ ] I-C3 — deterministic local-vs-thread differential closure.

### 10.1 I-S closure evidence (2026-07-24)

All results below were observed on the same final working tree; the commit hash remains
to be appended after commit.

- `cargo test --release --workspace`: **444/444 PASS** across 12 suites.
- `cargo test --release --workspace --no-default-features` in a separate pure-Rust target:
  **444/444 PASS**.
- `tools/audit-scoreboard.sh`: **77/77 PASS**.
- `tools/legacy-sweep.sh`: **87/87 CLEAN**.
- Frozen subsystem gates: **U 27/27, V 21/21, N 16/16, M 10/10, I 27/27 PASS**.
- A separately built `smt-z3` binary selected with `TNK_BIN` passes **T 11/11**. The
  default `tnk-repl` has no z3 linkage (`otool -L` lists only system libraries), loads the
  shipped SMT library, and returns the specified Null-backend `undecided` results.
- Focused live-oracle diffs for I17 manager variant-unifier accounting, V09 direct
  meta-variant accounting, and V03 filtered variant unification are empty.
- The default release loads `term-order.maude`, `machine-int.maude`, `linear.maude`,
  `smt.maude`, `model-checker.maude`, and the repository `metaInterpreter.maude`.
  The latter matches the source installation at SHA-256
  `9da39cd94099139514bdbf22f633fbb36371568a2d99b944c8f050710c9074c6`.
- A source audit finds no cancellation, worker-thread, channel, `newProcess`, Tokio,
  crossbeam, or async/await implementation in `tnk-core`, `tnk-session`, or `tnk-repl`.
  Phase I-C therefore remains unentered.
