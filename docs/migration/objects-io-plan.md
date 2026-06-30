# Phase 2.5 — Objects + external IO: implementation plan

The last Phase-2 subsystem: object-message **configurations**, the object-message-fair **`erewrite`**, and
**external objects** (standard streams / files / sockets / processes), plus Ctrl-C/SIGCHLD. It unblocks the
**prelude tail** (`LEXICAL`/`LOOP-MODE`/`CONFIGURATION`, the lines just past where the META corpus stops) and is
a prerequisite for **Full Maude** (Phase 3.4).

**Status: greenfield.** The Rust codebase has essentially nothing — the parser merely *skips* the
`obj`/`config`/`msg`/`portal` operator attributes (`tnk-frontend/src/surface/parser.rs:1145,1168`); there is no
`CONFIGURATION`, no `erewrite`, no external-object framework. The conformance corpus does not yet include any
object/IO module.

**Oracle / C++ reference.** Source tree: `~/code/maude-lang/Maude/`. **Everything OO/IO is Core-Maude C++** —
there is *no* Full-Maude `.maude` bootstrap; `omod`/`class`/`msg` desugaring is native C++ (added in Maude 3,
the `Mixfix/oo*.cc` family). Prelude modules: `src/Main/prelude.maude` (`CONFIGURATION` 3213, `LOOP-MODE` 3202,
`LEXICAL` 3174). External-object protocol modules: `src/Main/{file,socket,process,time,prng}.maude` (loaded
on demand). Binary oracle: `~/Downloads/Maude-3/maude`.

---

## 1. The model (confirmed against the reference)

A **configuration** is an associative-commutative multiset (`__ : Configuration Configuration -> Configuration
[ctor config assoc comm id: none]`) of **objects** `< Oid : Cid | AttributeSet >`, **messages** `Msg`, and an
optional **portal** `<>`. Rules rewrite object+message fragments. Plain `rewrite`/`search` over a configuration
**already work today** via the existing ACU engine — confirmed:
```
< p1 : Player | turns : 0 >  < p2 : Player | turns : 0 >  ping(p1, p2)
  --rewrite-->  pong(p2, p1)  < p1 : Player | turns : 1 >  < p2 : Player | turns : 0 >
getClass(< a : Account | bal: 0 >)  --reduce-->  Account
```
So the object *data* layer needs only the build-layer plumbing (§4-A); the new runtime is `erewrite`'s scheduler
(§4-C) and the reactor (§4-D).

**External IO is message-driven.** A request message in the soup — e.g. `write(stdout, me, "hi")` — is delivered
to a **manager** (an external object named by a manager constant); the manager does the syscall and injects a
**reply** — `wrote(me, stdout)` — back into the soup. Requests and replies swap arg0/arg1 (`dest`↔`me`) so the
reply lands on the sender.

---

## 2. C++ architecture (the ground truth to port)

### 2.1 The rewriting-context stack + the three modes
`RewritingContext` → `ObjectSystemRewritingContext` → `UserLevelRewritingContext` → `CacheableRewritingContext`
(the concrete one). `ObjectSystem/objectSystemRewritingContext.hh:41`:
```cpp
enum Mode { STANDARD, FAIR, EXTERNAL };
```
| command | driver | engine call | mode |
|---|---|---|---|
| `reduce`   | `execute.cc:244` | `reduce()` (equations only) | — |
| `rewrite [n]`  | `execute.cc:303` | `ruleRewrite(limit)` — top-down leftmost-outermost (`Core/run.cc:24`) | STANDARD |
| `frewrite [n,g]` | `execute.cc:356` | `setObjectMode(FAIR)` + `fairRewrite(limit,gas)` | FAIR |
| **`erewrite [n,g]`** | `Mixfix/erewrite.cc:27` | `setObjectMode(EXTERNAL)` + `fairStart(limit,gas)` + `externalRewrite()` | EXTERNAL |

`erewrite` gas defaults to **1** (`erewrite.cc:56`). FAIR vs EXTERNAL differ only in: EXTERNAL runs the event-loop
interleave driver and enables external-object messaging.

### 2.2 Position fairness (`Core/run.cc`)
`fairRewrite` (`:109`) repeats whole **gas-per-node** depth-first L-to-R traversals while progress is made:
```cpp
do { progress = false; if (fairTraversal()) return; } while (progress);   // run.cc:120
```
Each node gets `gasPerNode` rewrite attempts (`currentGas`, reset per node) before moving on — no runaway redex
can starve the others. We have the analog in our `frewrite` (engine.rs:3203) — confirm it ports cleanly.

### 2.3 Object-message fairness within a configuration — `ConfigSymbol`
The `config`-attributed `__` operator is built as a **`ConfigSymbol : public ACU_Symbol`**
(`ObjectSystem/configSymbol.hh:32`) that **overrides `ruleRewrite`** (`configSymbol.cc:220`). In FAIR/EXTERNAL
mode it bypasses generic AC matching:
1. **Partition** the AC soup by symbol-index into `objectSymbols` / `messageSymbols` / `portalSymbols` NatSets;
   the rest → `remainder` (`configSymbol.cc:234`). (The NatSets are filled at build from the op attribute flags,
   not from the `Object`/`Msg` sorts — see §2.8.)
2. Build a transient **`ObjectMap`** = `map<objectName, MessageQueue{object, list<messages>}>` (`objectMap.cc`),
   pairing each object with the messages addressed to it (**message arg0 = target oid**).
3. Per object, deliver queued messages via `objMsgRewrite` (`configSymbol.cc:433`), selecting rules from
   `ruleMap[messageSymbol]` — rules **hash-indexed by the message symbol they consume** — in **round-robin**
   (`rs.next` cycles). This is both the fairness mechanism and the key performance optimization (no AC search per
   message). Undelivered messages / surviving objects go back to `remainder`.

### 2.4 External gating + the bridge
`configSymbol.cc:279`: `external = portalSeen && (mode == EXTERNAL)`. External IO is enabled **only when a `<>`
portal is in the soup AND erewriting**. Then per object name: `getExternalMessages(name,…)` drains buffered
replies into the soup; a message whose target has no local object is offered via `offerMessageExternally(name,d)`.

### 2.5 The driver loop — `objectSystemRewritingContext.cc`
- `interleave()` (`:114`): `fairTraversal()`; if no progress, break; else non-blocking `eventLoop(false)`; repeat.
  **Local rewrites take priority; poll between bursts.**
- `externalRewrite()` (`:142`): once `interleave` runs dry, **block** on events:
  `blockAndHandleInterrupts(&normalSet)` → `eventLoop(true, &normalSet)` → `EVENT_HANDLED` ⇒ back to `interleave`;
  `NOTHING_PENDING` ⇒ done; `INTERRUPTED` ⇒ `handleInterrupt()`.
This is the **only** place the reactor is entered.

### 2.6 The external-object framework — `ObjectSystem/externalObjectManagerSymbol.{hh,cc}`
A manager **is a Maude `Symbol`** (`ExternalObjectManagerSymbol : public FreeSymbol`, a 0-ary constant — e.g.
`fileManager`, `socketManager`, `stdin`). Interface:
```cpp
virtual bool handleManagerMessage(DagNode* m, ObjectSystemRewritingContext&) = 0;  // msg to the manager constant
virtual bool handleMessage      (DagNode* m, ObjectSystemRewritingContext&) = 0;  // msg to a minted object
virtual void cleanUp(DagNode* objectId) = 0;                                       // free OS resources for one obj
void trivialReply(Symbol* reply, FreeDagNode* orig, ctx);                         // swap arg0/arg1, bufferMessage
```
**Routing** (`objectSystemRewritingContext.cc:89`): if `target` is a registered external object → its manager's
`handleMessage`; else if `target->symbol()` *is* a manager → `handleManagerMessage`.

**Registry + reply mailbox live on the context** (so they die with the command):
- `externalObjects : map<DagNode*, ExternalObjectManagerSymbol*>` — oid→manager (`addExternalObject`/`delete…`).
- `incomingMessages : map<DagNode*, list<DagNode*>>` — the reply mailbox; **`bufferMessage(target,msg)`** pushes,
  **`getExternalMessages(target,…)`** splices into the soup. The context destructor calls `cleanUp` for every live
  object — this is what stops a late callback firing into a freed context.

### 2.7 The reactor — `PseudoThread` (→ the `mio` port; exact contract)
`ObjectSystem/pseudoThread.{hh,cc}` + `pseudoThread-ppoll.cc` + `pseudoThreadSignal.cc`. In C++ **all reactor
state is static/global** (one per process); async managers multiply-inherit `PseudoThread`. `MAX_NR_FDS=1024`,
**one owner per fd**. Client API:
```cpp
void wantTo(int flags, int fd);                  // flags = READ(POLLIN)|WRITE(POLLOUT)
static void clearFlags(int fd);
CallbackHandle requestCallback(const timespec& notBefore, long clientData);   // absolute-time timer
void requestChildExitCallback(pid_t childPid);   // SIGCHLD
```
Callbacks (virtual, per manager): `doRead(fd)` / `doWrite(fd)` / `doError(fd)` / `doHungUp(fd)` /
`doCallback(clientData)` / `doChildExit(pid)`.
`eventLoop(bool block, sigset_t* normalSet)` returns an OR of
`NOTHING_HAPPENED|NOTHING_PENDING|INTERRUPTED|EVENT_HANDLED`. It fires due timers (multimap by absolute
`timespec`), computes the wait to the next timer, then `processFds` → **`ppoll(ufds,nfds,wait,mask)`** (the atomic
signal-mask is how SIGINT/SIGCHLD break the wait) and dispatches each fd's `revents`
(`POLLERR→doError, POLLIN→doRead, POLLHUP→doHungUp, POLLOUT→doWrite`), clearing the serviced flag first.

**The suspend→resume contract** (the part the `mio` port must replicate exactly) — canonical server-accept:
1. `acceptClient(socket(fd),me)`: `accept()` → `EAGAIN` ⇒ set object state `WAITING_TO_ACCEPT`, **stash the
   originating message in a GC root** (`lastReadMessage.setNode(message)`) + `objectContext=&context`,
   `wantTo(READ,fd)`, **return** (the message is consumed from the soup; the object is "blocked").
2. `eventLoop(true)` → `ppoll` POLLIN → `owner->doRead(fd)`.
3. `doRead` retrieves the stashed message+context, does the real `accept()`, `addExternalObject(socket(newFd))` +
   `bufferMessage(me, acceptedClient(...))`, clears the wait bit, releases the GC root.
4. `eventLoop` returns `EVENT_HANDLED` → `externalRewrite` re-runs `interleave` → `ConfigSymbol::ruleRewrite` →
   `getExternalMessages(me)` injects the reply → the object resumes.
**Port note:** the in-flight message must be kept alive against GC while the object is blocked.

Reactor clients: sockets, streams (interactive `getLine` forks a reader, registers the pipe fd), the time manager
(timers), the process manager (child exit). **Files/dir/prng are fully synchronous — they never touch the reactor.**

### 2.8 Signal handling
Two cooperating globals, **no self-pipe**: `ctrlC_Flag` records the event; `traceFlag` forces rewriting onto a
"slow route" so the flag is seen at per-rewrite safe points.
- **SIGINT**: handler (`SA_INTERRUPT`, no auto-restart so `ppoll` breaks) sets `ctrlC_Flag=true; setTraceStatus(true)`
  (`interact.cc:203`). CPU-bound: the trace flag diverts each rewrite to `handleDebug` (single ^C ⇒ `Debug>`
  prompt; `abort` sets `abortFlag`, polled by `traceAbort()`). Blocked-on-IO: `externalRewrite` does
  `blockAndHandleInterrupts` then `handleInterrupt()` (two-^C-or-within-1s ⇒ abort, else continue).
- **SIGCHLD**: lazily-installed `SA_SIGINFO|SA_INTERRUPT` handler is async-signal-safe (just sets
  `c.exited=true; exitedFlag=true`); deferred `dispatchChildRequests` (from `processFds`) does the real `waitpid`
  and buffers an `exited(...)` reply. Registration happens **before** the `waitpid(WNOHANG)` in `waitForExit` to
  avoid a lost-exit race.

### 2.9 LOOP-MODE — `Mixfix/loopSymbol.{hh,cc}`, `loopMode.cc`
`op [_,_,_] : QidList State QidList -> System [ctor special (id-hook LoopSymbol …)]` — the triple is
**[input QidList, internal State, output QidList]**. Input is a **parenthesized bubble** `( raw tokens )`
(grammar `commands.yy`/`modules.yy` `lexBubble`): `injectInput` writes typed tokens into arg0 & clears arg2;
rewrite; `extractOutput` reads arg2; `printBubble` to stdout. Cycle: `( line )` → rewrite → output QidList →
print. Under the `EREWRITE_LOOP_MODE` flag the loop runs in EXTERNAL mode (can talk to `stdin`/`stdout`).
(Marked `DROP`-able in the roadmap, but it's tiny.)

### 2.10 The OO syntax layer — Core-Maude C++ (not Full Maude)
- `SymbolType` flags (`symbolType.hh`): `CONFIG=0x100, OBJECT=0x200, MESSAGE=0x400, PORTAL=0x800`. Lexed from the
  `config/obj/msg/portal` keywords (`lexer.ll:353`), set in the grammar (`modules.yy:891`).
- A `config` ACU op → a `ConfigSymbol` via the factory (`fancySymbols.cc:39`); manager ops similarly. The module's
  `objectSymbols`/`messageSymbols`/`portalSymbols` NatSets are filled at op-entry (`entry.cc:679`) and copied into
  each `ConfigSymbol` (`mixfixModule.cc:353`). **Object-vs-message is the `obj`/`msg` attribute flag, not the sort.**
- `omod`/`class`/`subclass`/`msg` desugaring (all C++, `SyntacticPreModule`, `process.cc:67` + `ooProcess.cc`):
  `class C` → sort `C < Cid` + ctor `op C : -> C`; attribute `a : S` → ctor ``a`:_ : S -> Attribute``;
  `subclass A < B` → subsort; `msg m : S -> Msg` ≡ `op m : S -> Msg [ctor msg]`. Object-pattern completion
  (auto-insert a fresh attribute-set var + missing attrs in rules) is `ooTransform.cc`.

---

## 3. The manager protocols (the contracts to implement; from the `.maude` op-hooks)
`dest`=arg0, `me`/reply-to=arg1. Request → reply:
- **STD-STREAM** (`src/Main/file.maude:116`, portals `stdin`/`stdout`/`stderr`; reactor-async for interactive
  stdin): `write(stdout,me,String)`→`wrote`, `getLine(stdin,me,prompt)`→`gotLine(me,stdin,String)`,
  `cancelGetLine`→`canceledGetLine`, err `streamError`.
- **FILE** (`file.maude:37`; **synchronous, no reactor**; oid `file(Nat)`): `openFile`→`openedFile`,
  `getLine`→`gotLine` (empty=EOF), `getChars`→`gotChars`, `write`→`wrote`, `flush`→`flushed`,
  `getPosition`/`setPosition`→`positionGot`/`positionSet`, `closeFile`→`closedFile`, `removeFile`/`makeLink`,
  err `fileError`.
- **SOCKET** (`socket.maude`; reactor-async; oid `socket(Nat)`): `createClientTcpSocket`/`createServerTcpSocket`
  →`createdSocket`, `acceptClient`→`acceptedClient`, `send`→`sent` (empty string ⇒ `shutdown(SHUT_WR)`),
  `receive`→`received`, `closeSocket`→`closedSocket`, err `socketError`.
- **PROCESS** (`process.maude`; reactor-async via SIGCHLD; oid `process(Nat)`): `createProcess`→`createdProcess`
  (returns `process(pid), socket(io), socket(err)`), `signalProcess`→`signaledProcess`, `waitForExit`→`exited`
  (`normalExit(Nat)`|`terminatedBySignal(String)`), err `processError`.
- **(later)** DIRECTORY (sync), TIME (`requestCallback` timers), PRNG (sync Mersenne-Twister), META-INTERPRETER
  (`InterpreterManagerSymbol` — nested interpreters, ties to D1 / Phase 3.4).

---

## 4. Mapping C++ → `tnk`, in dependency order (each phase = a conformance milestone)

> Architectural divergence from C++: per **D1** (instance-based engine, no globals) the reactor is an **owned
> `Reactor` struct**, not `PseudoThread`'s static state. Per **D5** it's a deterministic single-threaded `mio`
> reactor (`Poll` + fd→manager map + timer heap); managers implement an `ExternalObject` trait (the `doRead`/
> `doWrite`/`doCallback`/`doChildExit` callbacks); Ctrl-C/SIGCHLD via `signal-hook` setting an `AtomicBool` checked
> at safe points (the `ctrlC_Flag`+`traceFlag` analog). `tokio` is **not** adopted (Maude IO is cooperative
> single-threaded; determinism is required for conformance).

### A — build-layer foundation + `CONFIGURATION` + in-memory object data. *(no reactor, no erewrite)*
- Record the `object`/`config`/`message`/`portal` operator attributes on the symbol (today the parser discards
  them: `surface/parser.rs:1145,1168`). Mirror `SymbolType`'s `CONFIG/OBJECT/MESSAGE/PORTAL` flags as symbol attrs.
- Resolve `ObjectConstructorSymbol` (and later the manager `id-hook`s) in `build_sig` alongside the existing
  `MetaLevelOpSymbol` resolution.
- Load `CONFIGURATION` (≈15 lines). The `__` config op stays an ordinary ACU symbol for now; `<_:_|_>` is a free
  symbol; `getClass` is an ordinary equation. **Plain `rewrite`/`search` over configs already work** (verified).
- **Conformance:** bank-account / ping-pong object systems under plain `rewrite`/`search` — value/order/count vs
  the reference (no IO).

### B — `erewrite` (the object-message-fair driver). *(still no external IO)*
- New `Command::ERewrite` (`surface/ast.rs`) + `run_command` arm (`tnk-repl/src/lib.rs:223`); new engine driver
  `engine.erewrite(...)` next to `rewrite`/`frewrite` (`engine.rs:3116/3203`).
- Port the position-fair `fairRewrite` gas-per-node traversal (reuse/extend `frewrite`).
- Port the **`ConfigSymbol` object-message scheduler**: recognize the `config`-tagged top symbol, partition the
  soup (objects/messages/portals/remainder via the symbol attr flags), build the object→message-queue map keyed on
  message arg0, deliver round-robin from rules hash-indexed by the consumed message symbol. This is the substantive
  new engine code.
- **Conformance:** the same object systems under `erewrite [n]` — solution + per-step order/count vs reference.
  *(Probe the reference first: `erewrite` order on a multi-object/multi-message config, bounded with `[n]`.)*

### C — the `mio` reactor + `STD-STREAM`. *(first external IO)*
- New `engine::io` module: the owned `Reactor` (`mio::Poll` + fd→owner map + timer `BinaryHeap`), the
  `ExternalObject` trait (`do_read`/`do_write`/`do_error`/`do_hung_up`/`do_callback`/`do_child_exit`), and the
  `eventLoop(block)` analog returning the `NOTHING_PENDING|INTERRUPTED|EVENT_HANDLED` discriminant.
- Wire the `externalObjects` registry + `incomingMessages` reply mailbox onto the erewrite context, with
  `buffer_message`/`get_external_messages` and the `<>`-portal gating.
- Implement the `interleave`/`externalRewrite` driver (local rewrites priority; block on `reactor.poll()` when dry;
  inject replies on the next config traversal).
- `STD-STREAM`: `stdout` `write`→`wrote` (synchronous), `stdin` `getLine`→`gotLine` (reactor-async). **GC-root the
  in-flight message while an object is blocked.**
- **Conformance:** scripted-stdin / expected-stdout fixtures — this is sequencing, not pure values (see Hazards).

### D — `FILE`, then `SOCKET` / `PROCESS`.
- FILE first — fully synchronous (no reactor), deterministic, easily testable.
- SOCKET / PROCESS — reactor-async + (for processes) SIGCHLD via `signal-hook`. Integration-heavy; lower
  conformance priority.

### E — `LOOP-MODE` + the prelude tail.
- `LoopSymbol` (the `[_,_,_]` triple), the parenthesized-bubble REPL input path, the `injectInput`/`extractOutput`
  cycle. Load `LEXICAL` + `LOOP-MODE`, finally completing the prelude.
- The `omod`/`class`/`subclass`/`msg` desugaring as a frontend `PreModule → PreModule` transform (mirrors the
  parameterization/views layer in `tnk-modules`) — Core-Maude does it in C++, but in `tnk` it's a natural frontend
  pass. (Can land earlier as sugar over hand-written CONFIGURATION modules; not on the critical path.)

---

## 5. Hazards / notes
- **Determinism is mandatory.** The reactor must produce the same event ordering as Maude's `ppoll`-based loop or
  `erewrite` traces diverge. The single-threaded `mio` reactor + fixed dispatch order (`POLLERR,POLLIN,POLLHUP,
  POLLOUT`) is the model.
- **Conformance for IO is about sequencing, not byte-values.** The differential discipline weakens here — need
  scripted-stdin/expected-stdout fixtures, not just `result:` comparison. The wrap-robust harness
  (`conformance/strat_diff.py`) still applies to any term output.
- **GC-root in-flight messages.** A message consumed from the soup while its object blocks on IO must be kept alive
  against GC until the reply is buffered (C++ uses `DagRoot lastReadMessage`). Our `RootGuard` discipline (D2)
  covers this — thread it through the manager-suspend path.
- **No global reactor.** Unlike C++ `PseudoThread` (static state), per D1 the reactor is owned (by the Engine or
  the erewrite context). This is cleaner but means the context↔reactor wiring is explicit.
- **`erewrite` fairness exactness.** The gas-per-node × round-robin-message scheduling determines step order and
  counts. Pin it empirically against the reference (bounded `erewrite [n]`) before trusting the port.
- **Object-vs-message is an attribute flag, not a sort.** Don't key partitioning on the `Object`/`Msg` sorts —
  key on the `obj`/`msg`/`config`/`portal` op attributes (mirror `entry.cc`/`mixfixModule.cc`).
- **`SIGPIPE` ignored; `SA_INTERRUPT` (not `SA_RESTART`)** on SIGINT/SIGCHLD so the poll wakes — replicate via the
  `signal-hook` config.

## 6. Integration points in `tnk`
- `surface/ast.rs` — `Command::ERewrite` (+ the `omod`/`class`/`msg` surface, later).
- `tnk-repl/src/lib.rs:223` — `run_command` dispatch arm.
- `tnk-core/src/engine.rs:3116/3203` — `erewrite` driver next to `rewrite`/`frewrite`; a new `engine::io` reactor
  module; the config-aware object-message scheduler.
- `tnk-frontend/src/sig/build_sig.rs` — resolve the object/IO `id-hook` symbols + record the new op attributes.
- `tnk-modules/` — the `omod`/`class` desugaring transform (frontend, Phase E).

## 7. First moves for the next session
1. Probe the reference's **`erewrite` order/count** on a no-IO multi-object/multi-message config, bounded with
   `[n]`, to pin the object-message fairness empirically (complements the C++ `configSymbol.cc` reading).
2. Probe a scripted **`STD-STREAM`** round-trip (`echo line | maude file.maude` with a loop/getLine module) to see
   the exact message/reply sequencing.
3. Start Phase A — it's pure build-layer plumbing over an already-working ACU engine and unblocks the object data
   layer with no new runtime.

## References
C++ source `~/code/maude-lang/Maude/src/`: drivers `Mixfix/{erewrite,execute,loopMode}.cc`, `Core/run.cc`,
`ObjectSystem/{objectSystemRewritingContext,configSymbol,objectMap,pseudoThread,pseudoThreadSignal}.{hh,cc}`,
`pseudoThread-ppoll.cc`; framework `ObjectSystem/externalObjectManagerSymbol.{hh,cc}` + each
`*ManagerSymbol.{hh,cc}` (+ `*Actions/*Stuff/*Async/*Outcomes/*Signature.cc`); signals/REPL
`Mixfix/{interact,loopSymbol}.cc`; syntax `Mixfix/{lexer.ll,modules.yy,process.cc,ooProcess.cc,fancySymbols.cc}`;
prelude `src/Main/prelude.maude` (CONFIGURATION/LOOP-MODE) + `src/Main/{file,socket,process}.maude` (protocols).
Decision: `03-open-decisions.md` §D5. Roadmap: `roadmap.md` Phase 2 item 5.
