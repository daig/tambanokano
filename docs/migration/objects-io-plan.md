# Phase 2.5 — Objects + external IO: implementation plan

> **⚠️ Direction change (2026-06-30): external IO is deferred in favor of EMBEDDING.** Phases A, B, and the
> synchronous STD-STREAM (C-sync, C-stdin) are **done** (objects, `erewrite`, host-mediated stdout/stdin). The
> remaining IO — **C-reactor and all of D (FILE/SOCKET/PROCESS, signals)** — is **not being built in-engine.**
> Per the revised **D5** (`03-open-decisions.md`), the engine stays a pure, instance-based kernel and a **host
> program owns IO** (native Rust file/socket/process/event-loop), embedding the engine for computation. The
> minimal embedding-IO API is **intentionally not designed yet** — to be specified when embedding is taken up.
> The §4-C…E material below is **retained as the shelved in-engine plan** (recoverable if we ever need to run
> arbitrary existing Maude IO `.maude` files unmodified).
>
> **Update (2026-06-30): `omod`/`class`/`subclass`/`msg` (the OO surface language, §4-E) is DONE** — a pure
> frontend desugaring, independent of IO. `omod … endom` (+ `oth`) parses and lowers to CONFIGURATION-based
> Core-Maude (`class` → sort + `subsort < Cid` + constant op + `a :_` attribute ops; `subclass` → subsort;
> `msg` → `[ctor msg]` op); an object module auto-imports the new **built-in `CONFIGURATION`** (injected on
> demand — `tnk-modules/prelude.rs`); and **object-pattern completion** (`ooTransform.cc`, in
> `tnk-frontend/oo_complete.rs`) runs at `load_statements` time — fresh `Atts:AttributeSet` variable per
> object pattern, class-constant → fresh class-sorted variable (subclass polymorphism), plus the
> missing-attribute / subject-only-attribute cases. Byte-conformant: `conformance/objects-omod.maude` +
> `objects-omod-attrs.maude`. (LOOP-MODE, §4-E's other half, remains the next target.)

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

### A — build-layer foundation + `CONFIGURATION` + in-memory object data. *(no reactor, no erewrite)* **DONE.**
- Record the `object`/`config`/`message`/`portal` operator attributes on the symbol (the parser used to discard
  them). **Done:** `Attrs.{config,object,message,portal}` (`surface/ast.rs`); the parser records them with the
  lexer's aliases (`obj`≡`object`, `msg`≡`message`, `config`≡`configuration`); they mirror onto the kernel symbol
  as `Symbol.oo: OoFlags` (`symbol.rs`) via `Engine::set_oo_flags`, wired from `build_sig` Pass B. The flags are
  inert for the current rewriting modes; `OoFlags`'s reader (`#[allow(dead_code)]`) is consumed by Phase B.
- Resolve `ObjectConstructorSymbol` in `build_sig` (`special_op` → `Ok(None)` — `<_:_|_>` is an ordinary free
  symbol; the `attributeSetSymbol` op-hook is ignored until Phase B). **Done.**
- Load `CONFIGURATION` verbatim; `__` stays an ordinary ACU symbol; `getClass` an ordinary equation. **Done.**
- **Conformance:** `conformance/objects.maude` (CONFIGURATION + minimal NAT + bank + ping-pong) under plain
  `rewrite`/`search`, pinned byte-identically (value/order/count/states/bindings, modulo the command echo and the
  `rewrites/second` rate) by `objects_through_repl`. **Done.**

**Three incidental fixes surfaced (all real gaps, fixed in place — not deferred):**
1. **`split_mixfix` now splits on `:`** (`lex.rs`). An attribute op `bal :_` lexes as tokens `[bal][:_]` and
   canonicalizes to `bal:_`; `:` was not a fragment boundary, so the grammar terminal glued to `bal:` and never
   matched a term's standalone `:`. `<_:_|_>` worked only because its `:` sits between holes. Now every
   `:`-bearing mixfix op (attribute ops, `<_:_|_>`) parses. (The main lexer is unchanged — `X:Nat` stays one
   colon-variable token.)
2. **`dag_compare` orders ACU elements arity-first** (`engine.rs`), matching Maude's
   `orderInt = symbolCount | (arity << 24)` (`Interface/symbol.cc`). A configuration soup's arity-2 messages thus
   sort before its arity-3 objects (`ping(p1,p2) < … > < … >`), as the reference does. Side benefit: resolved a
   pre-existing documented cosmetic discrepancy (`x + 5` vs `5 + x`, `nat_renders_like_binary`). Same-arity
   elements keep the prior `SymbolId` order, so NAT/SET/MAP conformance is unchanged.
3. **`set <non-trace>` is a silent no-op** in the REPL (`lib.rs` `meta_set`), so `set show advisories off` (used
   to suppress the reference's "redefining CONFIGURATION" advisory) and `set include …` apply silently — matching
   Maude — instead of printing an "unsupported" notice.

**Two known rendering divergences (cosmetic, abstracted over by the conformance harness — not objects bugs):**
- The **command echo** of an ACU soup: Maude re-renders with the `__` operator's binary nesting parens and its
  echo order; we render the canonical flat form. Results print identically; only the echoed *input* differs (the
  same class as the `join_tokens` echo caveat).
- An **on-the-fly search variable**'s sort qualifier: Maude elides `:Sort` when the goal position determines it
  (`bal : N:Nat` → `N --> …`) but keeps it for a top-level pattern (`=>1 Y:T` → `Y:T --> …`); we always keep it.
  Orthogonal to objects (a search/printing detail). The fixture sidesteps it with a declared variable.

### B — `erewrite` (the object-message-fair driver). *(still no external IO)* **DONE.**
- `Command::ERewrite { bound, gas }` (`surface/ast.rs`) + parser (`erewrite`/`erew`, `[n]` or `[n, g]`) +
  `run_command` arm (`tnk-repl/src/lib.rs`); `Engine::erewrite` + a `Mode::ObjectMessageFair` `Rewriting` session
  (`rewrite.rs`) next to `rewrite`/`frewrite`; the scheduler `Engine::erewrite_pass` + `retrieve_object` +
  `is_config_node` (`engine.rs`). Rules live keyed by their LHS top symbol (`__` for a config rule), so a delivery
  is just `rewrite_at` on the **isolated** two-element `__(object, message)` — the matching rule fires; no separate
  per-message rule index needed.
- **Conformance:** `objects.maude` extended with `msg`-flagged credit/ping/pong + `erewrite` commands;
  `objects_through_repl` pins bank (both credits in one pass → `< a | 50 > < b | 125 >`, count 4), a same-account
  bank (`a` evolves 0→5→12, lone-object `result Object:` collapse), and ping-pong `erewrite [3]` (one delivery per
  pass) — all byte-identical to the reference.

**Two corrections the implementation forced (the earlier un-`msg` probes were misleading):**
- A message symbol is one with the **`msg` attribute** (`OoFlags::message`), not merely one ranged in `Msg`. An
  un-flagged `Msg`-sorted op is **not** scheduled — Maude routes it through the generic `leftOver` path, which
  *looks* like object-message delivery on a simple system but is plain ACU rewriting. All the first probes (no
  `msg`) were exercising `leftOver`, not the scheduler; the real fixtures carry `[ctor msg]`.
- The `[n]` bound counts **delivering passes** (one `ConfigSymbol::ruleRewrite` call), **not** individual
  deliveries. One pass delivers *every* currently-queued message; bank `erewrite [1]` therefore delivers **both**
  credits (count 4). (The per-delivery bound only appears on the `leftOver` path — hence the misleading early
  probe. Ping-pong shows one delivery per pass because each delivery produces the *next* pass's lone message.)

**Residuals (errored-or-inert, documented — mirroring the strategy phase's `xmatchrew`/`csd`):**
- **`leftOver` / multi-object rules** — a rule consuming **two+ objects** (a shared counter, a broker) or an
  un-`msg` message does not fit the `message + single object` fast path; tnk leaves such messages undelivered
  (the soup terminates) rather than porting Maude's generic `leftOverRewrite`. Idiomatic `msg`-flagged,
  single-object-rule systems (the corpus) are byte-exact.
- **Round-robin among multiple rules consuming one message symbol** — our cursor is per-config-symbol, Maude's is
  per-message-symbol; identical while ≤1 rule matches a given message (the corpus).
- **Nested / non-top config** — the scheduler triggers on a `config` *top* node; a config nested inside another
  term falls to the position-fair fallback.

**Pinned model (empirical against the reference + `configSymbol.cc:221`/`run.cc:313`).** Confirmed with bounded
`erewrite [k]` probes on multi-object/multi-message configs:
- **Partition** the config ACU soup by the op's `OoFlags`: `object` ctors, `message` ops, `portal`, else
  `remainder` (`configSymbol.cc:234`). **Key on the flags, not the `Object`/`Msg` sorts.**
- **Object map** = `object-name → (object, message-queue)`. A message's target is its **arg0**; messages whose
  target has no local object stay in `remainder`. The map is iterated in **object-name order** — i.e. our
  `dag_compare` on the names (oid order `a < b`, **independent of soup position** — verified by reversing the
  soup). Each object's queue holds its messages in **`dag_compare` (canonical) order**.
- **Delivery** order: for each object (name order), for each queued message (canonical order), apply the rule
  that consumes that message symbol — **all of object a, then all of object b** (`m(a,1) m(a,2) m(b,3) m(b,4)` →
  that order). One `ConfigSymbol::ruleRewrite` **pass delivers every currently-queued message**; the `[n]` bound
  (default `gas` = 1, `erewrite.cc:56`) counts **delivering passes**, not individual deliveries — see the
  correction below. Within a pass the queues are fixed; a delivery's **newly-produced** messages (e.g. a reply)
  land in `remainder` and are delivered on the **next** pass (`fairTraversal` repeats while progress). The
  object's state updates between its own deliveries (`i->second.object = retrieveObject(...)`).
- **Two rule shapes.** The fast path (`objMsgRewrite:434`) matches `message + single object` and is what
  bank/ping-pong (and most systems) use — `ruleMap[messageSymbol]` is a per-message-symbol `RuleSet` cycled
  **round-robin** (`rs.next`) when >1 rule consumes the same message. A rule that needs **more than one object**
  (a shared counter, a broker) does **not** fit and falls to `leftOver.rules` → generic ACU `leftOverRewrite`.
  *Implementation note:* land the fast path first (covers the conformance corpus); a multi-object rule with no
  fast-path match should error clearly at `erewrite` (the established residual pattern, cf. `xmatchrew`/`csd`),
  **not** silently mis-deliver.
- **Count** is the cumulative `rewrites:` (rule + the equational reductions each delivery triggers — bank credit =
  rule + one `_+_` = 2 rewrites/credit, 4 total). Drive deliveries through the existing rule-application +
  `reduce` machinery so the count co-varies, as with `frewrite`.
- **No portal needed** for internal object-message delivery (`<>` only gates *external* IO in EXTERNAL mode);
  `erewrite` over a portal-less soup still does object-message fair delivery (verified).
- **Conformance:** the same object systems under `erewrite [n]` — solution + per-step order/count vs reference.
  Probe scaffolding in scratchpad (`sched.maude`/`fast.maude`); fold a bank/ping-pong `erewrite` fixture into
  `conformance/objects.maude` (or a sibling) + a REPL test, mirroring `objects_through_repl`.

### C — `STD-STREAM` + the `mio` reactor. *(first external IO)*

**C-sync — synchronous `stdout`/`stderr` `write`→`wrote`. DONE.** No reactor. The framework that the async
part also rides on:
- `SpecialOp::StreamManager { stream, write_msg, wrote_msg, … }` + `StdStream` (`symbol.rs`), resolved from the
  `StreamManagerSymbol` id-hook in `build_sig` (the `stdin`/`stdout`/`stderr` manager constants; the
  `stringSymbol`/`writeMsg`/`wroteMsg` op-hooks). **Note:** the reference *crashes* on a `stdout` op missing the
  `stringSymbol` op-hook — the conformance fixture carries the real op-hook shape.
- The `incomingMessages` reply **mailbox** (`Runtime::incoming`) + captured `external_out`/`external_err`, reset
  per `erewrite` command (`Engine::reset_external`). `erewrite_pass`, when a `<>` portal is in the soup
  (`portal_seen`, the `external` gate): drains buffered replies into each object's queue (`getExternalMessages`),
  and routes a message with no local object whose target is a stream manager to `handle_stream_message`
  (`offerMessageExternally`) — `write(stdout, me, str)` pushes `str` to `external_out` and buffers `wrote(me,
  stdout)`. External handling is **progress but not a rewrite** (so the count is just the user rules). The REPL
  surfaces `external_out` between the echo and `rewrites:`, as Maude interleaves the side-channel writes.
- **Conformance:** `conformance/objects-io.maude` + `objects_io_through_repl` — a one-line `write` (GREET) and
  three sequential writes (TICKER, each awaiting `wrote`), byte-identical to the reference (`hello`, count 2;
  `tick`×3, count 4). `set show advisories off` keeps it comparable.
- *Deferred to C-reactor:* `stderr` is captured (`external_err`) but not yet surfaced by the REPL; GC-rooting the
  in-flight message (REPL GC is off within a command, so the mailbox survives between passes meanwhile).

**C-stdin — `stdin` `getLine`→`gotLine` over a scripted/piped input buffer. DONE.**
- `SpecialOp::StreamManager` gains `string_sym` (the `stringSymbol` op-hook) to build the `gotLine` payload;
  `Runtime::external_in` holds the pending input, `read_line` consumes up to and **including** the next `\n` (the
  reference returns the newline), empty buffer = EOF → `""` (both pinned against the reference). `getLine(stdin,
  me, prompt)` writes `prompt` to stdout, reads a line, and buffers `gotLine(me, stdin, line)` — synchronous over
  the buffer (handled in `handle_stream_message` alongside `write`). The REPL threads the input via
  `Repl::set_stdin` → the running module's engine, returning the unread tail after each `erewrite`.
- **Conformance:** `objects-io.maude`'s ECHO module reads two piped lines and echoes each;
  `objects_io_through_repl` (with `set_stdin("one\ntwo\n")`) is byte-identical to the reference (`one`/`two`,
  count 5). For piped/scripted stdin this is exact — it *is* what Maude does once the bytes are available.

**C-reactor — the `mio` event loop. TODO (folded forward to Phase D, which needs it for sockets/processes).**
- New `engine::io` module: the owned `Reactor` (`mio::Poll` + fd→owner map + timer `BinaryHeap`), the
  `ExternalObject` trait (`do_read`/`do_write`/`do_error`/`do_hung_up`/`do_callback`/`do_child_exit`), and the
  `eventLoop(block)` analog returning the `NOTHING_PENDING|INTERRUPTED|EVENT_HANDLED` discriminant.
- Implement the `interleave`/`externalRewrite` driver (local rewrites priority; block on `reactor.poll()` when dry;
  inject replies on the next config traversal). Needed for *interactive* stdin (a forked reader) and the async
  managers below; the scripted-stdin path above does not require it. **GC-root the in-flight message while an
  object is blocked** (the reactor can span a GC; the synchronous buffer path cannot).
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
