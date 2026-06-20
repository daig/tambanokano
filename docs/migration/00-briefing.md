# Maude → Rust migration — Stage 1 briefing (shared context for deep-dive agents)

## Mission
Rewrite **Maude** (high-performance rewriting-logic + membership-equational-logic engine &
language) from C++ to **Rust**. This is **Stage 1: understand + plan**. Target = idiomatic,
well-architected Rust with **core feature parity**, NOT identical internals, **NO backward
compatibility**. New project root: `/Users/dai/Downloads/tambanokano` (currently empty).
**ANALYSIS ONLY for now — produce a report, do not write engine code.**

## Sources (both authoritative, for different things)
- **C++ source = ground truth for architecture:** `/Users/dai/code/maude-lang/Maude/src/` (~200k LOC).
  Read the actual code for your subsystem; cite real files as `path:line`.
- **Manual = ground truth for features/semantics:** `/Users/dai/Downloads/Maude-3/book/extracted_manual/manual.md`
  (Maude 3.1). Read the line ranges you're given.
- Prelude/library (the `.maude` files, e.g. `/Users/dai/Downloads/Maude-3/prelude.maude`) show built-in
  modules and the `special (id-hook …)` FFI seam between the library and the engine.

## Confirmed C++ subsystem map (≈ line counts)
- **Core (16k), Interface (5.7k), Variable (1.1k)** — the kernel. `Interface/` = abstract base classes
  (`Symbol`, `Term`, `DagNode`, `LhsAutomaton`, `RhsAutomaton`, `Subproblem`, `Instruction`…) implemented by
  every theory via C++ **virtual dispatch** — the #1 "C++ idiom → Rust" decision. `Core/` = the **Term
  (static parse-time tree) vs DagNode (runtime hash-consed, GC'd DAG)** duality; `RewritingContext`;
  `Substitution`; `Sort`/`ConnectedComponent`/`SortTable`/`sortBdds`; `Equation`/`Rule`/`SortConstraint`(+Tables);
  matching (`lhsAutomaton`/`subproblem*`); unification (`unificationContext`,`pendingUnificationStack`);
  **memory/GC** (`memoryCell`/`memoryBlock`/`memoryInfo`); a **`stackMachine`** compiled-rewriting path;
  `memoTable`.
- **Theories** (each supplies its own Symbol/Term/DagNode + matching & unification automata):
  **FreeTheory (10k)** — free symbols; `freeNet` discrimination net + compiled stack-machine path;
  **ACU_Theory (13k)** — assoc-comm[-unit]; flat `ACU_DagNode` vs red-black `ACU_TreeDagNode`; many
  LhsAutomata; AC unification; **AU_Theory (8k)** assoc[-unit]; **CUI_Theory (3.9k)** comm/unit/idem;
  **S_Theory (2.8k)** successor/`iter` stacked numbers; **NA_Theory (0.8k)** non-algebraic constants.
  `ACU_Persistent`/`AU_Persistent` = persistent data structures.
- **BuiltIn (6.6k)** — C++ ops bound to prelude ops via `special (id-hook …)`: `NumberOpSymbol`,
  `ACU_NumberOpSymbol`, `succSymbol`, `equalitySymbol`, `branchSymbol`, `stringOpSymbol`, `floatOpSymbol`…
  the FFI seam.
- **Mixfix (56k, largest)** — flex lexers (`lexer.ll`,`tokenizer.ll`) + bison grammars
  (`top.yy`,`bottom.yy`,`modules.yy`,`commands.yy`); the user-extensible **per-module mixfix grammar**
  (`makeGrammar`,`mixfixParser`); `MixfixModule`/`VisibleModule`/`preModule`; module database, module
  expressions, renaming, **parameterization & views**; the **interactive interpreter & all commands**
  (`execute`/`erewrite`/`search`/`srewrite`/`match`/`unify`/`getVariants`/`narrowing`); pretty-printing
  (incl. LaTeX/XML); `userLevelRewritingContext`; OO modules (`ooTransform`/`ooSorts`/`ooView`).
- **Parser (2.6k)** — standalone generalized context-free parser (`pass1`/`pass2`, `bubble`, `drp`) used by Mixfix.
- **Higher (12k)** — ops above plain rewriting: search & `stateTransitionGraph`; unification/variant/narrowing
  problems; `modelCheckerSymbol`/`satSolverSymbol`/`temporalSymbol` bridges.
- **StrategyLanguage (6k)** — strategy language (`strategyExpression` subclasses + a process/task interpreter).
- **Meta (18k)** — reflection/meta-level (`metaLevel`,`metaLevelOpSymbol` descent functions,
  `metaModule`(+Cache),`metaView`) + meta-interpreters (`interpreterManagerSymbol`).
- **ObjectSystem (8.7k), IO_Stuff (1.3k)** — configurations/objects; external objects
  (socket/file/process/stream/dir/time managers); `pseudoThread` event loop.
- **SMT (2.2k)** — solver abstraction (`SMT_EngineWrapper`) + concrete cvc4/yices bindings (in Mixfix).
- **Temporal (2.9k)** — on-the-fly LTL→Büchi model checker.
- **FullCompiler (0.9k)** — experimental compiler to standalone code. **Main (0.4k)** — entry point.

## Output contract (every agent uses this)
Concise, structured, **~700–1000 words, NO file dumps**. Cite real files as `path:line`. Base
architecture claims on the actual code; tag genuine gaps `[INFERRED]`.

```
## <Subsystem>
1. Functional scope — features, with manual §refs.
2. Architecture in C++ — key classes/files, data structures, algorithms, control flow; the
   polymorphism/dispatch pattern used.
3. Rust migration — per major piece: PORT (direct) / ADAPT / RETHINK, each with the idiomatic Rust
   approach (ownership/borrowing; enum-dispatch vs trait objects vs generics; arena/GC strategy;
   concrete crates) + one-line rationale. Explicitly call out what does NOT translate (raw-pointer
   DAGs, virtual hierarchies, manual GC, unions, macro tricks, bison/flex).
4. Hardest parts / risks / open questions.
5. Proposed Rust module layout for this subsystem.
```
Return ONLY the report.

## Agent assignments (subsystem → source focus + manual ranges)
- **A1 Kernel & memory** — Term/DagNode duality, hash-consing, arena+mark-sweep GC, RewritingContext,
  Substitution, reduce loop + stackMachine path, sort caching on dagnodes, eval control (strat/memo/frozen,
  S-theory/iter numbers). NOT matching algos (A2), NOT sort lattice math (A3).
  Source: `Interface/{dagNode,term,symbol,instruction,rhsAutomaton}.hh`;
  `Core/{dagNode*,term*,rewritingContext*,substitution.hh,localBinding.hh,memoryCell*,memoryBlock*,memoryInfo.hh,hashConsSet*,dagRoot.hh,stackMachine*,stackMachineRhsCompiler*,eqRewriter*,memoTable*,memoMap*,rhsBuilder*,module.hh}`;
  `Variable/{variableDagNode*,variableTerm*}`. Manual: 551-567, 1626-1642, 1862-2012, 2234-2308, 2430-2492, 10766-11086.
- **A2 Equational theories & matching** — theory-module pattern; match modulo axioms; LhsAutomaton compilation +
  freeNet discrimination net; AC/ACU matching (flat vs tree dag, bipartite+Diophantine, lazy subproblems);
  RhsAutomaton; coherence; per-theory unification *primitives* (features = A8). Deep-read FreeTheory + ACU_Theory,
  generalize. Source: `Interface/{lhsAutomaton,subproblem,rhsAutomaton,extensionInfo,unificationSubproblem,associativeSymbol}.hh`;
  `Core/{subproblem*,extensionMatchSubproblem*,sortCheckSubproblem*,equalitySubproblem*}`;
  `FreeTheory/{freeSymbol*,freeTerm*,freeLhsAutomaton*,freeNet*,freePreNet*,freeNetExec*,freeRemainder*,freeRhsAutomaton*,freeTheory.hh}`;
  `ACU_Theory/{ACU_Symbol*,ACU_DagNode*,ACU_TreeDagNode*,ACU_LhsAutomaton*,ACU_Subproblem*,ACU_LazySubproblem*,ACU_UnificationSubproblem2*,ACU_Theory.hh}`;
  skim `{AU_Theory,CUI_Theory,S_Theory,NA_Theory}/*.hh`. Manual: 1395-1626, 2208-2430, 11086-11348.
- **A3 Order-sorted type system** — sorts, subsort poset, connected-components=kinds (error supersorts),
  op decls/overloading/PREREGULARITY, sort computation (sortTable + sortBdds BDDs), memberships/sortConstraints,
  ctor & ctor-completeness, poly. Source: `Core/{sort*,connectedComponent*,sortTable*,sortBdds*,sortConstraint*,sortConstraintTable*,opDeclaration*,sortCheckSubproblem*}`;
  `Interface/{symbol,symbol2,binarySymbol}.hh`; `Core/module.hh`. Manual: 517-533, 973-1225, 1429-1559, 1642-1746, 2208-2234, 11144-11222.
- **A4 Frontend: lexer + mixfix parser + grammar** — tokens/identifiers/flex lexers; BUBBLES; user-extensible
  per-module grammar; prec/gather/format; the generalized CF parser (Parser/ pass1/pass2 — identify the algorithm)
  & disambiguation; bison grammars; term/statement reading. Expect major RETHINK; propose Rust parsing strategy.
  Source: `Parser/{parser*,pass1.cc,pass2.cc,compile*.cc,bubble.cc,drp.cc}`;
  `Mixfix/{token*,lexer.ll,tokenizer.ll,top.yy,bottom.yy,modules.yy,commands.yy,makeGrammar.cc,mixfixParser*,doParse.cc,symbolType*}`;
  skim `Mixfix/{prettyPrint.cc,termPrint.cc}`. Manual: 925-973, 1225-1375, 1746-1846, 10198-10322, 13101-13155.
- **A5 Module system, parameterization, command interpreter** — module DB & kinds; PreModule→flattened
  VisibleModule; importation modes (protecting/extending/including); module expressions (sum/rename/instantiate);
  PARAMETERIZED PROGRAMMING (theories/views/param modules/instantiation/param views); module & view caches; the
  interactive interpreter, command set, set/show options, REPL. Source:
  `Mixfix/{moduleDatabase*,moduleCache*,preModule*,syntacticPreModule*,visibleModule*,importModule*,importTranslation*,mixfixModule.hh,moduleExpression*,renaming*,renameModule.cc,view*,syntacticView*,viewDatabase*,viewCache*,viewExpression*,parameter.hh,parameterDatabase*,parameterization.cc,instantiate*,interpreter*,command.cc,global*}`;
  `Core/{module*,moduleItem*}`. Manual: 770-915, 935-973, 2879-3765, 4497-5202, 12429-13101.
- **A6 Operational rewriting: rules, rewrite/frewrite, search, strategies, objects, external IO** — rules &
  system modules; rewrite vs frewrite (position/object-message fairness) & schedulers; SEARCH (BFS state space,
  stateTransitionGraph, =>1/=>+/=>*/=>!, such-that, show path); STRATEGY LANGUAGE (+ process/task interpreter,
  dsrewrite); model checking via search (ch11); OBJECT/configuration system & fair object-message rewriting (ch8);
  EXTERNAL objects & IO (ch9: sockets/files/processes/streams, pseudoThread, control-C). Source:
  `Core/{rule*,ruleTable*,rewriteStrategy*,conditionFragment*}`;
  `Higher/{rewriteSequenceSearch*,rewriteSearchState*,searchState*,stateTransitionGraph*,positionState*,matchSearchState*,sequenceSearch.hh,pattern*}`;
  `StrategyLanguage/*`; `ObjectSystem/*`; `IO_Stuff/*`. Manual: 2492-2879, 5202-6069, 6069-7102.
- **A7 Reflection / meta-level / meta-interpreters + built-in data ops** — reflective tower
  (META-TERM/CONDITION/STRATEGY/MODULE/VIEW/LEVEL); up/down maps; DESCENT FUNCTIONS (metaReduce/metaRewrite/
  metaApply/metaXapply/metaMatch/metaSearch/metaUnify/metaGetVariant/metaParse/metaPrettyPrint…) & efficient
  reify/reflect (metaModuleCache, metaOpCache); META-INTERPRETERS (interpreterManagerSymbol); the `special
  (id-hook …)` BuiltIn FFI seam (number/string/float/equality/branch symbols) and how it becomes Rust.
  Source: `Meta/*`; `BuiltIn/{builtIn.hh,bindingMacros.hh,numberOpSymbol*,ACU_NumberOpSymbol*,succSymbol*,equalitySymbol*,branchSymbol*,stringOpSymbol*,floatOpSymbol*,sortTestSymbol*}`.
  Manual: 8681-10120, 10120-10568, 3765-4497. Also skim `/Users/dai/Downloads/Maude-3/prelude.maude` 33-200 and `metaInterpreter.maude`.
- **A8 Symbolic reasoning (unify/variant/narrow), SMT, LTL model checking, Full Maude/OO, FullCompiler** —
  order-sorted unification feature (unify command, theories, combining/hybrid); variants & variant unification
  (folding variant narrowing); narrowing (vu-narrow/fvu-narrow); SMT (bool/int/rational LA, satisfiability,
  variant satisfiability; SMT_EngineWrapper + cvc4/yices); LTL model checking (on-the-fly LTL→Büchi:
  Temporal/ + Higher modelCheckerSymbol); Full Maude & OO modules (what they add; assess what should be Core in
  Rust); FullCompiler (what/keep?). Source:
  `Higher/{unificationProblem*,irredundantUnificationProblem*,variantSearch*,variantFolder*,variantUnificationProblem*,variantMatchingProblem*,filteredVariantUnifierSearch*,narrowingSearchState*,narrowingSequenceSearch*,narrowingFolder*,modelCheckerSymbol*}`;
  `SMT/*`; `Temporal/*`; `FullCompiler/*`;
  `Mixfix/{ooTransform.cc,ooSorts.cc,ooView.cc,unify.cc,getVariants.cc,narrowing.cc,variantUnify.cc,variantMatch.cc,smtSearch.cc,cvc4_Bindings*,yices2_Bindings*}`.
  Manual: 7102-7454, 7454-8583, 8583-8681, 11348-12429.
