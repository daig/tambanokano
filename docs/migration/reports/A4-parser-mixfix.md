# A4 — Frontend: lexer + mixfix parser + grammar (deep-dive report)

## Frontend: lexer + mixfix parser + grammar

### 1. Functional scope
Maude parsing is a **two-level pipeline** (manual §3.9, 1225-1227): (a) a fixed *top-level* surface syntax (modules, views, commands, declarations, keywords) and (b) a *user-definable* per-module mixfix syntax for terms/statements. Features: ASCII identifiers with backquote escaping and special-char splitting (§3.1, 925-933); mixfix operator syntax with `_` argument slots, prefix form, structured/parameterized sort names (§3.4, 1067-1125); **precedence + gather disambiguation** with OBJ3-style defaults (§3.9.1-2, 1269-1304); the **extended signature** (parentheses, `(_)`/`(_).S` sort disambiguation, single-identifier prefix form, flattened assoc lists, BOOL/poly ops) (§3.9.3, 1305-1330); ambiguity detection/reporting (§3.9.4, 1331-1372); the `format` attribute for pretty-printing (§4.4.5, 1746-1844); and **bubbles** — arbitrary token sequences parsed later under the in-module grammar, used for metalanguage syntax (`Token`/`Bubble`/`NeTokenList` via `special (id-hook Bubble (min max) … Exclude(…))`) and LOOP-MODE (§18.3, 10198-10257).

### 2. Architecture in C++
**Outer flex lexer** (`Mixfix/lexer.ll`): a stateful scanner with start-states `INITIAL/ID_MODE/CMD_MODE/BUBBLE_MODE/SEEN_DOT/END_STATEMENT_MODE/FILE_NAME_MODE/STRING_MODE/LATEX_MODE` (`lexer.ll:110-124`). The `maudeId` regex encodes Maude's tokenization incl. backquote escaping (`lexer.ll:101-108`). Keyword sets differ per state. **Bubble collection**: when the bison grammar recognizes the start of a term/statement it calls `lexBubble(terminationSet, minLength)`, switching the lexer to `BUBBLE_MODE`, which squirrels tokens into the global `lexerBubble` until a termination token (`.`-at-EOL, `=`, `=>`, `:=`, `if`, `to`, op-attribute, `]`…) with `parenCount==0` is hit (`lexer.ll:397-508`). A second flex scanner `tokenizer.ll` implements the metalevel `tokenize()` op over a `Rope`.

**Outer bison grammar** (`top.yy`,`bottom.yy`,`modules.yy`,`commands.yy`): a pure (`%define api.pure`) LALR grammar over those keyword tokens whose `%union` carries `Token`/`ModuleExpression*`/etc. (`top.yy:119-277`). It parses module/view/command skeletons and drives the lexer via `lexBubble`/`lexContinueBubble` actions (`modules.yy:155-606`); the collected bubble of `Token`s is handed to the per-module parser.

**Per-module grammar** (`makeGrammar.cc`): `MixfixModule::makeGrammar(complexFlag)` lazily builds a `MixfixParser` from the signature (`makeGrammar.cc:27-92`). NonTerminals are **negative ints**, allocated per connected-component × type (`TERM_TYPE/SORT_TYPE/DOT_SORT_TYPE/ASSOC_LIST_TYPE/SORT_LIST_TYPE/…`) plus on-demand (`makeGrammar.cc:47-66`). `makeComponentProductions` emits the extended-signature machinery — parens, `(_).S`, sort lists, flattened assoc lists, equality/match/search pairs (`makeGrammar.cc:850-1090`). `makeSymbolProductions` turns each operator into productions: prefix form `f ( <t>,… )`, mixfix form (underscores → argument nonterminals) carrying the symbol's `prec`/`gather`, plus special built-in literal productions (float/string/qid/iter/nat) (`makeGrammar.cc:1092-1289`). `makeBubbleProductions` registers bubble specs (`makeGrammar.cc:1683-1703`). **Default prec/gather** follow OBJ3 rules in `computePrecAndGather` (`mixfixModule.cc:1425-1518`) using constants `ANY=127, PREFIX_GATHER=95, UNARY_PREC=15, INFIX_PREC=41` (`mixfixModule.hh:369-377`); gather values `E/e/&` become numeric bounds relative to `prec`.

**The CF parser** (`Parser/`): a standalone **Earley parser with Leo's right-recursion optimization** (Leo 1991), extended for prec/gather and bubbles, *no epsilon productions* (`parser.hh:24-31`). Grammar is compiled once: left-recursion **expansion lists** with prec-closure to fixpoint (`compile2.cc:buildExpansionTables`), and **ternary decision trees** over rhs-head symbols for terminal/nonterminal rules (`compile.cc`). Productions store rhs as `Pair{symbol,prec}` where the per-arg gather bound lives in `prec` (`parser.hh:76-101`, `parser.cc:104-116`). **Pass 1** (`pass1.cc`) builds the Earley item sets via `calls`/`continuations`/`returns` per token position, with prec checks gating completions (`pass1.cc:processReturn`), plus **Deterministic Reduction Path (DRP)** memoization to keep LR(k) grammars linear (`pass1.cc:chaseDeterministicReductionPath`, `drp.cc`). Bubbles are matched imperatively with paren-counting/bounds/excluded-token logic (`bubble.cc:processBubble`). **Pass 2** lazily extracts parse trees from the compact forest, detecting ambiguity by checking for alternative returns (`pass2.cc:extractNextParse`/`extractFirstSubparse`). The wrapper `MixfixParser` maps `Token` codes ↔ terminal indices, attaches a **semantic `Action`** (≈70 cases, `mixfixParser.hh:38-131`) to each production, then walks the tree to build `Term`/statement/command objects (`mixfixParser.cc:725-946 makeTerm`; flattened assoc lists reversed in `makeAssocList`). `doParse.cc` exposes `parseTerm/parseStatement/parse*Command`, reporting "no parse"/"ambiguous"/bad-token (`doParse.cc:36-358`).

**Dispatch patterns**: flex/bison generated state machines; C++ here is mostly *data-oriented* (index-linked `Vector` arenas, tagged unions in `Rule`, int action codes) rather than virtual hierarchies — `Token` is a 2-int handle into a static `StringTable` (`token.hh:34-114`).

### 3. Rust migration
- **flex lexers → RETHINK.** Hand-write a Rust scanner (or `logos`) for `maudeId`, numbers, strings, keywords. The stateful start-states + `lexBubble` coupling is the bad part: replace the lexer↔bison global-variable handshake (`lexerBubble`, `terminationSet`) with an explicit tokenizer that produces a `Vec<Token>` stream and a *bubble-collection* routine driven by the surface parser, returning a `Vec<Token>` slice. Rationale: removes hidden global state and reentrancy hazards.
- **bison surface grammar → RETHINK.** Rewrite as a hand-written recursive-descent / Pratt parser, or use `chumsky`/`winnow`. The surface grammar is small and keyword-driven; the value is clearer error recovery than bison's `error` productions (`top.yy:283-307`). Rationale: no generator, better diagnostics, owns the bubble handoff.
- **Token/StringTable → ADAPT.** Intern strings into a `Symbol`/`Interner` (e.g. `string_interner` or `lasso`); `Token = {code: Spur, line: u32}`. Special/aux properties become a precomputed table or `bitflags`. Backquote/structured-sort splitting are pure functions — PORT.
- **`SymbolType` flags → PORT** as `bitflags!` (`symbolType.hh:95-149`).
- **Grammar construction (`makeGrammar`/`computePrecAndGather`) → PORT (adapted).** Logic is signature-driven and arithmetic; reproduce directly. NonTerminal numbering can stay integer-keyed but wrapped in newtypes (`NtId`, `TermId`).
- **The Earley-Leo CF parser → ADAPT (port the algorithm, redo the data structures).** Port the algorithm (Earley + Leo DRP + prec/gather + bubbles) but replace index-linked `Vector` free-lists and `union{nextRule;equal}` (`parser.hh:88-101`) with idiomatic Rust: `Vec<Rule>` + `enum`/`Option<NonZeroU32>` links, `HashMap` for memo items, arena/index-based parse forest (`Vec<ParseNode>`). Keep integer node IDs (not `Rc`) to avoid cycles. Rationale: the algorithm is sound and performance-critical; the raw pointer/union tricks don't translate.
- **Semantic actions / `makeTerm` → ADAPT.** Replace the `int action` switch with a Rust `enum Action` and a tree-walk returning `Term`. Term construction must coordinate with A1 (Term arena) — return arena indices, not `new`.
- **Does NOT translate:** flex/bison codegen; lexer/parser global mutable state; `Vector` pointer-subtraction-as-index (`compile.cc:133-137`); the `Rule` union; `Token` living in the bison stack union; `Rope`-fed YY_INPUT.

### 4. Hardest parts / risks / open questions
- **Faithfully porting Leo's DRP + prec/gather interaction** (`pass1.cc`,`drp.cc`,`pass2.cc`) — the trickiest, least-documented code; subtle memoization invariants. Needs a differential test harness against C++ Maude on the prelude.
- **Ambiguity semantics**: Maude reports two parses and arbitrarily takes the first (`doParse.cc:62-85`); the *order* of forest extraction is observable behavior to preserve.
- **Lexer/grammar coupling for bubbles**: deciding bubble boundaries needs grammar context (which `terminationSet`); designing a clean Rust API for this without globals is the main architectural decision.
- **Whitespace-sensitive `.`/structured-sort tokenization** edge cases (`lexer.ll:298-311`, 488-499).
- Open: keep integer NT/terminal encoding or move to typed enums? Reuse a crate for Earley (none support prec/gather/Leo) — almost certainly hand-port.

### 5. Proposed Rust module layout
```
frontend/
  lexer/        token.rs (Token, interner, special/aux props, backquote)
                scanner.rs (maudeId/num/string/latex; start-mode logic)
                bubble.rs (bubble collection w/ termination sets)
  surface/      ast.rs (PreModule, View, Command, ModuleExpression)
                parser.rs (recursive-descent surface grammar; error recovery)
  grammar/      symbol_type.rs (bitflags)
                build.rs (per-module grammar from signature; makeComponent/Symbol/Bubble)
                prec_gather.rs (OBJ3 default prec/gather; ANY/PREFIX/UNARY/INFIX consts)
  cfparser/     rule.rs, compile.rs (expansion lists + decision trees)
                earley.rs (pass1: items/calls/returns + Leo DRP memo)
                forest.rs (pass2: lazy parse-tree + ambiguity)
                bubble_match.rs
  build_term.rs (Action enum + parse-tree → Term/Statement/Command; coordinates with kernel arena)
  pretty/       printer.rs (inverse: prec/gather/format-driven; LaTeX/XML later)
```
Integrates with A3 (sorts/components feed grammar build) and A1 (Term arena from `build_term`).
