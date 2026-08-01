# Recommendation

Build **The TNK Book** as a guided journey through TNK’s conceptual stack, not as the Reference rewritten in friendlier prose.

The current manual is already strongly reference-shaped:

- stable `TNK-*` contract identifiers;
- mathematical and behavioral definitions;
- complete command and grammar material;
- explicit feature classifications in §23;
- unsupported and incomplete boundaries;
- Session, CLI, and Rust API contracts;
- normative worked examples;
- appendices for commands, grammar, attributes, hooks, diagnostics, APIs, profiles, and clause indexing.

The Book should therefore be organized **horizontally around workflows and understanding**, while the manual is organized **vertically around features and contracts**.

```text
source text
    ↓
module environment
    ↓
canonical data and equational computation
    ↓
rules and transition systems
    ↓
control, search, and symbolic analysis
    ↓
verification
    ↓
host-owned Session and Rust integration
```

That sequence should be the Book’s spine.

## Division of responsibility

| Manual owns | Book owns |
|---|---|
| Exact semantics | Mental models |
| Complete syntax and grammar | Progressive introduction to syntax |
| Feature status and profiles | Advice about when to use a feature |
| Error and state-transition contracts | Debugging workflows |
| Completeness and resource boundaries | Intuition for why analyses terminate or diverge |
| Exact command catalogue | Common command flows |
| API contracts | Host-application design |
| Stable and unspecified ordering | How to consume results safely |
| Minimal normative examples | Extended projects and exercises |
| Unsupported-feature inventory | Practical warnings and alternatives |

Material may appear in both, but with different roles. For example:

- The manual defines $t \rightarrow^*_{E/A} u$.
- The Book explains why equations are used to canonicalize data before rules model change.
- The manual defines breadth-first search and depth accounting.
- The Book walks through a graph, demonstrates a bounded search, resumes it, and explains what was and was not proved.
- The manual defines `Session` state transitions.
- The Book builds a small Rust host that responds correctly to success, diagnostics, and continuations.

The Book may summarize a contract, but it should cite the applicable `TNK-*` identifier. It must never become the only place where a semantic fact is stated.

---

# Front matter

## Preface: What this book is

State prominently:

> The TNK Book is an explanatory, tutorial work. It is not normative. The TNK Language and System Reference defines TNK behavior.

Record:

- Book edition.
- Target Reference edition: currently `2026-07-29`.
- Target workspace version: currently `0.1.0`.
- Links to the Reference and its normative clause index.
- How feature-status badges work.
- How runnable examples are represented.
- Assumed installation and platform prerequisites.
- Whether a chapter uses the default profile, `smt-z3`, or loaded hook libraries.

Do not reuse RFC-style **MUST** and **SHOULD** as editorial emphasis. When exact requirements matter, quote or summarize the corresponding Reference clause and link it.

## How to read the book

Borrow the useful part of the Maude book’s approach: offer reading paths. Unlike the Maude book, keep one common spine so that the text remains readable cover to cover.

Suggested paths:

- **First-time TNK user:** Parts I–IV, then Parts VII.
- **Model author:** Parts I–IV, Chapters 20–22.
- **Verification user:** Parts I–V, then Chapters 20–22.
- **Rust embedder:** Parts I–III, then Part VI and Chapters 20–21.
- **Advanced language user:** Entire book.
- **Maude user:** Chapters 1–2, then the separate migration guide before continuing. Do not create a second Maude-centric edition of the Book.

## Example conventions

Explain:

- self-contained examples versus prelude-dependent examples;
- default versus optional profiles;
- Stable versus Experimental feature badges;
- which portions of transcript output are illustrative;
- how to find complete source files;
- how to run each example.

Most core examples should run with `--no-prelude`. This makes their dependencies explicit and reinforces `TNK-DOC-004`. Chapters specifically teaching bundled libraries should load them deliberately.

---

# Part I — A working mental model

The goal is a successful complete model before introducing the full language taxonomy.

## Chapter 1 — Rewriting as a way to describe computation

Introduce:

- terms as structured data;
- equations as canonical computation;
- rules as possible change;
- search as exploration rather than execution;
- strategies as control;
- verification as reasoning over the transition system.

Use one tiny example to show all three questions:

1. What is this value after normalization?
2. What can this state become?
3. Can a target state be reached?

Do not begin with DAGs, parse forests, matching algorithms, or module flattening. Those explain implementation and edge behavior, not the first mental model.

**Reference map:** `TNK-TERM-*`, `TNK-REDUCE-*`, `TNK-RULE-001`, `TNK-SEARCH-*`.

## Chapter 2 — Your first TNK session

Teach:

- invoking the REPL;
- loading a file;
- entering a complete module;
- selecting and inspecting the current module;
- `reduce`, `rewrite`, and `search`;
- quitting;
- the distinction between REPL policy and Session semantics;
- the absence of an implicit library prelude below the executable adapter.

Show the anatomy of a transcript, but avoid teaching incidental banner wording, whitespace, or rewrite totals as semantic results.

Include a short “What the output means” section:

- command echo;
- rewrite diagnostic;
- mathematical result;
- completion or continuation state;
- human-oriented diagnostics.

**Reference map:** `TNK-DOC-004`, `TNK-CMD-*`, `TNK-SESSION-*`, `TNK-OUT-*`, `TNK-CLI-001`.

## Lab A — A complete tiny model

Build one small model from an empty file:

- declare a sort;
- add constructors;
- define an equation;
- define a rule;
- reduce a term;
- rewrite a state;
- search for a state.

The reader should finish Part I able to write and run a complete, self-contained TNK file without understanding every edge case.

---

# Part II — Data and equational computation

## Chapter 3 — Signatures, terms, and syntax

Teach together:

- sorts and operator signatures;
- constants and applications;
- variables;
- prefix and mixfix notation;
- precedence, grouping, and disambiguation;
- literals and token boundaries;
- sort-qualified terms.

Use parsing failures as exercises, but explain the intended source form rather than exhaustively documenting the grammar.

Avoid reproducing Appendix D or E. Link there for:

- token boundaries;
- complete module grammar;
- gather details;
- ambiguous command-bubble rules.

**Reference map:** `TNK-SORT-*`, `TNK-LEX-*`, `TNK-PARSE-*`.

## Chapter 4 — Equations compute canonical values

Teach:

- left-to-right reading of an equation;
- variables and substitution;
- repeated reduction;
- normal forms;
- declaration priority;
- equation strategy;
- why equations are distinct from rules;
- why aggregate rewrite counts do not define the value.

Use a small expression evaluator or arithmetic datatype. First define it incorrectly, observe the stuck term, then complete the equations.

Include design advice:

- orient equations toward simpler or more canonical forms;
- keep semantic computation in equations;
- avoid equations whose intended execution obviously cycles;
- do not inspect rewrite totals as correctness evidence.

**Reference map:** `TNK-REDUCE-*`, `TNK-CMD-REDUCE-001`.

## Chapter 5 — Subsorts, memberships, and partial operations

Develop the type model gradually:

- subsort declarations;
- kinds and error sorts;
- overloaded operators;
- least sorts;
- memberships as sort refinement;
- partial operators;
- sort tests in conditions.

The reader should understand that kinds keep otherwise ill-sorted applications representable, but do not make them valid values of every user sort.

Use a partial operation such as predecessor, map lookup, or division to distinguish:

- successful reduction;
- a kind-sorted stuck term;
- membership-refined output;
- invalid declaration.

**Reference map:** `TNK-SORT-001`–`006`, `TNK-MB-*`.

## Chapter 6 — Conditions and backtracking

Teach the condition forms through examples:

- equality;
- sort test;
- matching assignment;
- rewrite condition;
- Boolean abbreviation.

Explain:

- left-to-right binding;
- newly introduced variables;
- short-circuiting;
- backtracking to the nearest multi-solution fragment;
- why conditional execution can diverge.

This chapter should teach how to design conditions, not reproduce the condition grammar table.

**Reference map:** `TNK-COND-*`, `TNK-STMT-001`.

## Chapter 7 — Computing modulo algebraic laws

Introduce one law at a time:

- associativity;
- identity;
- commutativity;
- idempotence;
- iteration.

Use concrete data interpretations:

- lists or words for associativity;
- bags for AC;
- sets for AC plus idempotence;
- repeated unary constructors for iteration.

Then explain:

- canonicalization versus user equations;
- whole matching versus extension matching;
- why AC result order is not mathematical;
- why a set of matches should be compared as a set;
- supported and unsupported combinations.

Do not explain the internal matching or Diophantine algorithms unless placed in an optional implementation note.

**Reference map:** `TNK-TERM-001`–`005`, `TNK-MATCH-*`.

## Lab B — A typed expression language

A suitable project:

- multiple value sorts;
- overloaded operators;
- conditional equations;
- a partial operation;
- one associative or AC data structure;
- matching queries.

This project can later be parameterized in Part IV.

---

# Part III — Systems, search, and control

## Chapter 8 — Rules describe change

Move from values to states:

- canonical states;
- rules as transitions;
- labels;
- conditions;
- equation normalization around rule applications;
- rule normal form versus equation normal form;
- `[nonexec]` as specification material.

Use a state-machine example where several transitions are possible. Explicitly contrast:

```text
equations: different presentations of the same semantic state
rules:     different possible future states
```

This distinction should become the central modeling discipline of the Book.

**Reference map:** `TNK-RULE-001`, `TNK-SEM-001`.

## Chapter 9 — Rewriting modes and continuations

Explain behaviorally:

- rule-fair rewriting;
- position-fair rewriting;
- bounds;
- gas;
- canonical versus bounded intermediate results;
- continuations;
- cumulative operation state;
- continuation invalidation.

Use side-by-side runs of `rewrite` and `frewrite` to explain why they answer different operational questions.

Treat `erewrite` as an advanced preview, since the feature matrix classifies external/object rewriting as Experimental.

**Reference map:** `TNK-REWRITE-*`, `TNK-CONT-001`, `TNK-CMD-001`.

## Chapter 10 — Search is graph exploration

This should be one of the Book’s central chapters.

Teach:

- canonical search states;
- successor generation;
- breadth-first exploration;
- `=>1`, `=>+`, `=>*`, and `=>!`;
- result and depth bounds;
- duplicate-state elimination;
- solution order versus same-depth tie order;
- continuation;
- graph and path inspection;
- finite failure versus a bounded prefix.

Use diagrams to draw the actual graph before showing TNK output.

A key exercise should deliberately contrast:

```text
search [1] initial =>* goal .
```

with proof that no goal exists. Reaching the first-result bound is not exhaustion.

**Reference map:** `TNK-SEARCH-*`, `TNK-CMD-001`, `TNK-CMD-002`.

## Chapter 11 — Strategies as programmable control

Develop strategies incrementally:

- `idle`, `fail`, and `all`;
- sequence and choice;
- iteration;
- branching;
- top and one;
- label application;
- named `sd` definitions;
- fair versus depth-first strategy scheduling;
- match and match-rewrite forms.

Explain strategies as control over an existing rewrite relation, not as a second equation language.

Keep unsupported `xmatchrew` and `csd` out of the main progression. Mention them only in a status callout.

**Reference map:** `TNK-STRAT-*`.

## Lab C — Find and repair a protocol bug

Use a finite protocol, workflow, or resource allocator:

1. define canonical data equationally;
2. define transitions with rules;
3. discover a bad state with search;
4. inspect the path;
5. repair the model;
6. use a strategy to explore or execute a controlled policy.

This is more valuable than a collection of unrelated puzzles because later verification chapters can revisit the same transition system.

---

# Part IV — Composing larger models

## Chapter 12 — Modules, imports, and renaming

Teach:

- separating signatures and behavior;
- import modes as source declarations;
- flattening as the construction of one executable environment;
- diamond imports;
- sums;
- structural renaming;
- current module and redefinition effects.

Do not imply that `protecting`, `extending`, and `including` currently enforce different mathematical obligations. The Book should show their present status and link `TNK-MOD-003`.

**Reference map:** `TNK-MOD-002`, `003`, `005`, `006`, `007`.

## Chapter 13 — Theories, views, and parameters

Introduce generic modeling through a concrete need:

1. define an interface theory;
2. write a parameterized module;
3. define a target module;
4. create a view;
5. instantiate;
6. inspect the resulting behavior.

Explain structured sorts and parameter-prefixed sorts only as they arise.

This chapter needs a prominent **Experimental boundaries** box because full view validation and some parameter cases are Experimental. Teach the supported pattern clearly without making broader promises.

**Reference map:** `TNK-MOD-004`, `TNK-VIEW-001`.

## Lab D — A reusable generic component

Extend the Part II expression or collection project into a parameterized library. Include:

- one identity view;
- one renamed instance;
- a deliberate invalid view;
- a dependent module rebuild.

The invalid example should assert the diagnostic category and preserved state, not exact prose.

---

# Part V — Symbolic reasoning and verification

These chapters should carry visible status/profile badges. They should not be prerequisites for ordinary modeling.

## Chapter 14 — From matching to unification

Start by comparing:

- matching: solve variables on one side against a subject;
- unification: solve variables on both sides;
- order-sorted constraints;
- simultaneous problems;
- complete versus irredundant sets;
- fresh-variable spelling versus mathematical result.

Use small free, commutative, and AC examples. Teach readers to validate solution sets semantically rather than relying on enumeration order.

Explain unsupported theory combinations and the low-level incompleteness signal.

**Status:** Stable over the documented theory domain.  
**Reference map:** `TNK-UNIFY-*`.

## Chapter 15 — Variants and narrowing

Develop the motivation first:

- equations normalize concrete terms;
- variants describe normalized symbolic instances;
- narrowing combines unification and rewriting;
- folding avoids retaining subsumed states.

Then cover:

- variants;
- irreducibility blockers;
- variant unification and matching;
- narrowing strategies and bounds;
- returned solutions versus completeness.

This should be a clearly marked **Experimental** chapter. Never describe one observed enumeration as canonical.

**Reference map:** `TNK-VARIANT-*`, `TNK-NARROW-*`.

## Chapter 16 — Constraints and SMT

Teach the three distinct outcomes before examples:

- satisfiable;
- unsatisfiable;
- unknown.

Show:

- behavior under the default null backend;
- enabling the `smt-z3` profile;
- formula construction through loaded hooks;
- constrained search;
- why `Unknown` is not failure or unsatisfiability;
- unsupported `=>!`.

All examples must state their profile and loaded-library requirements.

**Status:** null backend Stable; Z3 Optional.  
**Reference map:** `TNK-PROFILE-001`, `TNK-SMT-*`.

## Chapter 17 — Invariants and temporal properties

Build from ordinary search:

- safety properties as absence of bad reachable states;
- transition-system paths;
- deadlocks;
- LTL propositions;
- lasso counterexamples;
- finite-state requirements;
- satisfiability versus model checking.

Use the protocol from Lab C so that verification answers a previously motivated question.

Teach semantic counterexamples, not automaton dumps or internal state numbering.

**Status:** Optional, requiring loaded hooks.  
**Reference map:** `TNK-LTL-*`.

## Lab E — A complete verification argument

For the running protocol:

1. state the property in prose;
2. identify the canonical state space;
3. search for a simple invariant violation;
4. formulate an LTL property;
5. inspect a counterexample;
6. change the system;
7. rerun the argument;
8. state what was proved and under what finiteness/profile assumptions.

This lab should model good scientific reporting: outcome, bounds, completeness, backend, and assumptions.

---

# Part VI — Hosting and extending TNK

This is the principal TNK-specific addition relative to the old Maude book.

## Chapter 18 — A Session is a state machine

Explain:

- host-owned state;
- submission boundaries;
- incomplete versus malformed input;
- current module;
- module/view persistence;
- loading;
- continuations;
- diagnostics and recovery;
- scripted input;
- exit as returned data rather than process termination.

Use a state-transition diagram. Keep semantic result, Session state change, rendered text, and terminal behavior distinct throughout.

**Reference map:** `TNK-SESSION-*`, `TNK-LOAD-*`, `TNK-OUT-*`.

## Chapter 19 — Embedding TNK in Rust

Build a small host application:

- create a `Session`;
- submit definitions and commands;
- inspect `Eval`;
- preserve the Session;
- handle diagnostics;
- resume a bounded operation;
- provide input;
- respond to `exit`.

Then explain when to use:

- `tnk-session`;
- frontend/module APIs;
- the low-level kernel.

Cover engine-relative handles and rooting conceptually, but send exact ownership and lifetime rules to Rustdoc and the Reference.

**Status:** semantic Session behavior as classified by the manual; Rust source compatibility Experimental.  
**Reference map:** `TNK-API-*`, `TNK-RUNTIME-*`.

## Chapter 20 — Reflection, objects, and external systems

Treat this as an advanced preview:

- terms and modules as data;
- descent operations;
- object-module notation;
- configuration rewriting;
- external managers;
- local interpreter isolation;
- loaded hooks as runtime capabilities.

Do not build the Book’s core examples on these surfaces while they remain Experimental. Show one coherent extension workflow and identify every capability prerequisite.

**Reference map:** `TNK-BUILTIN-001`, `TNK-META-*`, `TNK-OO-001`.

---

# Part VII — Engineering reliable TNK models

## Chapter 21 — Diagnostics, tracing, and debugging

Teach a repeatable debugging workflow:

1. classify the failure boundary;
2. reduce suspicious subterms;
3. inspect sorts;
4. isolate matching;
5. inspect rule labels and paths;
6. enable focused tracing;
7. minimize the module;
8. distinguish a stuck term from rejected or unsupported behavior.

Explain why diagnostic category and state effect matter more than prose.

Do not reproduce every output record or setting. Link the relevant manual tables.

## Chapter 22 — Termination, completeness, and resource bounds

This chapter should unify several cautions otherwise scattered across features:

- equation nontermination;
- recursive conditions;
- infinite rewriting;
- infinite search graphs;
- strategy iteration;
- infinite or incomplete symbolic families;
- parser effort limits;
- user bounds;
- backend `Unknown`;
- unsupported theory;
- resource exhaustion;
- external interruption.

Give readers a vocabulary for reporting results:

> “No solution in the explored depth-five prefix” is not “no solution exists.”

Similarly:

> “Every returned unifier is sound, but the problem reported incompleteness” is not a complete unification result.

**Reference map:** `TNK-RESOURCE-*`, `TNK-CMD-001`, `TNK-UNIFY-004`.

## Chapter 23 — Testing and evolving TNK models

Teach tests from a model author’s perspective:

- normal-form examples;
- algebraic laws;
- matching and unification soundness;
- reachability invariants;
- bounded versus exhaustive checks;
- expected counterexamples;
- host-state transitions;
- avoiding assertions on incidental counts, order, and prose;
- recording feature profile and loaded capabilities.

This reinforces the project’s broader regression philosophy without turning the Book into an implementation-testing manual.

## Capstone — From model to hosted analysis tool

Finish by combining the running project:

- equational data definitions;
- transition rules;
- module composition;
- search and verification;
- a controlled strategy;
- a small Rust host;
- explicit handling of bounds and completion;
- a short report explaining exactly what was established.

The reader should finish with one substantial, runnable artifact—not merely isolated syntax fragments.

---

# Example strategy

Use three levels of examples.

## 1. Microexamples

Five to fifteen lines, showing one concept:

- overloaded operator;
- membership lowering;
- AC matching;
- one search arrow;
- one unification family.

These support explanations but should not dominate the Book.

## 2. One primary running system

Use a domain rich enough to support:

- canonical data;
- multiple rules;
- concurrency or nondeterminism;
- a reachable bug;
- a finite verification instance;
- strategies;
- hosting.

A work queue, message-delivery protocol, resource allocator, or bounded workflow would work. Prefer a system whose state can first be modeled with Stable core features. Object notation can be shown later as an Experimental alternative.

## 3. Specialist labs

Use separate examples when forcing a feature into the running system would be artificial:

- algebraic unification;
- variants and narrowing;
- arithmetic SMT;
- reflection.

One coherent spine plus specialist labs is better than either extreme:

- dozens of unrelated puzzles;
- one contrived mega-example using every feature.

---

# Standard chapter format

Every chapter should begin with:

```text
What you will learn
Prerequisites
Feature status
Required profile/capabilities
Example source
Reference contracts
```

Every chapter should end with:

```text
Mental model
What TNK guarantees — summarized, with Reference links
What TNK does not promise
Common mistakes
Exercises
Further Reference sections
```

For Experimental or Optional material, add:

```text
Portability boundary
Fallback/absence behavior
What may change
```

Use compact “Contract lens” callouts:

> **Contract lens — result order**  
> Search depths are nondecreasing. Order among independent solutions at the same depth is implementation-defined. See `TNK-SEARCH-002` and `TNK-CMD-002`.

The callout explains the practical consequence; the manual remains authoritative.

---

# Source and publication architecture

Use an mdBook-style structure:

```text
docs/
  manual.md
  book/
    book.toml
    src/
      SUMMARY.md
      preface.md
      part-1/
      part-2/
      ...
      appendices/
examples/
  book/
    first-session/
    expressions/
    protocol/
    composition/
    symbolic/
    embedding/
```

The Book should be one logical publication but many small source files. Keep `manual.md` as the separate normative publication.

Book appendices should contain only material useful to learning:

- exercise hints or solutions;
- running-example index;
- reading paths;
- bibliography;
- notation quick guide;
- pointer to the Maude migration guide.

Do **not** reproduce the manual’s:

- command catalogue;
- full grammar;
- operator/statement attribute tables;
- built-in hook catalogue;
- output schema;
- API inventory;
- feature matrix;
- unsupported-surface table;
- clause index.

Those already have authoritative owners in Appendices A–L.

---

# Cross-linking and verification

## Stable cross-links

Use `TNK-*` identifiers as the durable keys, not section numbers. Section numbers are navigational and may change.

The publication pipeline should expose explicit HTML anchors for clause identifiers. A Book link should resemble:

```text
TNK-SEARCH-002 — Search results
```

rather than “manual §10, third paragraph.”

Maintain a reverse index from each clause to the chapters that explain it. A simple metadata block per chapter is sufficient; no elaborate documentation database is needed.

## Runnable examples

Every complete example should run in CI:

- default-profile, self-contained examples;
- prelude-dependent examples with the intended library path;
- `smt-z3` examples in an optional-profile job;
- hook-loaded LTL examples in their capability job;
- Rust examples compiled against the workspace.

Assertions should target:

- value and sort;
- result set;
- reachability;
- completion classification;
- diagnostic category;
- Session state transition.

Avoid snapshotting:

- incidental whitespace;
- aggregate rewrite counts unless specifically taught;
- implementation-defined same-depth order;
- fresh-variable spelling;
- human-oriented warning prose.

Intentionally invalid examples should assert rejection and state preservation, not merely contain code that fails during the documentation build.

## Change policy

When the manual changes:

1. locate Book chapters citing the affected `TNK-*` clauses;
2. update explanations and examples;
3. update status/profile badges;
4. rerun all affected examples;
5. record the new target Reference edition.

If writing a Book chapter reveals a semantic fact absent from the manual, update the manual first. The Book must not accidentally create a contract through confident prose.

---

# What to borrow from the Maude book

Keep:

- gradual movement from syntax to semantics;
- alternation between concepts and substantial examples;
- serious treatment of rewriting logic, not merely command recipes;
- distinct paths for programmers, formal-methods users, and tool builders;
- extended projects showing why features matter.

Do not keep:

- duplicated reference chapters;
- encyclopedia-style exhaustive feature catalogues;
- a Core/Full organizational split not native to TNK;
- broad historical tool surveys;
- examples whose primary authority is an observed implementation transcript;
- the assumption that readers can jump into any advanced chapter without a shared conceptual spine.

The important TNK addition is the host boundary. The Book should make this chain explicit:

```text
language semantics
≠ Session state transition
≠ rendered output
≠ terminal behavior
```

That distinction is already present in the manual and should become one of the Book’s defining teaching strengths.

## Definition of done

The Book is successful when:

- a new reader can write an equational model, a transition system, and a meaningful search;
- an advanced reader can state whether a symbolic or verification result is sound, complete, bounded, unknown, or unsupported;
- an embedder can host a persistent Session without parsing incidental output as semantics;
- every exact behavioral statement is traceable to the manual;
- every complete example is runnable;
- Optional and Experimental features are unmistakably labeled;
- no reader needs the Maude manual to understand TNK;
- the Book remains readable from beginning to end rather than becoming a second reference manual.
