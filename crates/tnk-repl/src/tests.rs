//! `eval`-driven tests — the REPL with no terminal. Each feeds input submissions and asserts the output,
//! re-validating the whole pipeline (parse → flatten → build → reduce/match → print) through the shell.

use super::*;

fn repl() -> Repl {
    Repl::new(false) // uncolored, for deterministic output
}

macro_rules! conformance_file {
    ($n:expr) => {
        include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../conformance/", $n))
    };
}

/// Entering a module makes it current; a command in a *separate* submission (no module of its own — the
/// REPL case that `parse_source` rejects) binds to it.
#[test]
fn enter_module_then_reduce_across_submissions() {
    let mut r = repl();
    let ev = r.eval(
        "fmod COLOR is sort C . ops red green : -> C [ctor] . op f : C -> C . eq f(red) = green . endfm",
    );
    assert!(!ev.exit);
    assert_eq!(r.current(), Some("COLOR"));

    let out = r.eval("red f(red) .").output;
    assert!(out.contains("reduce in COLOR :"), "header: {out}");
    assert!(out.contains("rewrites: 1"), "count: {out}");
    assert!(out.contains("result C: green"), "result: {out}");
}

/// A command with no current module is a friendly error, not a panic.
#[test]
fn command_without_current_module() {
    let mut r = repl();
    assert!(r.eval("red foo .").output.contains("no current module"));
}

/// The module system end-to-end through the REPL: a diamond import reduces to the binary's value/count.
#[test]
fn import_diamond_through_repl() {
    let out = repl().eval(conformance_file!("import-diamond.maude")).output;
    assert!(out.contains("rewrites: 12"), "count: {out}");
    assert!(out.contains("result N: s(s(s(s(s(0)))))"), "value: {out}");
}

/// Renaming through the REPL: `top(e) = box(e) = e`, sort renamed to `Item`.
#[test]
fn import_renaming_through_repl() {
    let out = repl().eval(conformance_file!("import-renaming.maude")).output;
    assert!(out.contains("result Item: e"), "value: {out}");
    assert!(out.contains("rewrites: 2"), "count: {out}");
}

/// M2 milestone — the real prelude's `LIST{Nat}` (over BOOL+NAT) loads and every list operation
/// reduces byte-identically to the reference. Proves AU **identity-collapse matching**: each recursion
/// (`occurs`/`size`/`reverse`) peels `E L` off the front and must match the final singleton `c` as
/// `c nil`. Values/sorts/counts are the reference binary's (`red in T : …`, `T = LIST{Nat}`).
#[test]
fn prelude_list_m2_through_repl() {
    let out = repl().eval(conformance_file!("prelude-list.maude")).output;
    assert!(!out.contains("no parse") && !out.contains("error in module"), "LIST builds: {out}");
    let lines: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("result ") || l.starts_with("rewrites:"))
        .collect();
    // Pair each `rewrites:`/`result` into `[count] sort: value`, then compare the whole sequence.
    let got: Vec<String> = lines
        .chunks(2)
        .map(|c| {
            let n = c[0].trim_start_matches("rewrites: ").split(' ').next().unwrap_or("?");
            format!("[{n}] {}", c[1].trim_start_matches("result "))
        })
        .collect();
    assert_eq!(
        got,
        vec![
            "[6] Bool: true",          // occurs(2, 1 2 3)
            "[9] Bool: true",          // occurs(3, 1 2 3)  — recurses to the singleton
            "[10] Bool: false",        // occurs(5, 1 2 3)  — recurses past the singleton to nil
            "[3] Bool: true",          // occurs(7, 7)      — singleton subject
            "[12] NzNat: 5",           // size(1 2 3 4 5)
            "[4] NzNat: 1",            // size(7)           — collapse
            "[2] Zero: 0",             // size(nil)
            "[6] NeList{Nat}: 4 3 2 1", // reverse(1 2 3 4)
            "[3] NzNat: 7",            // reverse(7)
            "[2] List{Nat}: nil",      // reverse(nil)
            "[1] NzNat: 3",            // last(1 2 3)
            "[1] NeList{Nat}: 1 2",    // front(1 2 3)
            "[1] NeList{Nat}: 1 2 3 4", // append(1 2, 3 4)
        ],
        "LIST ops: {out}"
    );
}

/// Container milestone (cont.) — the real prelude's EXT-BOOL + SET{Nat} load and reduce
/// byte-identically. Proves the `[Sort]` kind notation (EXT-BOOL `var B : [Bool]`), ACU
/// identity-collapse matching (SET recursions to a singleton), non-linear ACU matching (`E in (E, S)`),
/// and the assoc-list separator spacing. Values/sorts/counts are the reference binary's.
#[test]
fn prelude_set_through_repl() {
    let out = repl().eval(conformance_file!("prelude-set.maude")).output;
    assert!(!out.contains("no parse") && !out.contains("error in module"), "SET builds: {out}");
    let lines: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("result ") || l.starts_with("rewrites:"))
        .collect();
    let got: Vec<String> = lines
        .chunks(2)
        .map(|c| {
            let n = c[0].trim_start_matches("rewrites: ").split(' ').next().unwrap_or("?");
            format!("[{n}] {}", c[1].trim_start_matches("result "))
        })
        .collect();
    assert_eq!(
        got,
        vec![
            "[1] Bool: false",          // true and-then false
            "[1] Bool: true",           // false or-else true
            "[1] Bool: true",           // 2 in (1, 2, 3)
            "[1] Bool: false",          // 5 in (1, 2, 3)   — absent, recurses to singleton (non-linear)
            "[1] Bool: true",           // 7 in 7           — singleton subject (collapse)
            "[8] NzNat: 3",             // | (1, 2, 3) |
            "[4] NzNat: 1",             // | 7 |
            "[6] Bool: false",          // (1, 5) subset (1, 2, 3)
            "[7] Bool: true",           // (1, 2) subset (1, 2, 3)
            "[2] NeSet{Nat}: 1, 3",     // delete(2, (1, 2, 3))
            "[1] NeSet{Nat}: 1, 2, 3, 4", // insert(4, (1, 2, 3))
            "[1] NeSet{Nat}: 1, 2, 3, 4", // union((1, 2), (3, 4))
            "[11] NeSet{Nat}: 2, 3",    // intersection((1, 2, 3), (2, 3, 4))
            "[11] NeSet{Nat}: 1, 3",    // (1, 2, 3) \ (2, 4)
        ],
        "SET ops: {out}"
    );
}

/// Helper for the prelude container fixtures: pair each `rewrites:`/`result` line into `[count] value`.
/// Each `[rewrite-count] sort: value` result, with the **full** value — a `format`-attribute result spans
/// continuation lines (a substitution's `_<-_` newline-indents each binding), captured up to the next
/// command echo / `rewrites:` line, so the multi-line layout is compared verbatim against the reference.
fn prelude_results(out: &str) -> Vec<String> {
    let lines: Vec<&str> = out.lines().collect();
    let mut results = Vec::new();
    let mut rw = "?";
    let mut i = 0;
    while i < lines.len() {
        if let Some(rest) = lines[i].strip_prefix("rewrites: ") {
            rw = rest.split(' ').next().unwrap_or("?");
        } else if let Some(value) = lines[i].strip_prefix("result ") {
            let mut block = vec![value.to_string()];
            let mut j = i + 1;
            while j < lines.len() && !lines[j].starts_with("reduce ") && !lines[j].starts_with("rewrites:") {
                block.push(lines[j].to_string());
                j += 1;
            }
            results.push(format!("[{rw}] {}", block.join("\n")));
            i = j;
            continue;
        }
        i += 1;
    }
    results
}

/// META-LEVEL Stages 1–4. The whole reflective tower (META-TERM/CONDITION/STRATEGY/MODULE/VIEW/LEVEL,
/// the real prelude) parses and builds with **no errors**; then the **entire descent surface** computes
/// byte-identically (value, sort, **rewrite count**, and layout) to the reference: the reflection core
/// (`metaReduce`/…/`metaSearchPath`, Stages 1–3.5) and the Stage-4 up*/query/syntax layer — the `up*`
/// family (`upModule`/`up{Sorts,…,Rls}`/`upView`/`upTerm`/`downTerm`), the sort/kind queries
/// (`sortLeq`/…/`maximalAritySet`), `metaParse`/`metaPrettyPrint`, and `metaWellFormed*`. (The two
/// `metaSearch` rewrite counts pin our BFS-snapshot value — see `gaps.md`; value/sort/reachability match.)
///
/// Stage 1 (the parse/flatten fixes the meta-modules first exercise):
///   * `'a ; 'b ; 'a` → `'a ; 'b` — the `op _,_ to _;_ [prec 43]` **mixfix renaming** over QID-SET
///     (grammar-aware, applied to QID-SET's `_,_` occurrences) gives a working idempotent `_;_` (`N ; N`).
///   * `getName(fmod 'FOO is nil sorts none . none none none none endfm)` → `'FOO` — the **module
///     constructor** `fmod_is_sorts_.____endfm`, whose name carries `.`/`is`/`endfm` fragments, parses
///     inside an equation (the `input_complete` chunker no longer mistakes those fragments for module
///     delimiters) and the projection equation fires.
///   * `getRls(…)` → `(none).RuleSet` — a bare **overloaded `none`** on the rhs, disambiguated by the
///     lhs kind (kind-homogeneous equation parsing).
#[test]
fn prelude_meta_through_repl() {
    let out = repl().eval(conformance_file!("prelude-meta.maude")).output;
    assert!(!out.contains("no parse") && !out.contains("error in module"), "META tower builds: {out}");
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        prelude_results(&out),
        vec![
            // Stage 1 — the tower loads + the parse/flatten fixes (idempotent renamed `_;_`, the module
            // constructor inside an equation, kind-homogeneous `none` rhs).
            "[1] NeSortSet: 'a ; 'b",
            "[1] Sort: 'FOO",
            "[1] RuleSet: (none).RuleSet",
            // Stage 2 — the reflection core: `metaReduce` (down/up + object reduction) over the `[Q]` form,
            // and `<Qids>`-classified `getName`/`getType`. Values, sorts, and rewrite counts are the
            // reference binary's.
            "[2] ResultPair: {'0.Zero, 'Zero}",
            "[3] ResultPair: {'s_^5['0.Zero], 'NzNat}",
            "[3] ResultPair: {'false.Bool, 'Bool}",
            "[6] Sort: 'foo",
            "[7] Sort: 'Bar",
            // Stage 3 — inline down_module: the module argument carries inline declarations (sorts,
            // subsorts, attributed ops, equations), down-translated straight into the built engine. BAR
            // (own eq over imported NAT) and LEN (subsorts + AU `id(...)` op + recursive AU-matching eq).
            "[3] ResultPair: {'s_^6['0.Zero], 'NzNat}",
            "[8] ResultPair: {'s_^3['0.Zero], 'NzNat}",
            // Stage 3 — the rewriting/matching/search family over the rule-bearing FOO (and `[NAT]`).
            // Stage 3.5 — value, rewrite count, AND the `format`-attribute layout are now byte-identical to
            // the reference: a substitution's `_<-_` (`format (n++i d d --)`) newline-indents each binding,
            // and `rl_=>_[_].` (`format (… s … s …)`) spaces its `[attrs]`/`.`.
            "[3] ResultPair: {'c.Elt, 'Elt}",                          // metaRewrite unbounded: a=>b=>c
            "[2] ResultPair: {'b.Elt, 'Elt}",                          // metaRewrite [1]: one step a=>b
            "[3] ResultPair: {'c.Elt, 'Elt}",                          // metaFrewrite gas 1: a=>b=>c
            "[2] Assignment: \n  'N:Nat <- 's_^4['0.Zero]",            // metaMatch: s_(N) <-> s^5(0)
            "[2] Substitution?: (noMatch).Substitution?",              // metaMatch: _+_ vs s^5 — no match
            "[2] ResultTriple: {'b.Elt, 'Elt, \n  'X:Elt <- 'b.Elt}",  // metaSearch =>+ sol 0: a=>b
            "[3] ResultTriple: {'c.Elt, 'Elt, \n  'X:Elt <- 'c.Elt}",  // metaSearch =>+ sol 1: a=>c (ab)
            "[3] ResultTriple: {'c.Elt, 'Elt, (none).Substitution}",   // metaSearch =>! to normal form c
            // metaApply: the labelled rule `unwrap` (f(N) => N) at the top, its binding, or failure.
            "[2] ResultTriple: {'s_^3['0.Zero], 'NzNat, \n  'N:Nat <- 's_^3['0.Zero]}", // apply at top
            "[1] ResultTriple?: (failure).ResultTriple?",              // solution 1 — past the last
            "[1] ResultTriple?: (failure).ResultTriple?",              // no top match (subject is s^3(0))
            // metaXmatch (extension match → {subst, context}) and metaXapply (rule at a position →
            // {term, type, subst, context}). The hole `[]` marks the matched/rewritten position: `[]` at
            // the top, `'f[[]]` at the inner f; the substitution's `_<-_` newline-indents (`format`).
            "[2] MatchPair: {\n  'N:Nat <- 's_^4['0.Zero], []}",       // metaXmatch s_(N) <-> s^5(0)
            "[2] MatchPair?: (noMatch).MatchPair?",                    // metaXmatch _+_ vs s^5 — no match
            "[2] Result4Tuple: {'f['0.Zero], 'Nat, \n  'N:Nat <- 'f['0.Zero], []}",   // xapply at top
            "[2] Result4Tuple: {'f['0.Zero], 'Nat, \n  'N:Nat <- '0.Zero, 'f[[]]}",   // xapply at inner f
            // metaSearchPath: the path to the first =>* solution is one TraceStep {a, Elt, ab-rule}. Stage
            // 3.5 closes the rule layout — `rl_=>_[_].`'s `format` spaces the `[label(…)]` and trailing `.`,
            // so the up-translated rule prints `'c.Elt [label('ab)] .` byte-identically to the reference.
            "[3] TraceStep: {'a.Elt, 'Elt, rl 'a.Elt => 'c.Elt [label('ab)] .}",
            // A two-step path (a => b => c) is a `__`-folded two-element Trace; `__`'s `format (d n d)`
            // newlines each TraceStep — exercising the assoc-fold format path (and what upModule's
            // declaration lists need). Byte-identical to the reference.
            "[3] Trace: {'a.Elt, 'Elt, rl 'a.Elt => 'b.Elt [label('r1)] .}\n\
             {'b.Elt, 'Elt, rl 'b.Elt => 'c.Elt [label('r2)] .}",
            // Stage 4 — the up*/query/parse layer. The sort/kind queries read the down-translated
            // module's lattice; value + count are the reference binary's.
            "[2] Bool: true",                                          // sortLeq(Zero, Nat)
            "[2] Bool: false",                                         // sameKind(Nat, Bool)
            "[2] Sort: 'NzNat",                                        // leastSort(2 + 3)
            "[2] NeSortSet: 'NzNat ; 'Zero",                           // lesserSorts(Nat)
            "[2] Sort: 'NzNat",                                        // glbSorts(Nat, NzNat)
            "[2] Sort: 'Nat",                                          // completeName(Nat)
            "[2] Kind: '`[Nat`]",                                      // getKind(Nat)
            "[2] NeKindSet: '`[Bool`] ; '`[Nat`]",                     // getKinds
            "[2] Sort: 'Nat",                                          // maximalSorts([Nat])
            "[2] NeSortSet: 'NzNat ; 'Zero",                           // minimalSorts([Nat])
            "[2] NeTypeList: 'Nat 'Nat",                               // maximalAritySet(_+_)
            // wellFormed: module/term/substitution. The ill-typed term/binding return false.
            "[2] Bool: true",                                          // wellFormed(2 + 3)
            "[2] Bool: false",                                         // wellFormed(true + 0) — ill-typed
            "[2] Bool: true",                                          // wellFormed(X:Nat <- 0)
            "[2] Bool: false",                                         // wellFormed(X:Nat <- true) — kind clash
            // upModule + the up* projections. Non-flat lists imports + own decls; flat (S4-LIST, no
            // imports) inlines everything with a `nil` import list. Empty sets render `none`. Exercises
            // the iter-chain collapse (`s s 0` → `'s_^2['0.Zero]`), the `id:` attribute, conditional eqs,
            // and a system module's labelled (`crl`) rules.
            "[1] FModule: fmod 'S4-FOO is\n  protecting 'NAT .\n  sorts 'Bar ; 'Foo .\n  \
             subsort 'Foo < 'Bar .\n  op 'c : nil -> 'Foo [ctor] .\n  \
             op 'f : 'Foo 'Nat -> 'Bar [ctor] .\n  op 'g : 'Bar -> 'Bar [none] .\n  none\n  \
             eq 'g['X:Bar] = 'X:Bar [none] .\nendfm",
            "[1] FModule: fmod 'S4-LIST is\n  nil\n  sorts 'Elt ; 'Lst .\n  subsort 'Elt < 'Lst .\n  \
             op '__ : 'Lst 'Lst -> 'Lst [assoc id('nil.Lst)] .\n  op 'a : nil -> 'Elt [ctor] .\n  \
             op 'b : nil -> 'Elt [ctor] .\n  op 'nil : nil -> 'Lst [ctor] .\n  none\n  \
             ceq 'a.Elt = 'b.Elt if 'a.Elt = 'b.Elt [none] .\nendfm",
            "[1] FModule: fmod 'S4-NUM is\n  protecting 'NAT .\n  sorts none .\n  none\n  \
             op 'two : nil -> 'Nat [none] .\n  none\n  eq 'two.Nat = 's_^2['0.Zero] [none] .\nendfm",
            "[1] SModule: mod 'S4-SYS is\n  nil\n  sorts 'St .\n  none\n  op 'a : nil -> 'St [ctor] .\n  \
             op 'b : nil -> 'St [ctor] .\n  op 'c : nil -> 'St [ctor] .\n  none\n  none\n  \
             rl 'a.St => 'b.St [label('r1)] .\n  crl 'b.St => 'c.St if 'b.St = 'b.St [label('r2)] .\nendm",
            "[1] Import: protecting 'NAT .",                           // upImports
            "[1] NeSortSet: 'Bar ; 'Foo",                             // upSorts (own)
            "[1] OpDeclSet: op 'c : nil -> 'Foo [ctor] .\n\
             op 'f : 'Foo 'Nat -> 'Bar [ctor] .\nop 'g : 'Bar -> 'Bar [none] .", // upOpDecls
            "[1] Equation: ceq 'a.Elt = 'b.Elt if 'a.Elt = 'b.Elt [none] .", // upEqs (conditional)
            "[1] RuleSet: rl 'a.St => 'b.St [label('r1)] .\n\
             crl 'b.St => 'c.St if 'b.St = 'b.St [label('r2)] .",      // upRls
            // upTerm reduces its argument then ups it; downTerm builds (the ambient reduces), returning
            // the default `99` when the meta-term is unresolvable.
            "[2] GroundTerm: 's_^3['0.Zero]",                          // upTerm(1 + 2)
            "[1] NzNat: 4",                                            // downTerm(s^4(0), 0)
            "[1] NzNat: 99",                                           // downTerm(bogus, 99) → default
            // metaParse parses (no reduce) → {term, sort}; noParse(n) on failure. metaPrettyPrint renders
            // a term to a QidList via the format-aware printer.
            "[2] ResultPair: {'_+_['s_['0.Zero], 's_^2['0.Zero]], 'NzNat}", // metaParse(1 + 2)
            "[2] ResultPair?: noParse(0)",                             // metaParse(foo bar)
            "[3] NeTypeList: '2 '+ '3",                                // metaPrettyPrint(2 + 3)
            // upView decomposes a view: header, from/to module exprs, and its sort/op maps.
            "[1] View: view 'S4-V from 'TRIV to 'NAT is\n  sort 'Elt to 'Nat .\n  none\n  none\nendv",
            // Stage 5 — the symbolic/SMT/strategy descent is declared (the tower loads) but stays INERT:
            // it reduces to OUR kind-level term, never misfiring, until the Phase-3.2/3.3 (D6/D7) and
            // strategy (Phase 2.4) backends land. (These two pin our inert result, *not* the reference's —
            // the reference computes `none` for a strat-free module; see gaps.md. The symbolic/SMT ops go
            // through the same exhaustive `=> None` arm.)
            "[0] [StratDeclSet]: upStratDecls('S4-FOO, false)",
            "[0] [StratDefSet]: upSds('S4-FOO, false)",
        ],
        "META tower reduces: {out}"
    );
}

/// Container milestone — the real prelude's `MAP{Nat, Nat}` loads and reduces byte-identically. Proves
/// two-parameter instantiation, the `[Y$Elt]` kind range (via `inst_sort`), and the `id:`-attribute
/// parse fix (an `_,_ [assoc comm id: empty prec 121]` keeps its prec, so a `_|->_` entry parses as an
/// argument). Values/sorts/counts are the reference binary's.
#[test]
fn prelude_map_through_repl() {
    let out = repl().eval(conformance_file!("prelude-map.maude")).output;
    assert!(!out.contains("no parse") && !out.contains("error in module"), "MAP builds: {out}");
    assert_eq!(
        prelude_results(&out),
        vec![
            "[2] Map{Nat,Nat}: 1 |-> 10, 2 |-> 20", // insert(1,10,insert(2,20,empty))
            "[3] NzNat: 10",                        // (… )[1]
            "[3] NzNat: 20",                        // (… )[2]
            "[1] [Nat]: undefined",                 // (… )[3] — miss → kind-level undefined
            "[1] Bool: true",                       // $hasMapping(…, 1)
            "[1] Bool: false",                      // $hasMapping((1|->10), 3)
        ],
        "MAP ops: {out}"
    );
}

/// Container milestone — the real prelude's `ARRAY{Nat, Nat0}` loads and reduces byte-identically.
/// Two-parameter (`X :: TRIV`, `Y :: DEFAULT`); the `_;_` array constructor; a missing index returns the
/// DEFAULT element `0`. Values/sorts/counts are the reference binary's.
#[test]
fn prelude_array_through_repl() {
    let out = repl().eval(conformance_file!("prelude-array.maude")).output;
    assert!(!out.contains("no parse") && !out.contains("error in module"), "ARRAY builds: {out}");
    assert_eq!(
        prelude_results(&out),
        vec![
            "[6] Array{Nat,Nat0}: 1 |-> 10 ; 2 |-> 20", // insert(1,10,insert(2,20,empty))
            "[3] NzNat: 10",                            // (… )[1]
            "[1] Zero: 0",                              // (… )[3] — miss → DEFAULT 0
            "[1] Bool: true",                           // $hasMapping((1|->10), 1)
        ],
        "ARRAY ops: {out}"
    );
}

/// Variable aliases are module-local (Blocker B): `M` and its import `P` both declare a variable `A`
/// at different sorts; `M`'s own equation must use `M`'s `A`, even though flattening collects `P`'s `A`
/// first. Without module-local scoping the name-dedup mistypes `f(A, L)` → no parse (the real `LIST`'s
/// `var A : List{X}` shadowed by BOOL-OPS' `vars A B C : Bool`). Values are the reference binary's.
#[test]
fn var_shadowing_through_repl() {
    let out = repl().eval(conformance_file!("var-shadowing.maude")).output;
    assert!(!out.contains("no parse"), "the shadowed prefix application must parse: {out}");
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(results, vec!["result T: e e", "result T: e", "result S: a"], "shadow values: {out}");
}

/// B-i: a theory loads through the REPL end-to-end — it becomes current, its `[nonexec]` axiom does NOT
/// fire (`e < e` stays, 0 rewrites), and an ordinary theory equation does (`id(e) = e`, 1 rewrite).
/// Values/counts are the reference binary's.
#[test]
fn theory_nonexec_through_repl() {
    let out = repl().eval(conformance_file!("theory-nonexec.maude")).output;
    assert!(out.contains("reduce in ELT-ORD :"), "header: {out}");
    assert!(out.contains("result Bool: e < e"), "nonexec not applied: {out}");
    assert!(out.contains("result Elt: e"), "exec eq fires: {out}");
    assert!(out.contains("rewrites: 0"), "nonexec count: {out}");
    assert!(out.contains("rewrites: 1"), "exec count: {out}");
}

/// B-i: a multi-line theory is buffered as ONE submission by `input_complete` (which recognizes
/// `fth`/`endfth`), then entered and made current — the interactive multi-line boundary for theories.
#[test]
fn theory_entry_is_one_submission_and_current() {
    let mut r = repl();
    assert!(!r.input_complete("fth TRIV is\n"), "open theory keeps buffering");
    assert!(!r.input_complete("fth TRIV is\n  sort Elt .\n"), "a `.` inside an open theory is not the end");
    let src = "fth TRIV is\n  sort Elt .\nendfth\n";
    assert!(r.input_complete(src), "`endfth` completes the submission");
    let ev = r.eval(src);
    assert!(!ev.exit);
    assert_eq!(r.current(), Some("TRIV"));
}

/// B-ii: a view loads through the REPL — the target module still reduces, `show views` lists it, and
/// `show view` renders its maps (byte-matching the reference binary's `show view`).
#[test]
fn view_through_repl() {
    let mut r = repl();
    let out = r.eval(conformance_file!("view-good.maude")).output;
    assert!(out.contains("result N: z"), "target module reduces: {out}");
    assert!(r.eval("show views .").output.contains("ToNum"), "show views lists it");
    let shown = r.eval("show view ToNum .").output;
    assert_eq!(shown, "view ToNum from TRIV to NUM is\n  sort Elt to N .\nendv");
}

/// B-iii: a parameterized module builds and reduces through the REPL — it echoes as its bare base name
/// (`CTR`, not `CTR{X}`) and its results print with structured sorts (`Ctr{X}` / least sort `NzCtr{X}`).
#[test]
fn parameterized_module_through_repl() {
    let out = repl().eval(conformance_file!("param-module.maude")).output;
    assert!(out.contains("reduce in CTR :"), "echoes as the base name: {out}");
    assert!(out.contains("result Ctr{X}: zero"), "structured result sort: {out}");
    assert!(out.contains("result NzCtr{X}: inc(inc(zero))"), "least sort over structured sorts: {out}");
}

/// B-iv: parameterized-module instantiation through the REPL end-to-end — a single-parameter `BOX{ToColor}`
/// (structured instance sort `Box{ToColor}`, view-image sort `Hue`) and a multi-parameter `PR{VA, VB}`.
#[test]
fn instantiation_through_repl() {
    let out = repl().eval(conformance_file!("instantiation.maude")).output;
    assert!(out.contains("result Box{ToColor}: wrap(green)"), "structured instance sort: {out}");
    assert!(out.contains("result Hue: green"), "view-image sort: {out}");
    assert!(out.contains("result SA: a"), "multi-parameter instantiation: {out}");
}

/// Axis-A5: chained instantiation `M{ToTheory}{Arg}` — a theory-view first level (parameter bound to a
/// richer theory) then a by-parameter / module-view second level, with the chained import's renaming
/// collapsing the multi-level structured sort. This is the SORTABLE-LIST family's shape; here `USE{X ::
/// ORD}` chains `LST{ORD}{X}` (renaming `Lst{ORD}{X}` back to `Lst{X}`), instantiated at `USE{OrdColor}`.
/// Byte-identical to the reference; the prelude's `SORTABLE-LIST{Nat<}` now sorts identically too.
#[test]
fn instantiation_chained_through_repl() {
    let out = repl().eval(conformance_file!("instantiation-chained.maude")).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result Lst{OrdColor}: cons(red, cons(green, nil))", // pair(red, green) — chained instance sort
            "result Lst{OrdColor}: cons(green, nil)",
        ],
        "chained instantiation: {out}"
    );
}

/// Axis-A1: view operator maps applied at instantiation through the REPL — `op zero to term f0` (op→term)
/// and `op wrap to box` (op→op), so `ARR{ToFL}`'s `d0`/`d1` reduce to the target's terms.
#[test]
fn view_opmap_through_repl() {
    let out = repl().eval(conformance_file!("param-view-opmap.maude")).output;
    assert!(out.contains("result F: f0"), "op->term: {out}");
    assert!(out.contains("result F: box(f0)"), "op->op over op->term: {out}");
}

/// Axis-A4: a parameter theory that imports a module — the module-declared sort `Bool` is kept (not
/// renamed to `X$Bool`), so the parameterized module builds and the instance reduces.
#[test]
fn theory_module_sorts_through_repl() {
    let out = repl().eval(conformance_file!("param-theory-module-sorts.maude")).output;
    assert!(out.contains("result Bool: tt"), "module-declared sort kept: {out}");
}

/// M0 milestone — the real prelude's BOOL stack (TRUTH-VALUE → BOOL-OPS → TRUTH → BOOL, verbatim)
/// loads and reduces byte-identically to Maude's built-in BOOL. Proves the poly/Universal expansion
/// (`_==_`/`_=/=_`/`if_then_else_fi` instantiated over the Bool kind) and the SystemTrue/SystemFalse
/// anchors. Each value + count is the reference binary's (`red in BOOL : …`).
#[test]
fn prelude_bool_m0_through_repl() {
    let out = repl().eval(conformance_file!("prelude-bool.maude")).output;
    // The poly ops parse and pretty-print — the headers round-trip the mixfix.
    assert!(out.contains("reduce in BOOL : true == true ."), "== header: {out}");
    assert!(out.contains("reduce in BOOL : if true then false else true fi ."), "if header: {out}");
    // Result value + sort, in order.
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result Bool: false", // true and false
            "result Bool: true",  // true == true
            "result Bool: true",  // true =/= false
            "result Bool: false", // if true then false else true fi
            "result Bool: true",  // false or true and not false
        ],
        "values: {out}"
    );
    // Distinctive rewrite counts: four single-rewrite reduces + the 7-rewrite xor expansion.
    assert_eq!(out.matches("rewrites: 1 ").count(), 4, "1-rewrite reduces: {out}");
    assert!(out.contains("rewrites: 7 "), "xor-expansion count: {out}");
}

/// Increment-3 core: poly/Universal expansion over TWO kinds (Bool + an unrelated Color). `_==_` and
/// `if_then_else_fi` each instantiate per kind; this proves distinct per-kind dispatch, grammar
/// disambiguation, and the `if`-result sort over a non-Bool kind. Values/counts are the reference
/// binary's (built-in poly `==`/`if`, `red in MK : …`).
#[test]
fn poly_multikind_through_repl() {
    let out = repl().eval(conformance_file!("poly-multikind.maude")).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result Bool: true",  // true == true     (Bool-kind ==)
            "result Bool: false", // true == false    (Bool-kind ==)
            "result Bool: true",  // c0 == c0         (Color-kind ==)
            "result Bool: false", // c0 == c2         (Color-kind ==)
            "result Color: c0",   // if true then c0 else c2 fi          (Color-kind if)
            "result Color: c2",   // if (c1 == c2) then c0 else c2 fi    (nested == then if)
        ],
        "multikind values: {out}"
    );
    // The nested reduce is exactly 2 rewrites (inner Color-kind == → false, then the if selects c2).
    // The header echoes with the redundant parens elided — `if c1 == c2 then …` — exactly as the
    // reference binary prints it (==' s prec 51 makes them unnecessary).
    assert!(
        out.contains("reduce in MK : if c1 == c2 then c0 else c2 fi .") && out.contains("rewrites: 2 "),
        "nested ==/if count: {out}"
    );
}

/// Increment 4 — a bare boolean condition `if b` abbreviates `if b = true`. The conditional
/// `ceq f(X) = b if X == a` fires for `f(a)` (a == a = true, 2 rewrites → b) and not for `f(b)`
/// (b == a = false, 1 rewrite, stays). Values/counts are the reference binary's (`red in T : …`).
#[test]
fn bare_condition_through_repl() {
    let out = repl().eval(conformance_file!("bare-condition.maude")).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(results, vec!["result Foo: b", "result Foo: f(b)"], "bare-cond values: {out}");
    // f(a): == eval + eq application = 2; f(b): == eval only (condition false) = 1.
    assert_eq!(out.matches("rewrites: 2 ").count(), 1, "fired count: {out}");
    assert_eq!(out.matches("rewrites: 1 ").count(), 1, "not-fired count: {out}");
}

/// M1 milestone — the real prelude's NAT (with its BOOL substrate) loads and every built-in reduces
/// byte-identically to Maude's built-in NAT, incl. the increment-5 additions: the `~>` partial arrow
/// (modExp parses), the ACU bitwise folds `xor`/`&`/`|` (multiplicity-aware — `5 xor 5 = 0`), the CUI
/// `sd` (`|m−n|`, commutative), `modExp` (modpow), and the `>>`/`<<` shifts (incl. the bignum
/// `1 << 64`). Each value/sort/count is the reference binary's (`red in NAT : …`); all cases are
/// 2-operand or prefix N-ary, whose counts match exactly (see gaps.md for the ≥3-operand-infix delta).
#[test]
fn prelude_nat_m1_through_repl() {
    let out = repl().eval(conformance_file!("prelude-nat.maude")).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result NzNat: 5",                    // 2 + 3
            "result NzNat: 3",                    // 7 quo 2
            "result NzNat: 1",                    // 7 rem 2
            "result NzNat: 1024",                 // 2 ^ 10
            "result NzNat: 6",                    // gcd(12, 18)
            "result NzNat: 2",                    // gcd(12, 18, 8)  — prefix N-ary folds to 1 rewrite
            "result NzNat: 12",                   // lcm(4, 6)
            "result NzNat: 3",                    // min(3, 5)
            "result NzNat: 5",                    // max(3, 5)
            "result NzNat: 5",                    // sd(3, 8)
            "result NzNat: 5",                    // sd(8, 3)  — commutative
            "result NzNat: 6",                    // 5 xor 3
            "result Zero: 0",                     // 5 xor 5   — multiplicity cancels
            "result NzNat: 8",                    // 12 & 10
            "result NzNat: 14",                   // 12 | 10
            "result NzNat: 24",                   // modExp(2, 10, 1000)
            "result NzNat: 40",                   // 5 << 3
            "result NzNat: 18446744073709551616", // 1 << 64  — bignum shift
            "result NzNat: 5",                    // 40 >> 3
            "result Bool: true",                  // 3 < 5
            "result Bool: true",                  // 5 <= 5
            "result Bool: true",                  // 7 > 2
            "result Bool: false",                 // 2 >= 7
            "result Bool: true",                  // 3 divides 12
        ],
        "NAT values/sorts: {out}"
    );
    // Every reduce here is a single built-in rewrite (2-operand / prefix N-ary).
    assert_eq!(out.matches("rewrites: 1 ").count(), 24, "NAT counts: {out}");
}

/// Tier 2 — the remaining built-in data types + leaf special ops: INT (`abs`/`~`, signed bignum +
/// two's-complement bitwise), RAT (rationals on the Division op), FLOAT (full op set + partiality:
/// `/0`/NaN don't reduce, but `log(0.0) = -Infinity` does), STRING/QID (`ascii`/`char`/`find`/case +
/// STRING-OPS classification/trim; value-dependent `Char`/`String` sort; qid backquote-escaping),
/// CONVERSION (float↔rat↔string + `decFloat`), INITIAL-EQUALITY-PREDICATE, RANDOM (MT19937 seed 0),
/// COUNTER (stateful — inert under `reduce`, advancing under `rewrite`). One fixture defines the whole
/// chain and reduces in each module via the `in <MODULE> :` qualifier; values, sorts, and rewrite counts
/// are byte-identical to the reference binary's built-in modules.
#[test]
fn prelude_tier2_through_repl() {
    let out = repl().eval(conformance_file!("prelude-tier2.maude")).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            // INT — abs, ~, (-1)&12, (-5) xor 3, -7 quo 2, (-3)*(-4), gcd(-12,18)
            "result NzNat: 5",
            "result NzInt: -6",
            "result NzNat: 12",
            "result NzInt: -8",
            "result NzInt: -3",
            "result NzNat: 12",
            "result NzNat: 6",
            // RAT
            "result PosRat: 5/6",
            "result PosRat: 2/3",
            "result PosRat: 3/4",
            "result NzNat: 3",
            // FLOAT — 2^10, sqrt 2, floor 3.7, atan2; then partiality: /0 and sqrt(-1) stay [Float],
            // log(0) = -Infinity; `=[ ]` approx-equality
            "result FiniteFloat: 1.024e+3",
            "result FiniteFloat: 1.4142135623730951",
            "result FiniteFloat: 3.0",
            "result FiniteFloat: 7.8539816339744828e-1",
            "result [Float]: 1.0 / 0.0",
            "result [Float]: sqrt(-1.0)",
            "result Float: -Infinity",
            "result Bool: true",
            // STRING — concat, ascii, char, find, rfind, upperCase (Char vs String sort is value-dependent)
            "result String: \"foobar\"",
            "result NzNat: 65",
            "result Char: \"A\"",
            "result NzNat: 2",
            "result NzNat: 2",
            "result String: \"HELLO\"",
            // STRING-OPS — isDigit, isAlphabetic, startsWith, trim
            "result Bool: true",
            "result Bool: true",
            "result Bool: true",
            "result String: \"hi\"",
            // QID — string('foo); qid("a b") escapes the space as a backquote
            "result String: \"foo\"",
            "result Qid: 'a`b",
            // CONVERSION — float, rat (exact), string-in-base, rat-from-base, float→string, string→float,
            // decFloat
            "result FiniteFloat: 5.0e-1",
            "result PosRat: 3602879701896397/36028797018963968",
            "result String: \"ff\"",
            "result NzNat: 255",
            "result String: \"-2.75\"",
            "result FiniteFloat: 3.1400000000000001",
            "result DecFloat: < 1, \"123456\", 3 >",
            // INITIAL-EQUALITY-PREDICATE, RANDOM, COUNTER (reduce leaves it; rewrite below advances it)
            "result Bool: true",
            "result NzNat: 2357136044",
            "result NzNat: 2774094101",
            "result [Nat]: counter",
            "result NzNat: 3",
        ],
        "Tier 2 values/sorts: {out}"
    );
    // COUNTER under `rewrite` yields 0, 1, 2 → 0 + 1 + 2 = 3 in 5 rewrites (3 counter steps + 2 ACU
    // folds) — the only multi-rewrite command here (the kind-sorted `[Float]`/`counter` results above
    // already attest the partial-op / inert-counter non-reductions).
    assert!(out.contains("rewrite in COUNTER :") && out.contains("rewrites: 5 in"), "counter: {out}");
}

/// The view-gap parser fix: a *parameterized* view declaration (`view V{X :: T} from T to M{X}`) and a
/// renaming over a **structured** sort (`* (sort Box{ColorE} to ColorBox)`) both parse, so a parameterized
/// module instantiated on a view + renamed builds and reduces. This is the pattern the metalevel's
/// container helpers use on the builtin chain — `protecting LIST{Qid} * (sort NeList{Qid} to NeQidList)`
/// (`QID-LIST`/`NAT-LIST`/`QID-SET`, verified byte-identical against the loaded prelude). Byte-identical to
/// the reference. (Chained multi-level instantiation — `LIST{A}{B}`, the SORTABLE-LIST family — is the
/// separate Axis-A5 residual in `gaps.md`.)
#[test]
fn view_parameterized_through_repl() {
    let out = repl().eval(conformance_file!("view-parameterized.maude")).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result ColorBox: b(red, green)", // b(red, green)
            "result ColorBox: b(red, green)", // b(green, red) — comm, same canonical form
        ],
        "parameterized-view instantiation + structured renaming: {out}"
    );
}

/// The eq parser splits a statement body at the **last** top-level `=` and peels a trailing `[attrs]`
/// only when its first inner token is an attribute keyword — so an equation with a `[_]`-list rhs
/// (`eq rev([X] L) = rev(L) [X] .`) keeps its bracketed term, and one ending in `[owise]` is still
/// recognised as an owise equation. (This is what the `[_]`-list modules `LIST*`/`SET*` need; it also
/// fixed a Tier-2 regression where the `=[`-of-`_=[_]_` heuristic wrongly skipped a separator `= [`.)
#[test]
fn eq_bracket_rhs_through_repl() {
    let out = repl().eval(conformance_file!("eq-bracket-rhs.maude")).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result BList: [c] [b] [a]", // rev([a] [b] [c]) — `[X]`-rhs equation
            "result Elt: a",             // headOr([a] [b], c) — `[X] L` pattern matches
            "result Elt: c",             // headOr(nil, c) — falls to the `[owise]` equation
        ],
        "`[_]`-list rhs + `[owise]` peel: {out}"
    );
}

/// B-ii: a view buffers as one submission via `view`/`endv`, and a bad view (missing target sort) is a
/// friendly error — the binary's diagnostic — not a panic, and does not abort the session.
#[test]
fn bad_view_reports_error_through_repl() {
    let mut r = repl();
    assert!(!r.input_complete("view V from TRIV to NUM is\n"), "open view keeps buffering");
    assert!(r.input_complete("view V from TRIV to NUM is endv\n"), "`endv` completes the submission");
    r.eval("fth TRIV is sort Elt . endfth");
    r.eval("fmod NUM is sort N . endfm");
    let out = r.eval("view Bad from TRIV to NUM is sort Elt to NoSuch . endv").output;
    assert!(out.contains("failed to find sort NoSuch in NUM"), "got: {out}");
    // The session survives — a following module still enters.
    r.eval("fmod OK is sort Z . endfm");
    assert_eq!(r.current(), Some("OK"));
}

/// C7 structure sharing end-to-end through the REPL: a repeated reducible subterm reduces once
/// (Maude's hash-consed subject/rhs DAG). Every result + count is the reference binary's. The strong
/// C7-specific guard: this fixture's reference counts top out at 2, so a pre-C7 over-count (`f(a)` was
/// 3, the deep chain and the triple were 4) would surface as a `rewrites: 3`/`4` line — assert there is
/// none. (The dedup window is applied in `reduce_command`; forwarding makes the shared node reduce once.)
#[test]
fn sharing_through_repl() {
    let out = repl().eval(conformance_file!("correctness-sharing.maude")).output;
    assert!(out.contains("result P: < c, c >"), "deep shared chain: {out}");
    assert!(out.contains("result P: < b, b >"), "free/rhs/triple dup: {out}");
    assert!(out.contains("result P: < mkA, mkA >"), "mb on shared constant: {out}");
    assert!(out.contains("result L: b b b"), "AU triple share: {out}");
    assert!(out.contains("result E: b & b"), "CUI share: {out}");
    assert!(out.contains("result E: b + b"), "ACU share: {out}");
    assert!(!out.contains("rewrites: 3"), "C7: no pre-fix over-count (f(a) was 3): {out}");
    assert!(!out.contains("rewrites: 4"), "C7: no pre-fix over-count (chain/triple were 4): {out}");
}

/// C13: a long result is line-wrapped through `eval` exactly as Maude's stdout wrapper (`auto_wrap`) —
/// every line stays within 79 columns and wrapped lines carry the 4-space indent. (The differential
/// suite pins this byte-identical to the reference binary, incl. `fib(22)`'s ~190-line numeral; this
/// pins that `eval` applies the wrap end-to-end, and that short output is left untouched.)
#[test]
fn long_result_is_line_wrapped() {
    let mut r = repl();
    r.eval("fmod W is sort N . op z : -> N [ctor] . op s_ : N -> N [ctor] . endfm");
    let out = r.eval(&format!("red {}z .", "s ".repeat(40))).output;
    assert!(out.contains("\n    s"), "a wrapped continuation line carries the 4-space indent: {out}");
    for line in out.lines() {
        assert!(line.len() <= 79, "every line stays within 79 columns: {} cols in {line:?}", line.len());
    }
    // A short reduction is unaffected (no wrapping introduced).
    let short = r.eval("red s s z .").output;
    assert!(short.contains("result N: s s z"), "short result rendered: {short}");
    assert!(!short.contains("\n    "), "short result is not wrapped: {short}");
}

/// The `match` command renders solutions (a commutative pattern → two pairings).
#[test]
fn match_command_through_repl() {
    let mut r = repl();
    r.eval("fmod M is sort E . ops a b : -> E . op g : E E -> E [comm] . vars X Y : E . endfm");
    let out = r.eval("match g(X, Y) <=? g(a, b) .").output;
    assert!(out.contains("match in M :"), "header: {out}");
    assert!(out.contains("X --> a") && out.contains("X --> b"), "pairings: {out}");
}

/// `select` switches the current module; success is silent, an unknown module is reported.
#[test]
fn select_and_show() {
    let mut r = repl();
    r.eval("fmod A is sort SA . op a : -> SA [ctor] . endfm");
    r.eval("fmod B is sort SB . op b : -> SB [ctor] . endfm");
    assert_eq!(r.current(), Some("B"));

    assert!(r.eval("select A .").output.is_empty(), "select success is silent");
    assert_eq!(r.current(), Some("A"));
    assert!(r.eval("select NOPE .").output.contains("no module"));

    let mods = r.eval("show modules .").output;
    assert!(mods.contains('A') && mods.contains('B'), "show modules: {mods}");
    let sm = r.eval("show module .").output; // current = A
    assert!(sm.contains("fmod A") && sm.contains("SA"), "show module: {sm}");
}

/// `quit`/`q`/`exit` signal exit.
#[test]
fn quit_exits() {
    let mut r = repl();
    assert!(r.eval("quit").exit);
    assert!(r.eval("q").exit);
    assert!(r.eval("exit").exit);
    assert!(!r.eval("red x .").exit);
}

/// An undefined import is reported (the REPL doesn't crash).
#[test]
fn unknown_import_reported() {
    let out = repl().eval("fmod M is protecting NOPE . sort S . endfm").output;
    assert!(out.contains("not defined") || out.contains("error"), "got: {out}");
}

/// A Peano module (matches the reference binary's rendering exactly: `s_` mixfix, infix `_+_`).
const PEANO: &str = "fmod PEANO is sort Nat . op 0 : -> Nat [ctor] . op s_ : Nat -> Nat [ctor] . \
     op _+_ : Nat Nat -> Nat . vars N M : Nat . eq N + 0 = N . eq N + s M = s (N + M) . endfm";

/// `set trace on` prints each rewrite step; `set trace off` removes them.
#[test]
fn trace_shows_rewrite_steps() {
    let mut r = repl();
    r.eval(
        "fmod NAT0 is sort N . op 0 : -> N [ctor] . op s : N -> N [ctor] . op add : N N -> N . \
         vars X Y : N . eq add(0, Y) = Y . eq add(s(X), Y) = s(add(X, Y)) . endfm",
    );
    r.eval("set trace on .");
    let out = r.eval("red add(s(0), s(0)) .").output;
    assert_eq!(out.matches("*********** equation").count(), 2, "two steps: {out}");
    assert!(out.contains("add(s(0), s(0))\n--->"), "first redex: {out}");
    assert!(out.contains("result N: s(s(0))"), "result: {out}");

    r.eval("set trace off .");
    let plain = r.eval("red add(s(0), s(0)) .").output;
    assert!(!plain.contains("***********"), "no trace when off: {plain}");
}

/// The full equation trace (body + substitution + redex/result) is byte-identical to the reference
/// binary (`~/Downloads/Maude-3/maude` on the same module + `set trace on .`).
#[test]
fn trace_full_equation_block() {
    let mut r = repl();
    r.eval(PEANO);
    r.eval("set trace on .");
    let out = r.eval("red s 0 + s 0 .").output;
    assert!(
        out.contains(
            "*********** equation\n\
             eq N + s M = s (N + M) .\n\
             N --> s 0\n\
             M --> 0\n\
             s 0 + s 0\n\
             --->\n\
             s (s 0 + 0)\n\
             *********** equation\n\
             eq N + 0 = N .\n\
             N --> s 0\n\
             s 0 + 0\n\
             --->\n\
             s 0\n"
        ),
        "full eq trace block:\n{out}"
    );
}

/// `set trace substitution off` drops the `Var --> binding` lines; `set trace whole on` adds the
/// `Old:`/`New:` whole-term lines (the inner step's whole is the *full* term, not just the redex).
#[test]
fn trace_substitution_and_whole_flags() {
    let mut r = repl();
    r.eval(PEANO);
    r.eval("set trace on .");
    r.eval("set trace substitution off .");
    let no_subst = r.eval("red s 0 + s 0 .").output;
    assert!(no_subst.contains("*********** equation\neq N + s M = s (N + M) .\ns 0 + s 0\n--->"), "no subst: {no_subst}");
    // The substitution `Var --> binding` lines are gone (the `--->` arrow is not a substitution line).
    assert!(!no_subst.contains("N --> ") && !no_subst.contains("M --> "), "substitution lines dropped: {no_subst}");

    r.eval("set trace substitution on .");
    r.eval("set trace whole on .");
    let whole = r.eval("red s 0 + s 0 .").output;
    // The second (inner) step rewrites `s 0 + 0`; its whole term is `s (s 0 + 0)` -> `s s 0`.
    assert!(whole.contains("Old: s (s 0 + 0)\ns 0 + 0\n--->\ns 0\nNew: s s 0\n"), "whole inner step: {whole}");
}

/// A conditional equation traces the whole sub-stream: `trial #1`, the `ceq … if …` body + the
/// substitution, `solving`/`success for condition fragment`, and `success #1`, then the firing step.
#[test]
fn trace_conditional_substream() {
    let mut r = repl();
    r.eval(
        "fmod CEQ-MAX is sorts Nat Truth . ops tt ff : -> Truth [ctor] . op z : -> Nat [ctor] . \
         op s_ : Nat -> Nat [ctor] . op _<=_ : Nat Nat -> Truth . op max : Nat Nat -> Nat . \
         vars M N : Nat . eq z <= N = tt . eq s M <= z = ff . eq s M <= s N = M <= N . \
         ceq max(M, N) = N if M <= N = tt . ceq max(M, N) = M if M <= N = ff . endfm",
    );
    r.eval("set trace on .");
    let out = r.eval("red max(s z, s s z) .").output;
    assert!(
        out.contains(
            "*********** trial #1\n\
             ceq max(M, N) = N if M <= N = tt .\n\
             M --> s z\n\
             N --> s s z\n\
             *********** solving condition fragment\n\
             M <= N = tt\n"
        ),
        "trial + fragment start:\n{out}"
    );
    assert!(
        out.contains(
            "*********** success for condition fragment\n\
             M <= N = tt\n\
             M --> s z\n\
             N --> s s z\n\
             *********** success #1\n"
        ),
        "fragment success + trial success:\n{out}"
    );
    assert!(out.contains("result Nat: s s z"), "result: {out}");
}

/// `set trace condition off` keeps the trial/fragment scaffolding but hides the condition's nested
/// reductions (the `s z <= s s z` equation steps); a failed-then-backtracked trial renders `failure #1`.
#[test]
fn trace_condition_off_and_backtrack() {
    let mut r = repl();
    r.eval(
        "fmod CEQ-MAX is sorts Nat Truth . ops tt ff : -> Truth [ctor] . op z : -> Nat [ctor] . \
         op s_ : Nat -> Nat [ctor] . op _<=_ : Nat Nat -> Truth . op max : Nat Nat -> Nat . \
         vars M N : Nat . eq z <= N = tt . eq s M <= z = ff . eq s M <= s N = M <= N . \
         ceq max(M, N) = N if M <= N = tt . ceq max(M, N) = M if M <= N = ff . endfm",
    );
    r.eval("set trace on .");
    // Backtrack: trial #1 (first ceq) fails, trial #2 (second ceq) succeeds.
    let bt = r.eval("red max(s s z, s z) .").output;
    assert!(bt.contains("*********** failure for condition fragment\nM <= N = tt\n*********** failure #1\n"), "failure: {bt}");
    assert!(bt.contains("*********** trial #2\nceq max(M, N) = M if M <= N = ff ."), "trial #2: {bt}");

    // condition off: the nested `_<=_` equation steps inside the condition disappear, scaffolding stays.
    r.eval("set trace condition off .");
    let off = r.eval("red max(s z, s s z) .").output;
    assert!(off.contains("*********** solving condition fragment\nM <= N = tt\n*********** success for condition fragment"), "scaffolding kept: {off}");
    assert!(!off.contains("z <= s z\n--->"), "nested condition rewrites hidden: {off}");
}

/// A membership axiom traces as a sort narrowing: `mb lhs : sort .` + substitution + `oldSort: term
/// becomes newSort`. `cmb` fires as a membership but its trial uses the `cmb …` body. With `set trace
/// whole on` each step also shows Maude's `Whole:` line — the full root term with the constrained
/// subject in place (C1: memberships fire inside the reduce loop, so the frame stack is available to
/// reconstruct it; closes full-trace deviation #2). Byte-exact vs the reference binary.
#[test]
fn trace_membership_and_cmb() {
    let mut r = repl();
    r.eval(
        "fmod MB-CHAIN is sorts A B C . subsorts C < B < A . op a : -> A [ctor] . op g : A -> A [ctor] . \
         var X : A . mb g(X) : B . mb g(g(X)) : C . endfm",
    );
    r.eval("set trace on .");
    let out = r.eval("red g(g(a)) .").output;
    assert!(out.contains("*********** membership axiom\nmb g(X) : B .\nX --> a\nA: g(a) becomes B\n"), "inner mb: {out}");
    assert!(out.contains("*********** membership axiom\nmb g(g(X)) : C .\nX --> a\nA: g(g(a)) becomes C\n"), "outer mb: {out}");
    assert!(out.contains("result C:"), "result sort C: {out}");

    // `set trace whole on` adds the `Whole:` line — the full root term (`g(g(a))`) at each membership
    // application, for both the inner (`g(a) becomes B`) and outer (`g(g(a)) becomes C`) steps.
    r.eval("set trace whole on .");
    let whole = r.eval("red g(g(a)) .").output;
    assert!(whole.contains("X --> a\nWhole: g(g(a))\nA: g(a) becomes B\n"), "inner mb Whole: {whole}");
    assert!(whole.contains("X --> a\nWhole: g(g(a))\nA: g(g(a)) becomes C\n"), "outer mb Whole: {whole}");
}

/// The command echo (`reduce in M : … .`) re-spaces the input tokens with Maude's rules — no space
/// before a `,` or bracket, none after an opening bracket — so nested-paren / comma terms echo compactly
/// (matching the reference binary), instead of the old space-between-every-token form.
#[test]
fn command_echo_spacing() {
    let mut r = repl();
    r.eval(
        "fmod E is sorts N P . op z : -> N [ctor] . op s_ : N -> N [ctor] . op g : N -> N . \
         op <_,_> : N N -> P [ctor] . var X : N . eq g(X) = X . endfm",
    );
    let nested = r.eval("red g(g(z)) .").output;
    assert!(nested.contains("reduce in E : g(g(z)) ."), "nested-paren echo: {nested}");
    let comma = r.eval("red < z, s z > .").output;
    assert!(comma.contains("reduce in E : < z, s z > ."), "comma echo: {comma}");
}

/// C9 / C10 / C11: the command echo prints the *normalized, pretty-printed* parsed term (Maude's
/// "normalize, then print"), so float / rational / negative-integer special constants collapse to their
/// canonical surface form in the `reduce in M : … .` line — byte-for-byte as the reference binary echoes
/// them. (The reduced *result* printing is pinned by the `conform_render` fixtures; this pins the echo,
/// which is REPL-only.)
#[test]
fn faithful_special_constant_echo() {
    // C9 — a float echo reformats via doubleToString (`100.0` → `1.0e+2`), not the raw input token.
    let mut r = repl();
    r.eval(conformance_file!("correctness-float-print.maude")); // enters FLTB (+ runs its reds)
    let e = r.eval("red 100.0 * 100.0 .").output;
    assert!(e.contains("reduce in FLTB : 1.0e+2 * 1.0e+2 ."), "float echo: {e}");
    assert!(e.contains("result Flt: 1.0e+4"), "float result: {e}");

    // C11 — a rational echo is the compact `num/den`; a `0/N` (Zero numerator) is not a rational, so it
    // stays spaced.
    let mut r = repl();
    r.eval(conformance_file!("rat.maude")); // enters RATB
    let q = r.eval("red 6 / 4 .").output;
    assert!(q.contains("reduce in RATB : 6/4 ."), "rational echo: {q}");
    assert!(q.contains("result NzRat: 3/2"), "rational result: {q}");
    let z = r.eval("red 0 / 5 .").output;
    assert!(z.contains("reduce in RATB : 0 / 5 ."), "0/N stays spaced: {z}");

    // C10 — a glued `-7` echoes compactly and reduces; a spaced `- 3` also echoes the compact `-3`; and
    // `5 -7` fails to parse, exactly as the reference binary rejects it.
    let mut r = repl();
    r.eval(conformance_file!("correctness-glued-minus.maude")); // enters INTB
    let g = r.eval("red -7 quo 2 .").output;
    assert!(g.contains("reduce in INTB : -7 quo 2 ."), "glued-minus echo: {g}");
    assert!(g.contains("result NzInt: -3"), "glued-minus result: {g}");
    let s = r.eval("red - 3 .").output;
    assert!(s.contains("reduce in INTB : -3 ."), "spaced minus echoes compact: {s}");
    let bad = r.eval("red 5 -7 .").output;
    assert!(bad.contains("no parse"), "`5 -7` is rejected like the binary: {bad}");
}

/// Multi-fragment `:=` backtracking: when the search backtracks *through* a deterministic fragment
/// (`g(X) = ok`) to re-solve an earlier matching fragment, Maude re-visits the deterministic fragment
/// (`re-solving` then `failure for condition fragment`). Trace-only — the result/count are unaffected.
/// Byte-exact vs the reference binary (verified separately); this pins the events in CI.
#[test]
fn trace_multi_fragment_backtrack_resolves_deterministic() {
    let mut r = repl();
    r.eval(
        "fmod BT is sorts E R B . ops a b c : -> E [ctor] . op _;_ : E E -> E [assoc] . \
         op f : E -> E . op g : E -> R . op ok : -> R [ctor] . ops tt ff : -> B [ctor] . \
         op test : E -> B . vars X Y Z : E . eq g(X) = ok . eq test(c) = tt . \
         ceq f(Z) = Y if X ; Y := Z /\\ g(X) = ok /\\ test(Y) = tt . endfm",
    );
    r.eval("set trace on .");
    let out = r.eval("red f(a ; b ; c) .").output;
    // The split (a, b c) passes g(X)=ok but fails test(b c)=tt, so the solver backtracks through the
    // deterministic g(X)=ok fragment — which Maude (and now we) re-solve and fail.
    assert!(
        out.contains(
            "*********** re-solving condition fragment\n\
             g(X) = ok\n\
             *********** failure for condition fragment\n\
             g(X) = ok\n"
        ),
        "deterministic re-solve on backtrack:\n{out}"
    );
    assert!(out.contains("result E: c"), "result (a ; b -> X, c -> Y): {out}");
}

/// Drive a multi-submission session the way the binary's stdin loop does (main.rs): buffer lines until
/// `input_complete`, then `eval` each submission. Returns the concatenated output.
fn run_session(input: &str) -> String {
    let mut r = repl();
    let mut out = String::new();
    let mut buffer = String::new();
    for line in input.lines() {
        buffer.push_str(line);
        buffer.push('\n');
        if r.input_complete(&buffer) {
            let ev = r.eval(&buffer);
            buffer.clear();
            if !ev.output.is_empty() {
                out.push_str(&ev.output);
                out.push('\n');
            }
            if ev.exit {
                break;
            }
        }
    }
    out
}

/// The `conformance/trace-*.maude` fixtures (the §1 spec modules) load through the REPL's stdin loop and
/// produce the expected trace. The byte-exact match against the reference binary is verified separately
/// (the doc-comment diff command); this is the in-repo regression guard.
#[test]
fn trace_fixtures_run_through_repl() {
    let eq = run_session(conformance_file!("trace-eq.maude"));
    assert!(
        eq.contains(
            "*********** equation\neq N + s M = s (N + M) .\nN --> s 0\nM --> 0\ns 0 + s 0\n--->\ns (s 0 + 0)\n"
        ),
        "trace-eq:\n{eq}"
    );

    let bi = run_session(conformance_file!("trace-builtin.maude"));
    assert!(bi.contains("(built-in equation for symbol _+_)\n2 + 3\n--->\n5\n"), "trace-builtin:\n{bi}");

    let mb = run_session(conformance_file!("trace-membership.maude"));
    assert!(
        mb.contains("*********** membership axiom\nmb g(X) : B .\nX --> a\nA: g(a) becomes B\n"),
        "trace-membership:\n{mb}"
    );

    let cond = run_session(conformance_file!("trace-conditional.maude"));
    assert!(cond.contains("*********** trial #1\nceq max(M, N) = N if M <= N = tt ."), "trial #1:\n{cond}");
    assert!(
        cond.contains("*********** failure #1") && cond.contains("*********** trial #2"),
        "backtrack #1->#2:\n{cond}"
    );
}

/// Pillar A-i: `rl` + `rewrite`/`continue` through the REPL, byte-matching the reference binary
/// (`conformance/rewrite.maude`). Reduce-then-rule-fair, the bound, the top-down `f(a)` traversal (7
/// steps), and the resumable `continue` (which resets the count).
#[test]
fn rewrite_command_through_repl() {
    let out = repl().eval(conformance_file!("rewrite.maude")).output;
    assert!(out.contains("rewrite in CHAIN : a .\nrewrites: 3 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: d"), "rewrite a:\n{out}");
    assert!(out.contains("rewrite [2] in CHAIN : a .\nrewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: c"), "rewrite [2] a:\n{out}");
    assert!(out.contains("rewrite in CHAIN : f(a) .\nrewrites: 7 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: d"), "rewrite f(a) (7 steps):\n{out}");
    // `rewrite [1] a .` -> b, then `continue 1 .` -> c (count reset to the 1 step done in the continue).
    assert!(out.contains("rewrite [1] in CHAIN : a .\nrewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: b\nrewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: c"), "[1] then continue:\n{out}");
}

/// `set trace on` + `rewrite` renders the rule step exactly as the reference: `*********** rule` + the
/// rule body + `empty substitution` + the `redex ---> result` tail.
#[test]
fn traced_rewrite_renders_rule_blocks() {
    let s = run_session(
        "mod CHAIN is sort S . ops a b c d : -> S . rl a => b . rl b => c . endm\n\
         set trace on .\n\
         rewrite a .",
    );
    assert!(s.contains("*********** rule\nrl a => b .\nempty substitution\na\n--->\nb"), "rule block 1:\n{s}");
    assert!(s.contains("*********** rule\nrl b => c .\nempty substitution\nb\n--->\nc"), "rule block 2:\n{s}");
    assert!(s.contains("rewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: c"), "tail:\n{s}");
}

/// Pillar A-ii: `frewrite` (position-fair) + frozen arguments, byte-matching the reference
/// (`conformance/frewrite.maude`). The essential fairness property (a bound spreads across positions,
/// unlike greedy `rewrite`), the unbounded normal form, the `(sort not calculated)` bounded stop, and
/// frozen-argument skipping.
#[test]
fn frewrite_command_through_repl() {
    let out = repl().eval(conformance_file!("frewrite.maude")).output;
    // Unbounded: all three positions reach `d` in 9 steps.
    assert!(out.contains("frewrite in FR : (a | a) | a .\nrewrites: 9 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: (d | d) | d"), "unbounded:\n{out}");
    // Fairness: greedy `rewrite [2]` drains one position; fair `frewrite [2]` spreads across two.
    assert!(out.contains("rewrite [2] in FR : (a | a) | a .\nrewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: (a | a) | c"), "greedy:\n{out}");
    assert!(out.contains("frewrite [2] in FR : (a | a) | a .\nrewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)\nresult (sort not calculated): (b | b) | a"), "fair + sort-not-calculated:\n{out}");
    // Frozen: a rule never rewrites inside f's (frozen) argument; g's argument IS rewritten.
    assert!(out.contains("frewrite in FR : f(a) .\nrewrites: 0 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: f(a)"), "frozen blocks:\n{out}");
    assert!(out.contains("frewrite in FR : g(a) .\nrewrites: 3 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: g(d)"), "non-frozen rewrites:\n{out}");
}

/// Pillar A-iii: conditional rules (`crl`) with equality / matching / sort-test fragments, byte-matching
/// the reference (`conformance/crl.maude`). First-applicable selection with condition backtracking.
#[test]
fn crl_command_through_repl() {
    let out = repl().eval(conformance_file!("crl.maude")).output;
    assert!(out.contains("rewrite in CRL : f(a) .\nrewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: g(a)"), "equality holds:\n{out}");
    assert!(out.contains("rewrite in CRL : f(b) .\nrewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: h(b)"), "backtrack to `:=`:\n{out}");
    assert!(out.contains("rewrite in CRL : k(a) .\nrewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: g(a)"), "sort-test holds:\n{out}");
    assert!(out.contains("rewrite in CRL : k(b) .\nrewrites: 0 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: k(b)"), "sort-test fails -> no rewrite:\n{out}");
}

/// A traced `crl` renders the rule trial / condition-fragment / backtrack stream exactly as the
/// reference: trial #1 fails its `X = a` fragment, then trial #2's `Y := X` succeeds and the rule fires.
#[test]
fn traced_crl_backtrack() {
    let s = run_session(
        "mod CRL is sort S . ops a b : -> S . ops f g h : S -> S [ctor] . vars X Y : S . \
         crl f(X) => g(X) if X = a . crl f(X) => h(Y) if Y := X . endm\n\
         set trace on .\n\
         rewrite f(b) .",
    );
    assert!(s.contains("*********** trial #1\ncrl f(X) => g(X) if X = a .\nX --> b"), "trial #1:\n{s}");
    assert!(s.contains("*********** failure for condition fragment\nX = a"), "fragment failure:\n{s}");
    assert!(s.contains("*********** failure #1"), "trial #1 fails:\n{s}");
    assert!(s.contains("*********** trial #2\ncrl f(X) => h(Y) if Y := X ."), "trial #2:\n{s}");
    assert!(s.contains("*********** success #2"), "trial #2 succeeds:\n{s}");
    assert!(s.contains("*********** rule\ncrl f(X) => h(Y) if Y := X .\nX --> b\nY --> b\nf(b)\n--->\nh(b)"), "rule fires:\n{s}");
}

/// Pillar A-iv: `search` over the state-transition graph, byte-matching the reference
/// (`conformance/search.maude`). The four arrows, hash-consing (b,c collapse onto one d state),
/// `such that`, and a lazy bounded `[1]` + `continue` (c generated post-reset shows rewrites 1).
#[test]
fn search_command_through_repl() {
    let out = repl().eval(conformance_file!("search.maude")).output;
    // =>1: exactly the one-step successors b, c (states 3, rewrites 2 at the end).
    assert!(out.contains("search in NDET : a =>1 X .\n\nSolution 1 (state 1)\nstates: 2  rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)\nX --> b"), "=>1 sol1:\n{out}");
    assert!(out.contains("Solution 2 (state 2)\nstates: 3  rewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)\nX --> c\n\nNo more solutions.\nstates: 3  rewrites: 2"), "=>1 sol2+end:\n{out}");
    // =>* includes the initial state 0 at rewrites 0.
    assert!(out.contains("search in NDET : a =>* X .\n\nSolution 1 (state 0)\nstates: 1  rewrites: 0 in 0ms cpu (0ms real) (~ rewrites/second)\nX --> a"), "=>* state 0:\n{out}");
    // =>! finds only the normal form e (whole graph explored: states 5, rewrites 5).
    assert!(out.contains("search in NDET : a =>! X .\n\nSolution 1 (state 4)\nstates: 5  rewrites: 5 in 0ms cpu (0ms real) (~ rewrites/second)\nX --> e\n\nNo more solutions."), "=>! e:\n{out}");
    // such that filters to state 3 (d), but exploration still finishes the whole graph.
    assert!(out.contains("such that X = d .\n\nSolution 1 (state 3)\nstates: 4  rewrites: 3 in 0ms cpu (0ms real) (~ rewrites/second)\nX --> d\n\nNo more solutions.\nstates: 5  rewrites: 5"), "such-that:\n{out}");
    // [1] then continue: the second solution c is generated lazily during continue, so rewrites: 1.
    assert!(out.contains("search [1] in NDET : a =>+ X .\n\nSolution 1 (state 1)\nstates: 2  rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)\nX --> b\n\nSolution 2 (state 2)\nstates: 3  rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)\nX --> c"), "bounded+continue:\n{out}");
}

/// `show path N` and `show search graph` for the last search, byte-matching the reference.
#[test]
fn search_show_path_and_graph() {
    let s = run_session(
        "mod NDET is sort St . ops a b c d e : -> St . var X : St . \
         rl a => b . rl a => c . rl b => d . rl c => d . rl d => e . endm\n\
         search a =>! X .\n\
         show path 4 .\n\
         show search graph .",
    );
    assert!(
        s.contains("state 0, St: a\n===[ rl a => b . ]===>\nstate 1, St: b\n===[ rl b => d . ]===>\nstate 3, St: d\n===[ rl d => e . ]===>\nstate 4, St: e"),
        "show path:\n{s}"
    );
    assert!(
        s.contains("state 0, St: a\narc 0 ===> state 1 (rl a => b .)\narc 1 ===> state 2 (rl a => c .)"),
        "show graph state 0:\n{s}"
    );
    assert!(s.contains("state 3, St: d\narc 0 ===> state 4 (rl d => e .)"), "show graph state 3:\n{s}");
}

/// Pillar A-v: the rewrite-condition fragment `crl ... if t => p` (a nested =>* reachability search),
/// byte-matching the reference (`conformance/rewrite-cond.maude`). =>* semantics (0-step match), the
/// search rewrite count, and a fresh variable bound from the reached state.
#[test]
fn rewrite_condition_through_repl() {
    let out = repl().eval(conformance_file!("rewrite-cond.maude")).output;
    // X => c holds via a->b->c (2 search rewrites) + the rule itself = 3.
    assert!(out.contains("rewrite in REACH : f(a) .\nrewrites: 3 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: done"), "reach a:\n{out}");
    // c matches c at 0 steps -> just the rule fires (1 rewrite).
    assert!(out.contains("rewrite in REACH : f(c) .\nrewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: done"), "reach c (0 steps):\n{out}");
    // stuck reaches nothing matching c -> condition fails, no rewrite.
    assert!(out.contains("rewrite in REACH : f(stuck) .\nrewrites: 0 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: f(stuck)"), "unreachable:\n{out}");
    // The target pattern s(Y) binds Y from a reached state — matching the reference byte-for-byte (Y = z,
    // 2 rewrites). The exact `=>` search order is Maude's; we reproduce it (verified across cases).
    assert!(out.contains("rewrite in BIND : f(s(s(z))) .\nrewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)\nresult N: g(z)"), "binding:\n{out}");
}

/// A rewrite condition (`=>`) in an equation/membership is rejected — it is legal only in a rule.
#[test]
fn rewrite_condition_rejected_in_equation() {
    let out = repl()
        .eval("fmod E is sort S . ops a b : -> S . var X : S . ceq a = b if X => b . endfm")
        .output;
    assert!(out.contains("rewrite condition (`=>`) is only allowed in a rule"), "rejection: {out}");
}

/// On-the-fly colon variables `X:Sort` (one token) parse anywhere a term is expected — in an `eq`
/// (mixed with declared vars), a `match` pattern, and a `search` goal — without a `var` declaration. The
/// whole token is the variable name, echoed back with its sort.
#[test]
fn on_the_fly_colon_variables() {
    let mut r = repl();
    r.eval(
        "fmod N is sort Nat . op z : -> Nat . op s_ : Nat -> Nat [ctor] . op _+_ : Nat Nat -> Nat . \
         op dbl : Nat -> Nat . vars M N : Nat . eq N + z = N . eq N + s M = s (N + M) . \
         eq dbl(N:Nat) = N:Nat + N:Nat . endfm",
    );
    assert!(r.eval("red dbl(s s z) .").output.contains("result Nat: s s s s z"), "on-the-fly var in an eq");
    assert!(r.eval("match X:Nat <=? s z .").output.contains("X:Nat --> s z"), "on-the-fly var in match, with sort");
    // …and in a system module's search goal.
    r.eval("mod S is sort T . ops p q : -> T . rl p => q . endm");
    let s = r.eval("search p =>1 Y:T .").output;
    assert!(s.contains("Y:T --> q"), "on-the-fly var in a search goal:\n{s}");
}

/// A rule in a functional module (`fmod`) is rejected — rules belong only to system modules (`mod`).
#[test]
fn rule_in_fmod_is_rejected() {
    let out = repl()
        .eval("fmod F is sort S . ops a b : -> S . rl a => b . endfm")
        .output;
    assert!(out.contains("not allowed in a functional module"), "rejection: {out}");
}

/// A single `eval` of a file that mixes a module, a `set trace on .` meta-command, and a traced command
/// — previously the mid-stream `set` broke the whole-file parse (it is now split into per-statement
/// dispatch). The `show`/`continue` etc. across statements share the persistent REPL state.
#[test]
fn eval_mixed_file_with_meta_commands() {
    let out = repl()
        .eval(
            "mod CH is sort S . ops a b c : -> S . rl a => b . rl b => c . endm\n\
             set trace on .\n\
             rewrite a .",
        )
        .output;
    assert!(out.contains("*********** rule\nrl a => b ."), "traced rule from a one-shot file load:\n{out}");
    assert!(out.contains("rewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: c"), "result:\n{out}");
}

/// The multi-line buffer boundary: a command terminator / a closed module complete; an open module body
/// or a terminator-less line keep buffering; a bare `quit` completes.
#[test]
fn input_complete_boundaries() {
    let mut r = repl();
    assert!(r.input_complete("red x ."), "command terminator");
    assert!(r.input_complete("fmod M is sort S . endfm"), "closed module");
    assert!(!r.input_complete("fmod M is sort S ."), "open module body keeps buffering");
    assert!(!r.input_complete("red x"), "no terminator");
    assert!(r.input_complete("quit"), "bare quit");
    assert!(r.input_complete("q"), "bare q");
    assert!(!r.input_complete(""), "empty");
    assert!(!r.input_complete("   \n  "), "whitespace");
}

