//! `eval`-driven tests — the REPL with no terminal. Each feeds input submissions and asserts the output,
//! re-validating the whole pipeline (parse → flatten → build → reduce/match → print) through the shell.

use super::*;

fn repl() -> Repl {
    Repl::new(false) // uncolored, for deterministic output
}

macro_rules! conformance_file {
    ($n:expr) => {
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../conformance/",
            $n
        ))
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
    let out = repl()
        .eval(conformance_file!("import-diamond.maude"))
        .output;
    assert!(out.contains("rewrites: 12"), "count: {out}");
    assert!(out.contains("result N: s(s(s(s(s(0)))))"), "value: {out}");
}

/// Renaming through the REPL: `top(e) = box(e) = e`, sort renamed to `Item`.
#[test]
fn import_renaming_through_repl() {
    let out = repl()
        .eval(conformance_file!("import-renaming.maude"))
        .output;
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
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "LIST builds: {out}"
    );
    let lines: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("result ") || l.starts_with("rewrites:"))
        .collect();
    // Pair each `rewrites:`/`result` into `[count] sort: value`, then compare the whole sequence.
    let got: Vec<String> = lines
        .chunks(2)
        .map(|c| {
            let n = c[0]
                .trim_start_matches("rewrites: ")
                .split(' ')
                .next()
                .unwrap_or("?");
            format!("[{n}] {}", c[1].trim_start_matches("result "))
        })
        .collect();
    assert_eq!(
        got,
        vec![
            "[6] Bool: true",           // occurs(2, 1 2 3)
            "[9] Bool: true",           // occurs(3, 1 2 3)  — recurses to the singleton
            "[10] Bool: false",         // occurs(5, 1 2 3)  — recurses past the singleton to nil
            "[3] Bool: true",           // occurs(7, 7)      — singleton subject
            "[12] NzNat: 5",            // size(1 2 3 4 5)
            "[4] NzNat: 1",             // size(7)           — collapse
            "[2] Zero: 0",              // size(nil)
            "[6] NeList{Nat}: 4 3 2 1", // reverse(1 2 3 4)
            "[3] NzNat: 7",             // reverse(7)
            "[2] List{Nat}: nil",       // reverse(nil)
            "[1] NzNat: 3",             // last(1 2 3)
            "[1] NeList{Nat}: 1 2",     // front(1 2 3)
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
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "SET builds: {out}"
    );
    let lines: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("result ") || l.starts_with("rewrites:"))
        .collect();
    let got: Vec<String> = lines
        .chunks(2)
        .map(|c| {
            let n = c[0]
                .trim_start_matches("rewrites: ")
                .split(' ')
                .next()
                .unwrap_or("?");
            format!("[{n}] {}", c[1].trim_start_matches("result "))
        })
        .collect();
    assert_eq!(
        got,
        vec![
            "[1] Bool: false",            // true and-then false
            "[1] Bool: true",             // false or-else true
            "[1] Bool: true",             // 2 in (1, 2, 3)
            "[1] Bool: false", // 5 in (1, 2, 3)   — absent, recurses to singleton (non-linear)
            "[1] Bool: true",  // 7 in 7           — singleton subject (collapse)
            "[8] NzNat: 3",    // | (1, 2, 3) |
            "[4] NzNat: 1",    // | 7 |
            "[6] Bool: false", // (1, 5) subset (1, 2, 3)
            "[7] Bool: true",  // (1, 2) subset (1, 2, 3)
            "[2] NeSet{Nat}: 1, 3", // delete(2, (1, 2, 3))
            "[1] NeSet{Nat}: 1, 2, 3, 4", // insert(4, (1, 2, 3))
            "[1] NeSet{Nat}: 1, 2, 3, 4", // union((1, 2), (3, 4))
            "[11] NeSet{Nat}: 2, 3", // intersection((1, 2, 3), (2, 3, 4))
            "[11] NeSet{Nat}: 1, 3", // (1, 2, 3) \ (2, 4)
        ],
        "SET ops: {out}"
    );
}

/// Helper for the prelude container fixtures: pair each `rewrites:`/`result` line into `[count] value`.
/// Each `[rewrite-count] sort: value` result, with the **full** value — a `format`-attribute result spans
/// continuation lines (a substitution's `_<-_` newline-indents each binding), captured up to the next
/// command echo / `rewrites:` line, so the multi-line layout is compared verbatim against the reference.
/// Per `srewrite`/`dsrewrite` command, the ordered solution values joined by ` ; ` (or `(no solution)`).
fn strategy_solutions(out: &str) -> Vec<String> {
    let mut res = Vec::new();
    let mut cur: Vec<String> = Vec::new();
    let (mut active, mut none) = (false, false);
    for line in out.lines() {
        if line.starts_with("srewrite ") || line.starts_with("dsrewrite ") {
            if active {
                res.push(if none {
                    "(no solution)".to_string()
                } else {
                    cur.join(" ; ")
                });
            }
            cur = Vec::new();
            active = true;
            none = false;
        } else if let Some(v) = line.strip_prefix("result ") {
            if let Some(idx) = v.find(": ") {
                cur.push(v[idx + 2..].to_string());
            }
        } else if line.starts_with("No solution.") {
            none = true;
        }
    }
    if active {
        res.push(if none {
            "(no solution)".to_string()
        } else {
            cur.join(" ; ")
        });
    }
    res
}

/// Phase 2.4 — the core strategy language. `srewrite`/`dsrewrite` over `STRAT-CORE` exercising
/// `idle`/`fail`/`all`/rule-by-label/`top`/`one`/`;`/`|`/`*`/`+`/`!`/`?:`(+`try`/`not`)/`match`/`amatch`:
/// the solution values + order are byte-identical to the reference. (The per-solution `srewrite` rewrite
/// count follows the BFS snapshot — see `fable-audit.md` — so this pins the solution values/structure.)
#[test]
fn strategy_core_through_repl() {
    let out = repl().eval(conformance_file!("strategy.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error:"),
        "strategy core builds/runs: {out}"
    );
    assert_eq!(
        strategy_solutions(&out),
        vec![
            "b",             // r1
            "b ; c",         // r1 | r2
            "d",             // r1 ; r3
            "a ; b",         // r1 * (zero-or-more)
            "b ; c",         // all
            "a",             // idle
            "(no solution)", // fail
            "b",             // top(r1)
            "(no solution)", // match b — a doesn't match b
            "a",             // match a — succeeds, returns the subject
            "(no solution)", // amatch d — d occurs nowhere in a
            "d",             // r1 ? r3 : r2 — r1 succeeds → r3 on b
            "(no solution)", // r2 ? r3 : r4 — r2 succeeds → r3 on c fails (no γ)
            "b ; c",         // (r1 | r2) ! — normalization to the strategy's normal forms
            "b",             // r1 +
            "b",             // try(r1)
            "a",             // not(fail)
            "d",             // (r1 ; r3) | (r2 ; r4)
            "b",             // one(r1 | r2) — only the first solution
            "b ; c",         // dsrewrite r1 | r2
            "d",             // dsrewrite (r1 | r2) ; r3
            // Phase C — strategy definitions (`sd`) + calls. `go := r1 ; r3`, `go2 := go | r2`, and the
            // recursive `reach := idle | ((r1|r2|r3|r4) ; reach)` (cycle-detected). `dsrewrite` for the
            // multi-solution calls (the fair `srewrite` order is the BFS follow-on, fable-audit.md).
            "d",             // srewrite go
            "d ; c",         // dsrewrite go2
            "a ; b ; d ; c", // dsrewrite reach — all states reachable from a (recursion terminates)
            // Phase D — matchrew/amatchrew, conditional rules (equality + rewrite-condition substrategies),
            // application substitution `L[x <- t]`, the `xmatch` test, and parameterized strategy calls.
            "f(b, c)",                               // matchrew by X using r1, Y using r2
            "f(b, b) ; f(c, b)",                     // matchrew by X using (r1|r2), Y using r1
            "f(b, b) ; f(c, b) ; f(b, c) ; f(c, c)", // dsrewrite matchrew — full cartesian product
            "f(b, a)",           // matchrew by X using r1 — partial by-list (Y kept)
            "(no solution)",     // matchrew f(b,a) … X using r1 — r1 fails on b
            "f(b, a) ; f(a, b)", // amatchrew X by X using r1 — anywhere
            "g(b)",              // wrap{r1} — rewrite condition solved by r1
            "g(c)",              // wrap{r2}
            "g(b) ; g(c)",       // dsrewrite wrap{r1 | r2}
            "(no solution)",     // wrap — bare rewrite-conditional rule cannot apply
            "d",                 // eqc — equality condition holds
            "(no solution)",     // eqf — equality condition fails
            "f(b, a)",           // swap — plain
            "f(b, a)",           // swap[X <- a] — consistent constraint
            "(no solution)",     // swap[X <- b] — inconsistent with the match
            "a . a . a",         // xmatch X . Y — extension test returns the subject
            "a . a . a",         // match X . Y — whole-match test returns the subject
            "b",                 // s2(a) — parameterized call
            "b",                 // go3 := s2(a)
            "b",                 // mtest(b) := match b — parameter used in a pattern
            "(no solution)",     // mtest(a) := match a — fails on subject b
        ],
        "strategy solutions: {out}"
    );
}

/// Per `srewrite`/`dsrewrite` command, each solution as `value[cumulative-rewrite-count]` joined by ` ; `
/// (or `(no solution)`). The `rewrites:` line precedes each `result`, so each result pairs with the most
/// recent count. Pins the fair-`srewrite` solution ORDER **and** per-solution count (unlike
/// [`strategy_solutions`], which pins only values).
fn strategy_value_counts(out: &str) -> Vec<String> {
    let mut res = Vec::new();
    let mut cur: Vec<String> = Vec::new();
    let (mut active, mut rw) = (false, String::new());
    for line in out.lines() {
        if line.starts_with("srewrite ") || line.starts_with("dsrewrite ") {
            if active {
                res.push(cur.join(" ; "));
            }
            cur = Vec::new();
            active = true;
        } else if let Some(n) = line.strip_prefix("rewrites: ") {
            rw = n.split(' ').next().unwrap_or("?").to_string();
        } else if let Some(v) = line.strip_prefix("result ") {
            if let Some((_, val)) = v.split_once(": ") {
                cur.push(format!("{val}[{rw}]"));
            }
        } else if line.starts_with("No solution.") {
            cur.push("(no solution)".to_string());
        }
    }
    if active {
        res.push(cur.join(" ; "));
    }
    res
}

/// Phase 2.4 — fair `srewrite` (and `dsrewrite`) solution ORDER **and** per-solution cumulative rewrite
/// COUNT, byte-identical to Maude 3.5.1. These are the unequal-depth interleavings the old eager depth-first
/// enumerator got wrong: the fair FIFO round-robin emits the shorter derivation first while DFS explores
/// left-fully, and the per-solution count tracks the exact process schedule (a decompose step costs a turn
/// but no rewrite; unions are n-ary). The process-queue + task-tree executor reproduces both.
#[test]
fn strategy_fair_counts_through_repl() {
    let out = repl().eval(conformance_file!("strategy-fair.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error:"),
        "fair strategy builds/runs: {out}"
    );
    assert_eq!(
        strategy_value_counts(&out),
        vec![
            "c[2] ; g[4]", // srew (r1;p;pp) | r2 — fair emits the shorter derivation (c) first
            "g[3] ; c[4]", // dsrew — left branch explored fully first
            "c[1] ; d[5] ; g[6]", // srew r2 | (r1;p) | (r1;p;pp) — n-ary union decompose timing
            "c[1] ; d[3] ; g[6]", // dsrew
            "d[4] ; e[4]", // srew (r1;p) | (r2;q) — equal depth, both at the level's final count
            "a[0] ; b[2] ; c[2]", // srew (r1|r2)* — reachable set, fair count snapshot
            "a[0] ; b[1] ; c[2]", // dsrew (r1|r2)* — depth-first count snapshot
            "c[2] ; b[2]", // srew r2 | r1 — the 2nd branch rewrites before the 1st emits
            "e[5] ; g[5]", // srew (r1|r2) ; (p ? pp : q) — interleaved branch sub-tasks
            "b[1] ; c[2]", // dsrew (r1|r2)! — normalize, depth-first
        ],
        "fair srewrite order+count: {out}"
    );
}

/// TNK-021 — every command echo is executable source for the same strategy tree. Besides the
/// precedence boundaries, right-nested `;`/`|` pin grouping that a flat left-associative echo would lose.
/// Re-executing each emitted strategy must retain solution order and cumulative rewrite counts.
#[test]
fn strategy_echoes_round_trip_through_repl() {
    let mut r = repl();
    let setup = r.eval(
        r#"
smod STRAT-ECHO-ROUNDTRIP is
  sort S .
  ops a b c d : -> S [ctor] .
  op f : S S -> S [ctor] .
  op g : S -> S [ctor] .
  rl [r1] : a => b .
  rl [r2] : a => c .
  rl [r3] : b => d .
  rl [r4] : c => d .
  crl [wrap] : a => g(Z:S) if a => Z:S .
endsm
"#,
    );
    assert!(
        !setup.output.contains("error") && !setup.output.contains("no parse"),
        "strategy round-trip module: {}",
        setup.output
    );

    let cases = [
        ("a", "(r1 | r2) !", "(r1 | r2)!"),
        ("a", "(r1 | r2) ; (r3 | r4)", "(r1 | r2) ; (r3 | r4)"),
        ("a", "(r1 | r2) ? r3 : r4", "r1 | r2 ? r3 : r4"),
        ("a", "r3 ? r4 : (r1 | r2)", "r3 ? r4 : r1 | r2"),
        ("a", "(r1 ? r3 : r4) | r2", "(r1 ? r3 : r4) | r2"),
        (
            "a",
            "try((r1 | r2) ; (r3 | r4))",
            "try((r1 | r2) ; (r3 | r4))",
        ),
        ("a", "not((r1 | r2) ; fail)", "not((r1 | r2) ; fail)"),
        ("a", "top(r1) | r2", "top(r1) | r2"),
        ("a", "r1 | (r2 | fail)", "r1 | (r2 | fail)"),
        ("a", "r1 ; (r3 ; idle)", "r1 ; (r3 ; idle)"),
        ("a", "(r1 +) *", "r1 + *"),
        ("a", "wrap{r1 | r2}", "wrap{r1 | r2}"),
        (
            "f(a, a)",
            "matchrew f(X:S, Y:S) by X:S using (r1 | r2), Y:S using r1",
            "matchrew f(X:S, Y:S) by X:S using (r1 | r2), Y:S using r1",
        ),
    ];

    for (subject, original, expected_echo) in cases {
        let first = r
            .eval(&format!("srewrite {subject} using {original} ."))
            .output;
        assert!(
            !first.contains("error") && !first.contains("no parse"),
            "original `{original}`: {first}"
        );
        let header = first
            .split_once("\n\n")
            .map_or(first.as_str(), |(header, _)| header);
        let echoed = header
            .split_once(" using ")
            .and_then(|(_, strategy)| strategy.strip_suffix(" ."))
            .unwrap_or_else(|| panic!("malformed echo for `{original}`: {header}"));
        // Mixfix `format` attributes may make the subject/strategy command header multiline; newlines are
        // source whitespace, so compare and replay its token-equivalent one-line spelling.
        let emitted = echoed.split_whitespace().collect::<Vec<_>>().join(" ");
        assert_eq!(emitted, expected_echo, "echo for `{original}`");

        let replay = r
            .eval(&format!("srewrite {subject} using {emitted} ."))
            .output;
        assert!(
            !replay.contains("error") && !replay.contains("no parse"),
            "replayed `{emitted}`: {replay}"
        );
        assert_eq!(
            strategy_value_counts(&first),
            strategy_value_counts(&replay),
            "behavior changed after echo/reparse: `{original}` -> `{emitted}`"
        );
    }
}

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
            while j < lines.len()
                && !lines[j].starts_with("reduce ")
                && !lines[j].starts_with("rewrites:")
            {
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
/// (`sortLeq`/…/`maximalAritySet`), `metaParse`/`metaPrettyPrint`, and `metaWellFormed*`. (The `=>!`
/// `metaSearch` count now matches the oracle — the B2b normal-form-confirmation snapshot fix, §3.3; the
/// `=>+` sol-1 count still pins tnk's BFS-snapshot value, a separate parallel-odometer divergence in
/// `fable-audit.md` §3.3 — value/sort/reachability match.)
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
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "META tower builds: {out}"
    );
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
            "[3] ResultPair: {'c.Elt, 'Elt}", // metaRewrite unbounded: a=>b=>c
            "[2] ResultPair: {'b.Elt, 'Elt}", // metaRewrite [1]: one step a=>b
            "[3] ResultPair: {'c.Elt, 'Elt}", // metaFrewrite gas 1: a=>b=>c
            "[2] Assignment: \n  'N:Nat <- 's_^4['0.Zero]", // metaMatch: s_(N) <-> s^5(0)
            "[2] Substitution?: (noMatch).Substitution?", // metaMatch: _+_ vs s^5 — no match
            "[2] ResultTriple: {'b.Elt, 'Elt, \n  'X:Elt <- 'b.Elt}", // metaSearch =>+ sol 0: a=>b
            "[3] ResultTriple: {'c.Elt, 'Elt, \n  'X:Elt <- 'c.Elt}", // metaSearch =>+ sol 1: a=>c (ab)
            "[4] ResultTriple: {'c.Elt, 'Elt, (none).Substitution}", // metaSearch =>! normal form c: snapshot at nf-confirmation (oracle rewrites: 4; fable-audit.md §3.3 B2b)
            // metaApply: the labelled rule `unwrap` (f(N) => N) at the top, its binding, or failure.
            "[2] ResultTriple: {'s_^3['0.Zero], 'NzNat, \n  'N:Nat <- 's_^3['0.Zero]}", // apply at top
            "[1] ResultTriple?: (failure).ResultTriple?", // solution 1 — past the last
            "[1] ResultTriple?: (failure).ResultTriple?", // no top match (subject is s^3(0))
            // metaXmatch (extension match → {subst, context}) and metaXapply (rule at a position →
            // {term, type, subst, context}). The hole `[]` marks the matched/rewritten position: `[]` at
            // the top, `'f[[]]` at the inner f; the substitution's `_<-_` newline-indents (`format`).
            "[2] MatchPair: {\n  'N:Nat <- 's_^4['0.Zero], []}", // metaXmatch s_(N) <-> s^5(0)
            "[2] MatchPair?: (noMatch).MatchPair?",              // metaXmatch _+_ vs s^5 — no match
            "[2] Result4Tuple: {'f['0.Zero], 'Nat, \n  'N:Nat <- 'f['0.Zero], []}", // xapply at top
            "[2] Result4Tuple: {'f['0.Zero], 'Nat, \n  'N:Nat <- '0.Zero, 'f[[]]}", // xapply at inner f
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
            "[2] Bool: true",                      // sortLeq(Zero, Nat)
            "[2] Bool: false",                     // sameKind(Nat, Bool)
            "[2] Sort: 'NzNat",                    // leastSort(2 + 3)
            "[2] NeSortSet: 'NzNat ; 'Zero",       // lesserSorts(Nat)
            "[2] Sort: 'NzNat",                    // glbSorts(Nat, NzNat)
            "[2] Sort: 'Nat",                      // completeName(Nat)
            "[2] Kind: '`[Nat`]",                  // getKind(Nat)
            "[2] NeKindSet: '`[Bool`] ; '`[Nat`]", // getKinds
            "[2] Sort: 'Nat",                      // maximalSorts([Nat])
            "[2] NeSortSet: 'NzNat ; 'Zero",       // minimalSorts([Nat])
            "[2] NeTypeList: 'Nat 'Nat",           // maximalAritySet(_+_)
            // wellFormed: module/term/substitution. The ill-typed term/binding return false.
            "[2] Bool: true",  // wellFormed(2 + 3)
            "[2] Bool: false", // wellFormed(true + 0) — ill-typed
            "[2] Bool: true",  // wellFormed(X:Nat <- 0)
            "[2] Bool: false", // wellFormed(X:Nat <- true) — kind clash
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
            "[1] Import: protecting 'NAT .", // upImports
            "[1] NeSortSet: 'Bar ; 'Foo",    // upSorts (own)
            "[1] OpDeclSet: op 'c : nil -> 'Foo [ctor] .\n\
             op 'f : 'Foo 'Nat -> 'Bar [ctor] .\nop 'g : 'Bar -> 'Bar [none] .", // upOpDecls
            "[1] Equation: ceq 'a.Elt = 'b.Elt if 'a.Elt = 'b.Elt [none] .", // upEqs (conditional)
            "[1] RuleSet: rl 'a.St => 'b.St [label('r1)] .\n\
             crl 'b.St => 'c.St if 'b.St = 'b.St [label('r2)] .", // upRls
            // upTerm reduces its argument then ups it; downTerm builds (the ambient reduces), returning
            // the default `99` when the meta-term is unresolvable.
            "[2] GroundTerm: 's_^3['0.Zero]", // upTerm(1 + 2)
            "[1] NzNat: 4",                   // downTerm(s^4(0), 0)
            "[1] NzNat: 99",                  // downTerm(bogus, 99) → default
            // metaParse parses (no reduce) → {term, sort}; noParse(n) on failure. metaPrettyPrint renders
            // a term to a QidList via the format-aware printer.
            "[2] ResultPair: {'_+_['s_['0.Zero], 's_^2['0.Zero]], 'NzNat}", // metaParse(1 + 2)
            "[2] ResultPair?: noParse(0)",                                  // metaParse(foo bar)
            "[3] NeTypeList: '2 '+ '3", // metaPrettyPrint(2 + 3)
            // upView decomposes a view: header, from/to module exprs, and its sort/op maps.
            "[1] View: view 'S4-V from 'TRIV to 'NAT is\n  sort 'Elt to 'Nat .\n  none\n  none\nendv",
            // Stage 5 — the symbolic/SMT/strategy descent is declared (the tower loads) but stays INERT:
            // it reduces to OUR kind-level term, never misfiring, until the Phase-3.2/3.3 (D6/D7) and
            // strategy (Phase 2.4) backends land. (These two pin our inert result, *not* the reference's —
            // the reference computes `none` for a strat-free module; see fable-audit.md. The symbolic/SMT ops go
            // through the same exhaustive `=> None` arm.)
            "[1] StratDeclSet: (none).StratDeclSet",
            "[1] StratDefSet: (none).StratDefSet",
        ],
        "META tower reduces: {out}"
    );
}

/// LEXICAL's two quoted-identifier hooks dispatch through the upper-layer descent seam: `tokenize`
/// constructs the real AU QidList (including punctuation/backquote canonicalization), and `printTokens`
/// emits Maude's byte-level spacing/control semantics. Values and one-rewrite counts are the 3.5.1 oracle's.
#[test]
fn lexical_token_hooks_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(
            r#"fmod LEXICAL is
  protecting QID-LIST .
  op printTokens : QidList -> String
    [special (id-hook QuotedIdentifierOpSymbol (printTokens)
              op-hook stringSymbol (<Strings> : ~> String)
              op-hook quotedIdentifierSymbol (<Qids> : ~> Qid)
              op-hook nilQidListSymbol (nil : ~> QidList)
              op-hook qidListSymbol (__ : QidList QidList ~> QidList))] .
  op tokenize : String -> QidList
    [special (id-hook QuotedIdentifierOpSymbol (tokenize)
              op-hook stringSymbol (<Strings> : ~> String)
              op-hook quotedIdentifierSymbol (<Qids> : ~> Qid)
              op-hook nilQidListSymbol (nil : ~> QidList)
              op-hook qidListSymbol (__ : QidList QidList ~> QidList))] .
endfm
red in LEXICAL : tokenize("") .
red in LEXICAL : tokenize("alpha") .
red in LEXICAL : tokenize("alpha beta gamma") .
red in LEXICAL : tokenize("f(a,b) _+_ `[ x`y") .
red in LEXICAL : tokenize("--- not a comment *** neither") .
red in LEXICAL : tokenize("ab\
cd") .
red in LEXICAL : tokenize("café λ") .
red in LEXICAL : printTokens(nil) .
red in LEXICAL : printTokens('alpha) .
red in LEXICAL : printTokens('f '`( 'a '`, 'b '`) '`[ '`] '`{ '`} '_+_) .
red in LEXICAL : printTokens('\n '\t '\s '\\) .
fmod LEXICAL-PARSE is
  sorts List Elt .
  subsort Elt < List .
  op __ : List List -> List [assoc] .
endfm
red in META-LEVEL : metaParse(['LEXICAL-PARSE], none, 'A:List 'B:List, anyType) .
red in META-LEVEL : metaParse(['LEXICAL-PARSE], 'A:List ; 'B:List, 'A 'B, anyType) .
"#,
        )
        .output;
    assert_eq!(
        prelude_results(&out),
        vec![
            "[1] QidList: nil",
            "[1] Qid: 'alpha",
            "[1] NeQidList: 'alpha 'beta 'gamma",
            "[1] NeQidList: 'f '`( 'a '`, 'b '`) '_+_ '`[ 'x`y",
            "[1] NeQidList: '--- 'not 'a 'comment '*** 'neither",
            "[1] Qid: 'abcd",
            "[1] NeQidList: 'café 'λ",
            "[1] String: \"\"",
            "[1] String: \"alpha\"",
            "[1] String: \"f (a ,b )[]{ }_+_\"",
            "[1] String: \"\\n\\t \\\\\"",
            "[2] ResultPair: {'__['A:List, 'B:List], 'List}",
            "[2] ResultPair: {'__['A:List, 'B:List], 'List}",
        ],
        "LEXICAL hooks: {out}"
    );
}

/// Modern (Qid-family) free order-sorted `metaUnify` indexes distinct maximal-lower-sort unifiers in
/// Maude order, then returns the typed exhaustion sentinel. This deliberately excludes AU and variants.
#[test]
fn modern_free_meta_unify_indices_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(
            r#"fmod FREE-MULTI is
  sorts A B C D Top .
  subsorts C D < A B < Top .
endfm
red in META-LEVEL : metaUnify(['FREE-MULTI], 'X:A =? 'Y:B, '%, 0) .
red in META-LEVEL : metaUnify(['FREE-MULTI], 'X:A =? 'Y:B, '%, 1) .
red in META-LEVEL : metaUnify(['FREE-MULTI], 'X:A =? 'Y:B, '%, 2) .
"#,
        )
        .output;
    assert_eq!(
        prelude_results(&out),
        vec![
            "[2] UnificationPair: {\n  'X:A <- '#1:C ; \n  'Y:B <- '#1:C, '#}",
            "[2] UnificationPair: {\n  'X:A <- '#1:D ; \n  'Y:B <- '#1:D, '#}",
            "[2] UnificationPair?: (noUnifier).UnificationPair?",
        ],
        "modern free metaUnify indices: {out}"
    );
}

/// Container milestone — the real prelude's `MAP{Nat, Nat}` loads and reduces byte-identically. Proves
/// two-parameter instantiation, the `[Y$Elt]` kind range (via `inst_sort`), and the `id:`-attribute
/// parse fix (an `_,_ [assoc comm id: empty prec 121]` keeps its prec, so a `_|->_` entry parses as an
/// argument). Values/sorts/counts are the reference binary's.
#[test]
fn prelude_map_through_repl() {
    let out = repl().eval(conformance_file!("prelude-map.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "MAP builds: {out}"
    );
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
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "ARRAY builds: {out}"
    );
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
    assert!(
        !out.contains("no parse"),
        "the shadowed prefix application must parse: {out}"
    );
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec!["result T: e e", "result T: e", "result S: a"],
        "shadow values: {out}"
    );
}

/// B-i: a theory loads through the REPL end-to-end — it becomes current, its `[nonexec]` axiom does NOT
/// fire (`e < e` stays, 0 rewrites), and an ordinary theory equation does (`id(e) = e`, 1 rewrite).
/// Values/counts are the reference binary's.
#[test]
fn theory_nonexec_through_repl() {
    let out = repl()
        .eval(conformance_file!("theory-nonexec.maude"))
        .output;
    assert!(out.contains("reduce in ELT-ORD :"), "header: {out}");
    assert!(
        out.contains("result Bool: e < e"),
        "nonexec not applied: {out}"
    );
    assert!(out.contains("result Elt: e"), "exec eq fires: {out}");
    assert!(out.contains("rewrites: 0"), "nonexec count: {out}");
    assert!(out.contains("rewrites: 1"), "exec count: {out}");
}

/// B-i: a multi-line theory is buffered as ONE submission by `input_complete` (which recognizes
/// `fth`/`endfth`), then entered and made current — the interactive multi-line boundary for theories.
#[test]
fn theory_entry_is_one_submission_and_current() {
    let mut r = repl();
    assert!(
        !r.input_complete("fth TRIV is\n"),
        "open theory keeps buffering"
    );
    assert!(
        !r.input_complete("fth TRIV is\n  sort Elt .\n"),
        "a `.` inside an open theory is not the end"
    );
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
    assert!(
        r.eval("show views .").output.contains("ToNum"),
        "show views lists it"
    );
    let shown = r.eval("show view ToNum .").output;
    assert_eq!(
        shown,
        "view ToNum from TRIV to NUM is\n  sort Elt to N .\nendv"
    );
}

/// B-iii: a parameterized module builds and reduces through the REPL — it echoes as its bare base name
/// (`CTR`, not `CTR{X}`) and its results print with structured sorts (`Ctr{X}` / least sort `NzCtr{X}`).
#[test]
fn parameterized_module_through_repl() {
    let out = repl().eval(conformance_file!("param-module.maude")).output;
    assert!(
        out.contains("reduce in CTR :"),
        "echoes as the base name: {out}"
    );
    assert!(
        out.contains("result Ctr{X}: zero"),
        "structured result sort: {out}"
    );
    assert!(
        out.contains("result NzCtr{X}: inc(inc(zero))"),
        "least sort over structured sorts: {out}"
    );
}

/// B-iv: parameterized-module instantiation through the REPL end-to-end — a single-parameter `BOX{ToColor}`
/// (structured instance sort `Box{ToColor}`, view-image sort `Hue`) and a multi-parameter `PR{VA, VB}`.
#[test]
fn instantiation_through_repl() {
    let out = repl().eval(conformance_file!("instantiation.maude")).output;
    assert!(
        out.contains("result Box{ToColor}: wrap(green)"),
        "structured instance sort: {out}"
    );
    assert!(out.contains("result Hue: green"), "view-image sort: {out}");
    assert!(
        out.contains("result SA: a"),
        "multi-parameter instantiation: {out}"
    );
}

/// Axis-A5: chained instantiation `M{ToTheory}{Arg}` — a theory-view first level (parameter bound to a
/// richer theory) then a by-parameter / module-view second level, with the chained import's renaming
/// collapsing the multi-level structured sort. This is the SORTABLE-LIST family's shape; here `USE{X ::
/// ORD}` chains `LST{ORD}{X}` (renaming `Lst{ORD}{X}` back to `Lst{X}`), instantiated at `USE{OrdColor}`.
/// Byte-identical to the reference; the prelude's `SORTABLE-LIST{Nat<}` now sorts identically too.
#[test]
fn instantiation_chained_through_repl() {
    let out = repl()
        .eval(conformance_file!("instantiation-chained.maude"))
        .output;
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
    let out = repl()
        .eval(conformance_file!("param-view-opmap.maude"))
        .output;
    assert!(out.contains("result F: f0"), "op->term: {out}");
    assert!(
        out.contains("result F: box(f0)"),
        "op->op over op->term: {out}"
    );
}

/// Axis-A4: a parameter theory that imports a module — the module-declared sort `Bool` is kept (not
/// renamed to `X$Bool`), so the parameterized module builds and the instance reduces.
#[test]
fn theory_module_sorts_through_repl() {
    let out = repl()
        .eval(conformance_file!("param-theory-module-sorts.maude"))
        .output;
    assert!(
        out.contains("result Bool: tt"),
        "module-declared sort kept: {out}"
    );
}

/// M0/TNK-004 — the real prelude's BOOL stack (TRUTH-VALUE → BOOL-OPS → TRUTH → BOOL, verbatim)
/// loads and reduces byte-identically to Maude's built-in BOOL. Proves poly/Universal expansion,
/// equality and BranchSymbol hooks, decided-condition laziness, stuck-branch normalization, and
/// SystemTrue/SystemFalse anchors. Each value + count is the reference binary's.
#[test]
fn prelude_bool_m0_through_repl() {
    let out = repl().eval(conformance_file!("prelude-bool.maude")).output;
    // The poly ops parse and pretty-print — the headers round-trip the mixfix.
    assert!(
        out.contains("reduce in BOOL : true == true ."),
        "== header: {out}"
    );
    assert!(
        out.contains("reduce in BOOL : if true then false else true fi ."),
        "if header: {out}"
    );
    assert!(
        out.contains("reduce in BOOL : if X:Bool then true and false else true or false fi ."),
        "stuck if header: {out}"
    );
    // Result value + sort, in order.
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result Bool: false",                             // true and false
            "result Bool: true",                              // true == true
            "result Bool: true",                              // true =/= false
            "result Bool: false",                             // if true then false else true fi
            "result Bool: if X:Bool then false else true fi", // stuck if normalizes both branches
            "result Bool: true",                              // false or true and not false
        ],
        "values: {out}"
    );
    // Distinctive rewrite counts: four single-rewrite reduces, the 5-rewrite stuck conditional, and
    // the 7-rewrite xor expansion.
    assert_eq!(
        out.matches("rewrites: 1 ").count(),
        4,
        "1-rewrite reduces: {out}"
    );
    assert!(out.contains("rewrites: 7 "), "xor-expansion count: {out}");
    assert!(
        out.contains("rewrites: 5 "),
        "stuck-branch normalization count: {out}"
    );
}

/// Increment-3 core: poly/Universal expansion over TWO kinds (Bool + an unrelated Color). `_==_` and
/// `if_then_else_fi` each instantiate per kind; this proves distinct per-kind dispatch, grammar
/// disambiguation, and the `if`-result sort over a non-Bool kind. Values/counts are the reference
/// binary's (built-in poly `==`/`if`, `red in MK : …`).
#[test]
fn poly_multikind_through_repl() {
    let out = repl()
        .eval(conformance_file!("poly-multikind.maude"))
        .output;
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
        out.contains("reduce in MK : if c1 == c2 then c0 else c2 fi .")
            && out.contains("rewrites: 2 "),
        "nested ==/if count: {out}"
    );
}

/// Increment 4 — a bare boolean condition `if b` abbreviates `if b = true`. The conditional
/// `ceq f(X) = b if X == a` fires for `f(a)` (a == a = true, 2 rewrites → b) and not for `f(b)`
/// (b == a = false, 1 rewrite, stays). Values/counts are the reference binary's (`red in T : …`).
#[test]
fn bare_condition_through_repl() {
    let out = repl()
        .eval(conformance_file!("bare-condition.maude"))
        .output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec!["result Foo: b", "result Foo: f(b)"],
        "bare-cond values: {out}"
    );
    // f(a): == eval + eq application = 2; f(b): == eval only (condition false) = 1.
    assert_eq!(out.matches("rewrites: 2 ").count(), 1, "fired count: {out}");
    assert_eq!(
        out.matches("rewrites: 1 ").count(),
        1,
        "not-fired count: {out}"
    );
}

/// M1 milestone — the real prelude's NAT (with its BOOL substrate) loads and every built-in reduces
/// byte-identically to Maude's built-in NAT, incl. the increment-5 additions: the `~>` partial arrow
/// (modExp parses), the ACU bitwise folds `xor`/`&`/`|` (multiplicity-aware — `5 xor 5 = 0`), the CUI
/// `sd` (`|m−n|`, commutative), `modExp` (modpow), and the `>>`/`<<` shifts (incl. the bignum
/// `1 << 64`). Each value/sort/count is the reference binary's (`red in NAT : …`); all cases are
/// 2-operand or prefix N-ary, whose counts match exactly (see fable-audit.md for the ≥3-operand-infix delta).
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
            "result NzNat: 2",  // gcd(12, 18, 8)  — prefix N-ary folds to 1 rewrite
            "result NzNat: 12", // lcm(4, 6)
            "result NzNat: 3",  // min(3, 5)
            "result NzNat: 5",  // max(3, 5)
            "result NzNat: 5",  // sd(3, 8)
            "result NzNat: 5",  // sd(8, 3)  — commutative
            "result NzNat: 6",  // 5 xor 3
            "result Zero: 0",   // 5 xor 5   — multiplicity cancels
            "result NzNat: 8",  // 12 & 10
            "result NzNat: 14", // 12 | 10
            "result NzNat: 24", // modExp(2, 10, 1000)
            "result NzNat: 40", // 5 << 3
            "result NzNat: 18446744073709551616", // 1 << 64  — bignum shift
            "result NzNat: 5",  // 40 >> 3
            "result Bool: true", // 3 < 5
            "result Bool: true", // 5 <= 5
            "result Bool: true", // 7 > 2
            "result Bool: false", // 2 >= 7
            "result Bool: true", // 3 divides 12
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
    assert!(
        out.contains("rewrite in COUNTER :") && out.contains("rewrites: 5 in"),
        "counter: {out}"
    );
}

/// The view-gap parser fix: a *parameterized* view declaration (`view V{X :: T} from T to M{X}`) and a
/// renaming over a **structured** sort (`* (sort Box{ColorE} to ColorBox)`) both parse, so a parameterized
/// module instantiated on a view + renamed builds and reduces. This is the pattern the metalevel's
/// container helpers use on the builtin chain — `protecting LIST{Qid} * (sort NeList{Qid} to NeQidList)`
/// (`QID-LIST`/`NAT-LIST`/`QID-SET`, verified byte-identical against the loaded prelude). Byte-identical to
/// the reference. (Chained multi-level instantiation — `LIST{A}{B}`, the SORTABLE-LIST family — is the
/// separate Axis-A5 residual in `fable-audit.md`.)
#[test]
fn view_parameterized_through_repl() {
    let out = repl()
        .eval(conformance_file!("view-parameterized.maude"))
        .output;
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
    let out = repl()
        .eval(conformance_file!("eq-bracket-rhs.maude"))
        .output;
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
    assert!(
        !r.input_complete("view V from TRIV to NUM is\n"),
        "open view keeps buffering"
    );
    assert!(
        r.input_complete("view V from TRIV to NUM is endv\n"),
        "`endv` completes the submission"
    );
    r.eval("fth TRIV is sort Elt . endfth");
    r.eval("fmod NUM is sort N . endfm");
    let out = r
        .eval("view Bad from TRIV to NUM is sort Elt to NoSuch . endv")
        .output;
    assert!(
        out.contains("failed to find sort NoSuch in NUM"),
        "got: {out}"
    );
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
    let out = repl()
        .eval(conformance_file!("correctness-sharing.maude"))
        .output;
    assert!(
        out.contains("result P: < c, c >"),
        "deep shared chain: {out}"
    );
    assert!(
        out.contains("result P: < b, b >"),
        "free/rhs/triple dup: {out}"
    );
    assert!(
        out.contains("result P: < mkA, mkA >"),
        "mb on shared constant: {out}"
    );
    assert!(out.contains("result L: b b b"), "AU triple share: {out}");
    assert!(out.contains("result E: b & b"), "CUI share: {out}");
    assert!(out.contains("result E: b + b"), "ACU share: {out}");
    assert!(
        !out.contains("rewrites: 3"),
        "C7: no pre-fix over-count (f(a) was 3): {out}"
    );
    assert!(
        !out.contains("rewrites: 4"),
        "C7: no pre-fix over-count (chain/triple were 4): {out}"
    );
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
    assert!(
        out.contains("\n    s"),
        "a wrapped continuation line carries the 4-space indent: {out}"
    );
    for line in out.lines() {
        assert!(
            line.len() <= 79,
            "every line stays within 79 columns: {} cols in {line:?}",
            line.len()
        );
    }
    // A short reduction is unaffected (no wrapping introduced).
    let short = r.eval("red s s z .").output;
    assert!(
        short.contains("result N: s s z"),
        "short result rendered: {short}"
    );
    assert!(
        !short.contains("\n    "),
        "short result is not wrapped: {short}"
    );
}

/// The `match` command renders solutions (a commutative pattern → two pairings).
#[test]
fn match_command_through_repl() {
    let mut r = repl();
    r.eval("fmod M is sort E . ops a b : -> E . op g : E E -> E [comm] . vars X Y : E . endfm");
    let out = r.eval("match g(X, Y) <=? g(a, b) .").output;
    assert!(out.contains("match in M :"), "header: {out}");
    assert!(
        out.contains("X --> a") && out.contains("X --> b"),
        "pairings: {out}"
    );
}

/// `select` switches the current module; success is silent, an unknown module is reported.
#[test]
fn select_and_show() {
    let mut r = repl();
    r.eval("fmod A is sort SA . op a : -> SA [ctor] . endfm");
    r.eval("fmod B is sort SB . op b : -> SB [ctor] . endfm");
    assert_eq!(r.current(), Some("B"));

    assert!(
        r.eval("select A .").output.is_empty(),
        "select success is silent"
    );
    assert_eq!(r.current(), Some("A"));
    assert!(r.eval("select NOPE .").output.contains("no module"));

    let mods = r.eval("show modules .").output;
    assert!(
        mods.contains('A') && mods.contains('B'),
        "show modules: {mods}"
    );
    let sm = r.eval("show module .").output; // current = A
    assert!(
        sm.contains("fmod A") && sm.contains("SA"),
        "show module: {sm}"
    );
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
    let out = repl()
        .eval("fmod M is protecting NOPE . sort S . endfm")
        .output;
    assert!(
        out.contains("not defined") || out.contains("error"),
        "got: {out}"
    );
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
    assert_eq!(
        out.matches("*********** equation").count(),
        2,
        "two steps: {out}"
    );
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
    assert!(
        no_subst.contains("*********** equation\neq N + s M = s (N + M) .\ns 0 + s 0\n--->"),
        "no subst: {no_subst}"
    );
    // The substitution `Var --> binding` lines are gone (the `--->` arrow is not a substitution line).
    assert!(
        !no_subst.contains("N --> ") && !no_subst.contains("M --> "),
        "substitution lines dropped: {no_subst}"
    );

    r.eval("set trace substitution on .");
    r.eval("set trace whole on .");
    let whole = r.eval("red s 0 + s 0 .").output;
    // The second (inner) step rewrites `s 0 + 0`; its whole term is `s (s 0 + 0)` -> `s s 0`.
    assert!(
        whole.contains("Old: s (s 0 + 0)\ns 0 + 0\n--->\ns 0\nNew: s s 0\n"),
        "whole inner step: {whole}"
    );
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
    assert!(
        bt.contains(
            "*********** failure for condition fragment\nM <= N = tt\n*********** failure #1\n"
        ),
        "failure: {bt}"
    );
    assert!(
        bt.contains("*********** trial #2\nceq max(M, N) = M if M <= N = ff ."),
        "trial #2: {bt}"
    );

    // condition off: the nested `_<=_` equation steps inside the condition disappear, scaffolding stays.
    r.eval("set trace condition off .");
    let off = r.eval("red max(s z, s s z) .").output;
    assert!(off.contains("*********** solving condition fragment\nM <= N = tt\n*********** success for condition fragment"), "scaffolding kept: {off}");
    assert!(
        !off.contains("z <= s z\n--->"),
        "nested condition rewrites hidden: {off}"
    );
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
    assert!(
        out.contains("*********** membership axiom\nmb g(X) : B .\nX --> a\nA: g(a) becomes B\n"),
        "inner mb: {out}"
    );
    assert!(
        out.contains(
            "*********** membership axiom\nmb g(g(X)) : C .\nX --> a\nA: g(g(a)) becomes C\n"
        ),
        "outer mb: {out}"
    );
    assert!(out.contains("result C:"), "result sort C: {out}");

    // `set trace whole on` adds the `Whole:` line — the full root term (`g(g(a))`) at each membership
    // application, for both the inner (`g(a) becomes B`) and outer (`g(g(a)) becomes C`) steps.
    r.eval("set trace whole on .");
    let whole = r.eval("red g(g(a)) .").output;
    assert!(
        whole.contains("X --> a\nWhole: g(g(a))\nA: g(a) becomes B\n"),
        "inner mb Whole: {whole}"
    );
    assert!(
        whole.contains("X --> a\nWhole: g(g(a))\nA: g(g(a)) becomes C\n"),
        "outer mb Whole: {whole}"
    );
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
    assert!(
        nested.contains("reduce in E : g(g(z)) ."),
        "nested-paren echo: {nested}"
    );
    let comma = r.eval("red < z, s z > .").output;
    assert!(
        comma.contains("reduce in E : < z, s z > ."),
        "comma echo: {comma}"
    );
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
    assert!(
        e.contains("reduce in FLTB : 1.0e+2 * 1.0e+2 ."),
        "float echo: {e}"
    );
    assert!(e.contains("result Flt: 1.0e+4"), "float result: {e}");

    // C11 — a rational echo is the compact `num/den`; a `0/N` (Zero numerator) is not a rational, so it
    // stays spaced.
    let mut r = repl();
    r.eval(conformance_file!("rat.maude")); // enters RATB
    let q = r.eval("red 6 / 4 .").output;
    assert!(q.contains("reduce in RATB : 6/4 ."), "rational echo: {q}");
    assert!(q.contains("result NzRat: 3/2"), "rational result: {q}");
    let z = r.eval("red 0 / 5 .").output;
    assert!(
        z.contains("reduce in RATB : 0 / 5 ."),
        "0/N stays spaced: {z}"
    );

    // C10 — a glued `-7` echoes compactly and reduces; a spaced `- 3` also echoes the compact `-3`; and
    // `5 -7` fails to parse, exactly as the reference binary rejects it.
    let mut r = repl();
    r.eval(conformance_file!("correctness-glued-minus.maude")); // enters INTB
    let g = r.eval("red -7 quo 2 .").output;
    assert!(
        g.contains("reduce in INTB : -7 quo 2 ."),
        "glued-minus echo: {g}"
    );
    assert!(g.contains("result NzInt: -3"), "glued-minus result: {g}");
    let s = r.eval("red - 3 .").output;
    assert!(
        s.contains("reduce in INTB : -3 ."),
        "spaced minus echoes compact: {s}"
    );
    let bad = r.eval("red 5 -7 .").output;
    assert!(
        bad.contains("no parse"),
        "`5 -7` is rejected like the binary: {bad}"
    );
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
    assert!(
        out.contains("result E: c"),
        "result (a ; b -> X, c -> Y): {out}"
    );
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
    assert!(
        bi.contains("(built-in equation for symbol _+_)\n2 + 3\n--->\n5\n"),
        "trace-builtin:\n{bi}"
    );

    let mb = run_session(conformance_file!("trace-membership.maude"));
    assert!(
        mb.contains("*********** membership axiom\nmb g(X) : B .\nX --> a\nA: g(a) becomes B\n"),
        "trace-membership:\n{mb}"
    );

    let cond = run_session(conformance_file!("trace-conditional.maude"));
    assert!(
        cond.contains("*********** trial #1\nceq max(M, N) = N if M <= N = tt ."),
        "trial #1:\n{cond}"
    );
    assert!(
        cond.contains("*********** failure #1") && cond.contains("*********** trial #2"),
        "backtrack #1->#2:\n{cond}"
    );
}

/// TNK-011 end to end: the retained collapse-membership fixture reaches the downstream value and its
/// traced collapsed application preserves the original statement id/body, identity binding, and Whole line.
#[test]
fn collapsing_membership_fixture_through_repl() {
    let out = repl()
        .eval(conformance_file!("audit/B3c-membership-collapse.maude"))
        .output;
    assert!(
        out.contains(
            "reduce in B3C-DOWNSTREAM-VALUE : wrap(a) .\n\
             rewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)\n\
             result E: b"
        ),
        "downstream sorted equation:\n{out}"
    );
    assert!(
        out.contains(
            "*********** membership axiom\n\
             mb a * X : Special .\n\
             X --> z\n\
             Whole: a\n\
             E: a becomes Special"
        ),
        "collapsed membership trace:\n{out}"
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
    assert!(
        s.contains("*********** rule\nrl a => b .\nempty substitution\na\n--->\nb"),
        "rule block 1:\n{s}"
    );
    assert!(
        s.contains("*********** rule\nrl b => c .\nempty substitution\nb\n--->\nc"),
        "rule block 2:\n{s}"
    );
    assert!(
        s.contains("rewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: c"),
        "tail:\n{s}"
    );
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
    assert!(
        s.contains("*********** trial #1\ncrl f(X) => g(X) if X = a .\nX --> b"),
        "trial #1:\n{s}"
    );
    assert!(
        s.contains("*********** failure for condition fragment\nX = a"),
        "fragment failure:\n{s}"
    );
    assert!(s.contains("*********** failure #1"), "trial #1 fails:\n{s}");
    assert!(
        s.contains("*********** trial #2\ncrl f(X) => h(Y) if Y := X ."),
        "trial #2:\n{s}"
    );
    assert!(
        s.contains("*********** success #2"),
        "trial #2 succeeds:\n{s}"
    );
    assert!(
        s.contains(
            "*********** rule\ncrl f(X) => h(Y) if Y := X .\nX --> b\nY --> b\nf(b)\n--->\nh(b)"
        ),
        "rule fires:\n{s}"
    );
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
        s.contains(
            "state 0, St: a\narc 0 ===> state 1 (rl a => b .)\narc 1 ===> state 2 (rl a => c .)"
        ),
        "show graph state 0:\n{s}"
    );
    assert!(
        s.contains("state 3, St: d\narc 0 ===> state 4 (rl d => e .)"),
        "show graph state 3:\n{s}"
    );
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

/// A rewrite condition (`=>`) is legal only in a rule. In an equation Maude warns "no parse for statement"
/// and DROPS the statement, keeping the module usable (fable-audit.md §3.4 statement recovery — verified
/// against the oracle: `reduce a` returns `a`, the dropped `ceq` never fires). Our diagnostics are phase E,
/// so the drop is silent; the pin is that the module builds and the bad `ceq` has no effect.
#[test]
fn rewrite_condition_dropped_in_equation() {
    let out = repl()
        .eval("fmod E is sort S . ops a b : -> S . var X : S . ceq a = b if X => b . endfm\nreduce a .")
        .output;
    assert!(
        out.contains("result S: a"),
        "module usable, bad ceq dropped: {out}"
    );
    assert!(
        !out.contains("result S: b"),
        "the dropped ceq must not fire: {out}"
    );
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
    assert!(
        r.eval("red dbl(s s z) .")
            .output
            .contains("result Nat: s s s s z"),
        "on-the-fly var in an eq"
    );
    assert!(
        r.eval("match X:Nat <=? s z .")
            .output
            .contains("X:Nat --> s z"),
        "on-the-fly var in match, with sort"
    );
    // …and in a system module's search goal.
    r.eval("mod S is sort T . ops p q : -> T . rl p => q . endm");
    let s = r.eval("search p =>1 Y:T .").output;
    assert!(
        s.contains("Y:T --> q"),
        "on-the-fly var in a search goal:\n{s}"
    );
}

/// A rule in a functional module (`fmod`) is rejected — rules belong only to system modules (`mod`).
#[test]
fn rule_in_fmod_is_rejected() {
    let out = repl()
        .eval("fmod F is sort S . ops a b : -> S . rl a => b . endfm")
        .output;
    assert!(
        out.contains("not allowed in a functional module"),
        "rejection: {out}"
    );
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
    assert!(
        out.contains("*********** rule\nrl a => b ."),
        "traced rule from a one-shot file load:\n{out}"
    );
    assert!(
        out.contains("rewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)\nresult S: c"),
        "result:\n{out}"
    );
}

/// The multi-line buffer boundary: a command terminator / a closed module complete; an open module body
/// or a terminator-less line keep buffering; a bare `quit` completes.
#[test]
fn input_complete_boundaries() {
    let mut r = repl();
    assert!(r.input_complete("red x ."), "command terminator");
    assert!(
        r.input_complete("fmod M is sort S . endfm"),
        "closed module"
    );
    assert!(
        !r.input_complete("fmod M is sort S ."),
        "open module body keeps buffering"
    );
    assert!(!r.input_complete("red x"), "no terminator");
    assert!(r.input_complete("quit"), "bare quit");
    assert!(r.input_complete("q"), "bare q");
    assert!(!r.input_complete(""), "empty");
    assert!(!r.input_complete("   \n  "), "whitespace");
}

/// Extract the conformance-relevant outcome lines from an objects-system run: every line that is **not**
/// a command echo (the `rewrite`/`reduce`/`search` line and any wrapped continuation, ending at the
/// trailing ` .`). What remains — `result …`, `rewrites:`, `states:`, `Solution …`, the `Var --> v`
/// bindings — is exactly what we compare byte-for-byte to the reference (the echo's `__`-parenthesization
/// and ordering is a known rendering divergence that every conformance fixture abstracts over; the
/// `rewrites/second` *rate* is timing noise — ours is always `~`).
fn objects_outcomes(out: &str) -> Vec<String> {
    let mut lines = out.lines().peekable();
    let mut keep = Vec::new();
    while let Some(line) = lines.next() {
        if matches!(
            line.split(' ').next(),
            Some("rewrite" | "reduce" | "search" | "erewrite")
        ) {
            // Skip the echo block: this line plus continuations, through the trailing ` .`.
            let mut l = line;
            while !l.trim_end().ends_with('.') {
                match lines.next() {
                    Some(next) => l = next,
                    None => break,
                }
            }
            continue;
        }
        keep.push(line.to_string());
    }
    keep
}

/// Pillar 2.5-A — object-message **configurations** under plain `rewrite`/`search` (no `erewrite`, no
/// external IO). Loads the real prelude `CONFIGURATION` (`<_:_|_>` resolving its `ObjectConstructorSymbol`
/// id-hook; the `config`/`obj`/`portal` op attributes recorded onto the kernel symbol) plus a bank and a
/// ping-pong system, and pins the outcome of each command **byte-identically to the reference**
/// (`~/Downloads/Maude-3/maude -no-banner conformance/objects.maude`). The message-vs-object multiset
/// order is the load-bearing case: Maude orders ACU elements arity-first (`orderInt`), so the arity-2
/// `ping(p1, p2)` prints *before* the arity-3 objects — `dag_compare` now matches (it ordered by raw
/// `SymbolId` before, which is why this is the test that locks the fix in).
#[test]
fn objects_through_repl() {
    let out = repl().eval(conformance_file!("objects.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "objects build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            // BANK: two credits apply (4 rewrites), balances updated, objects in `a < b` order.
            "rewrites: 4 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: < a : Account | bal : 50 > < b : Account | bal : 125 >",
            // getClass: an ordinary equation over the object constructor.
            "rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Cid: Account",
            // BANK search: credit 5 then 7 reaches balance 12 (state 3 of 4); declared var `N` prints bare.
            "",
            "Solution 1 (state 3)",
            "states: 4  rewrites: 6 in 0ms cpu (0ms real) (~ rewrites/second)",
            "N --> 12",
            "",
            "No more solutions.",
            "states: 4  rewrites: 8 in 0ms cpu (0ms real) (~ rewrites/second)",
            // PINGPONG `rewrite [4]`: four message hand-offs; the leftover `ping(p1, p2)` (arity 2) prints
            // BEFORE the two arity-3 objects — the arity-first ACU order. (Result wraps at 80 cols.)
            "rewrites: 4 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: ping(p1, p2) < p1 : Player | turns : 2 > < p2 : Player |",
            "    turns : 2 >",
            // PINGPONG search `=>+`: the first `pong(p2, p1)` state (depth 1), the soup remainder bound to C.
            "",
            "Solution 1 (state 1)",
            "states: 2  rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)",
            "C:Configuration --> < p1 : Player | turns : 1 > < p2 : Player | turns : 0 >",
            // erewrite (object-message-fair, Pillar 2.5-B). The `msg`-flagged credit/ping/pong engage the
            // ConfigSymbol scheduler. BANK: one pass delivers BOTH credits (the bound counts passes), 4
            // rewrites (2 credits x rule+`+`).
            "rewrites: 4 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: < a : Account | bal : 50 > < b : Account | bal : 125 >",
            // BANK, two credits to ONE account: `a` evolves 0->5->12 within the pass; the lone object
            // collapses to `result Object:`.
            "rewrites: 4 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Object: < a : Account | bal : 12 >",
            // PINGPONG `erewrite [3]`: one delivery per pass (each produces the next message), so [3] = 3
            // hand-offs — pong leftover, p1 at 2 turns, p2 at 1. (Result wraps at 80 cols.)
            "rewrites: 3 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: pong(p2, p1) < p1 : Player | turns : 2 > < p2 : Player |",
            "    turns : 1 >",
        ],
        "objects outcomes (echoes/rate aside) must match the reference: {out}"
    );
}

/// Pillar 2.5-C (synchronous STD-STREAM) — `erewrite` EXTERNAL-mode standard-stream output. With a `<>`
/// portal in the soup, a `write(stdout, me, str)` message to the `stdout` manager (`StreamManagerSymbol`)
/// emits `str` and replies `wrote(me, stdout)` **synchronously** (no reactor). The side-channel writes
/// surface after the echo, before `rewrites:` — exactly as Maude interleaves them. GREET writes one line;
/// TICKER writes three sequentially (each waits for the `wrote` reply). Byte-identical to the reference.
#[test]
fn objects_io_through_repl() {
    let mut r = repl();
    r.set_stdin("one\ntwo\n"); // piped stdin for ECHO's getLine
    let out = r.eval(conformance_file!("objects-io.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "io build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            // GREET: start -> write "hello\n" -> wrote -> stop. The write happens externally (not a
            // rewrite); the count is the `go`+`done` rules = 2.
            "hello",
            "rewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: <> < g : Greeter | none >",
            // TICKER: three sequential "tick\n" writes (go + next + next), then stop = 4 rule rewrites.
            "tick",
            "tick",
            "tick",
            "rewrites: 4 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: <> < t : Ticker | n : 0 >",
            // ECHO: getLine reads "one\n"/"two\n" (incl. newline), each echoed straight to stdout; count is
            // go + got + next + got + stop = 5 rule rewrites (the getLine/write handling is not a rewrite).
            "one",
            "two",
            "rewrites: 5 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: <> < e : Echoer | n : 0 >",
        ],
        "STD-STREAM stdout writes + stdin getLine + erewrite outcomes must match the reference: {out}"
    );
}

#[test]
fn erewrite_parse_failure_preserves_pending_stdin() {
    let mut r = repl();
    let (modules, _) = conformance_file!("objects-io.maude")
        .split_once("erewrite in GREET")
        .expect("objects-io command boundary");
    let loaded = r.eval(modules);
    assert!(
        !loaded.exit && !loaded.output.contains("error in module"),
        "{}",
        loaded.output
    );

    r.set_stdin("kept\n");
    let rejected = r.eval("erewrite in ECHO : bogus .");
    assert!(
        rejected
            .output
            .contains("error: no parse at token 0 (`bogus`)"),
        "{}",
        rejected.output
    );

    let recovered = r.eval("erewrite in ECHO : <> start(e) < e : Echoer | n : (s 0) > .");
    assert!(
        recovered.output.contains("\nkept\n"),
        "failed erewrite must not consume pending stdin: {}",
        recovered.output
    );
}

/// Pillar 2.5-E — the object-oriented **surface language** (`omod`/`class`/`subclass`/`msg`). Each `omod`
/// desugars to CONFIGURATION-based Core-Maude (`class C` → sort + `subsort C < Cid` + constant `op C`;
/// attribute `a : S` → `op a :_ : S -> Attribute`; `subclass` → subsort; `msg` → `[ctor msg]` op) and
/// auto-imports the **built-in** CONFIGURATION. Object-pattern completion (`ooTransform.cc`) is the
/// load-bearing part: the `credit` rule names only `bal` yet fires on a `Savings` object that also carries
/// `rate` (a fresh `Atts:AttributeSet` variable captures it) and whose class `Savings` is a **subclass** of
/// the rule's `Account` (the class constant is rewritten to a fresh class-sorted variable, so `V:Account`
/// matches `Savings`). Byte-identical to the reference
/// (`~/Downloads/Maude-3/maude -no-banner conformance/objects-omod.maude`).
#[test]
fn objects_omod_through_repl() {
    let out = repl().eval(conformance_file!("objects-omod.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "omod build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            // rewrite: credit fires on the Account and on the Savings subclass (its extra `rate` preserved).
            "rewrites: 4 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: < a : Account | bal : 50 > < b : Savings | bal : 125,",
            "    rate : 5 >",
            // getClass on the subclass instance returns its actual class.
            "rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Savings: Savings",
            // search: credit 5 then 7 reaches balance 12 (state 3 of 4).
            "",
            "Solution 1 (state 3)",
            "states: 4  rewrites: 6 in 0ms cpu (0ms real) (~ rewrites/second)",
            "N --> 12",
            "",
            "No more solutions.",
            "states: 4  rewrites: 8 in 0ms cpu (0ms real) (~ rewrites/second)",
            // erewrite (object-message-fair): one pass delivers both credits.
            "rewrites: 4 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: < a : Account | bal : 50 > < b : Savings | bal : 125,",
            "    rate : 5 >",
            // erewrite ping-pong: [3] = three hand-offs; pong leftover, p1 at 2 turns, p2 at 1.
            "rewrites: 3 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: pong(p2, p1) < p1 : Player | turns : 2 > < p2 : Player |",
            "    turns : 1 >",
        ],
        "omod/class/subclass/msg + object-pattern completion outcomes must match the reference: {out}"
    );
}

/// Pillar 2.5-E — object-pattern completion **attribute edge cases** (`ooTransform.cc`), beyond the
/// class-constant→variable + fresh-variable cases above: (1) a rule whose RHS omits an attribute its LHS
/// matched — completion copies the pattern attribute back, so `applyRate` updates `bal` yet preserves
/// `rate`; (2) a rule whose RHS sets an attribute its LHS did not match (`last`) — completion adds a fresh
/// kind-variable attribute to the LHS pattern, so the rule fires only on objects already carrying it.
/// Byte-identical to `~/Downloads/Maude-3/maude -no-banner conformance/objects-omod-attrs.maude`.
#[test]
fn objects_omod_attrs_through_repl() {
    let out = repl()
        .eval(conformance_file!("objects-omod-attrs.maude"))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "omod-attrs build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            // applyRate: bal := bal + rate (100 + 5); rate preserved via the missing-attribute copy.
            "rewrites: 2 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Object: < s1 : Savings | bal : 105, rate : 5 >",
            // log: count := s count, last := 7 (last matched by a fresh kind-variable on the LHS).
            "rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Object: < lg : Logger | count : 1, last : 7 >",
        ],
        "object-pattern completion attribute edge cases must match the reference: {out}"
    );
}

/// Pillar 2.5-E / erewrite — the object-message scheduler's **two paths**. `reward` is a single-object
/// message rule (Maude's fast path: object + message, same name); `pair` is a MULTI-object rule (message +
/// two objects), which is not an object-message pair, so it takes the generic **leftOver** path
/// (`ConfigSymbol::leftOverRewrite`). tnk previously fired only the fast path, so a multi-object rule never
/// delivered under `erewrite` though it did under plain `rewrite`. Byte-identical to the reference
/// (`~/Downloads/Maude-3/maude -no-banner conformance/objects-omod-multi.maude`).
#[test]
fn objects_omod_multi_through_repl() {
    let out = repl()
        .eval(conformance_file!("objects-omod-multi.maude"))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "multi build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            // reward(a,5) via the fast path (a: 0->5, +1 for the `+`), then pair via leftOver (a->6, b->1) = 3.
            "rewrites: 3 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: < a : Member | pts : 6 > < b : Member | pts : 1 >",
            // pair alone: one leftOver rewrite bumps both objects.
            "rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Configuration: < a : Member | pts : 1 > < b : Member | pts : 1 >",
        ],
        "erewrite object-message fast path + multi-object leftOver path must match the reference: {out}"
    );
}

/// Pillar 2.5-E: `oth` (object THEORY) — the theory analogue of `omod`. It shares the `omod`
/// class/subclass/msg desugaring (gated on the object-oriented flag, not module-vs-theory), auto-imports
/// CONFIGURATION, and builds; `getClass` (from CONFIGURATION) resolves an object's class, and a subclass
/// instance returns its own class. Byte-identical to
/// `~/Downloads/Maude-3/maude -no-banner conformance/objects-oth.maude`.
#[test]
fn objects_oth_through_repl() {
    let out = repl().eval(conformance_file!("objects-oth.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "oth build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            "rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Shape: Shape",
            // getClass on a Square (a subclass of Shape) instance returns its own class.
            "rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)",
            "result Square: Square",
        ],
        "oth (object theory) class/subclass/msg build + getClass must match the reference: {out}"
    );
}

/// Pillar 2.5-E / META-LEVEL: an object module round-trips through the meta level byte-identically to the
/// reference. `upModule` of an `omod` yields a plain completed `mod` (Maude strips the OO fiction) whose
/// message op carries `[ctor msg]`, whose attribute op is named `` 'bal`:_ `` (the backtick-blank Maude
/// keeps in a spaced mixfix name — reconstructed by `meta_op_name`), and whose rule shows the completed
/// form (`'V:Account`, `'Atts:AttributeSet` spliced in). `metaRewrite` over it delivers the message and
/// reduces the balance, the result again spelling the attribute op `` 'bal`:_ ``. Verified byte-identical
/// against `~/Downloads/Maude-3/maude` (see the diff in the commit).
#[test]
fn objects_omod_meta_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude")); // load the META-LEVEL tower
    let out = r
        .eval(concat!(
            "omod BANK is\n",
            "  protecting NAT .\n",
            "  class Account | bal : Nat .\n",
            "  ops a b : -> Oid [ctor] .\n",
            "  msg credit : Oid Nat -> Msg .\n",
            "  vars A : Oid .  vars N M : Nat .\n",
            "  rl [credit] : credit(A, M) < A : Account | bal : N > => < A : Account | bal : (N + M) > .\n",
            "endom\n",
            "red in META-LEVEL : upModule('BANK, false) .\n",
            "red in META-LEVEL : metaRewrite(upModule('BANK, false), ",
            "'__['credit['a.Oid, 's_^5['0.Zero]], ",
            "'<_:_|_>['a.Oid, 'Account.Account, 'bal`:_['0.Zero]]], unbounded) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error"),
        "omod meta: {out}"
    );
    // upModule: the message op is `[ctor msg]`, the attribute op is spelled with the backtick-blank.
    assert!(
        out.contains("op 'credit : 'Oid 'Nat -> 'Msg [ctor msg] ."),
        "upModule [ctor msg]: {out}"
    );
    assert!(
        out.contains("op 'bal`:_ : 'Nat -> 'Attribute [ctor gather('&)] ."),
        "attr op name: {out}"
    );
    // metaRewrite: credit delivered, balance 0 -> 5, attribute op spelled `` 'bal`:_ `` in the result.
    assert!(
        out.contains("'bal`:_['s_^5["),
        "metaRewrite result must spell the attribute op with the backtick-blank and reduce the balance: {out}"
    );
}

/// Pillar 2.5-E / META-LEVEL: an object THEORY's rule is object-pattern-completed and up-translates
/// byte-identically. `upModule` of an `oth` yields a `th` whose rule shows the completed form
/// (`'V:Acct` for the class constant, a fresh `'Atts:AttributeSet`, the attribute op spelled `` 'bal`:_ ``).
/// Verified byte-identical against the reference (an `oth`'s non-`[nonexec]` axioms execute + complete, as
/// in Maude, so they are retained and shown).
#[test]
fn objects_oth_meta_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(concat!(
            "oth OT is\n",
            "  protecting NAT .\n",
            "  class Acct | bal : Nat .\n",
            "  op c : -> Oid [ctor] .\n",
            "  msg cr : Oid Nat -> Msg .\n",
            "  vars A : Oid .  vars N M : Nat .\n",
            "  rl [cr] : cr(A, M) < A : Acct | bal : N > => < A : Acct | bal : (N + M) > .\n",
            "endoth\n",
            "red in META-LEVEL : upModule('OT, false) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "oth meta: {out}"
    );
    // The oth up-translates to a `th` (theory), and its rule is completed and shown.
    assert!(
        out.contains("th 'OT is"),
        "oth up-translates to a theory: {out}"
    );
    // The rule is object-pattern-completed: class constant -> fresh `'V:Acct`, a fresh attribute-set
    // variable `'Atts:AttributeSet`, and the attribute op spelled with the backtick-blank. (The full rule
    // wraps at 80 columns, so assert the individual completion markers.)
    for marker in ["'V:Acct", "'Atts:AttributeSet", "'bal`:_[", "[label('cr)]"] {
        assert!(
            out.contains(marker),
            "oth rule missing completion marker `{marker}`: {out}"
        );
    }
}

/// META-LEVEL up*: a module's own `[nonexec]` axioms are retained by `upEqs`/`upMbs`/`upRls` (build skips
/// them — a proof obligation carries no engine trace — so up-translation parses their bubbles on demand),
/// in **declaration order**, and equation/membership `[label …]`s are retained too (the label rode along).
/// Byte-verified against the reference: nonexec eq/mb/cmb/rule with labels, exec-before-nonexec ordering,
/// and an executable equation's own label.
#[test]
fn meta_nonexec_up_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude")); // load the META-LEVEL tower
    let out = r
        .eval(concat!(
            // an executable eq declared BEFORE a nonexec eq — declaration order must survive up-translation.
            "fth ORDA is\n",
            "  sorts Elt .\n",
            "  op a : -> Elt [ctor] .\n",
            "  op f : Elt -> Elt .  op g : Elt -> Elt .\n",
            "  var X : Elt .\n",
            "  eq f(X) = X .\n",
            "  eq g(X) = X [nonexec label gx] .\n",
            "endfth\n",
            // an EXECUTABLE equation label is retained too (previously dropped).
            "fmod LBL is\n",
            "  sorts S .  op a : -> S [ctor] .  op f : S -> S .  var X : S .\n",
            "  eq f(X) = X [label fx] .\n",
            "endfm\n",
            // nonexec memberships: plain + conditional.
            "fth MBX is\n",
            "  sorts S T .  subsort T < S .  op a : -> S [ctor] .  op p : S -> S .  var X : S .\n",
            "  mb a : T [nonexec label mbax] .\n",
            "  cmb p(X) : T if X : T [nonexec label cmbax] .\n",
            "endfth\n",
            // a nonexec rule (label from the leading `[rax] :`), then an executable rule.
            "mod RLX is\n",
            "  sorts S .  ops a b : -> S [ctor] .  op f : S -> S .  var X : S .\n",
            "  rl [rax] : f(X) => X [nonexec] .\n",
            "  rl f(a) => b .\n",
            "endm\n",
            "red in META-LEVEL : upEqs('ORDA, false) .\n",
            "red in META-LEVEL : upEqs('ORDA, true) .\n", // flat form (no imports ⇒ same result) — exercises the flat merge path
            "red in META-LEVEL : upEqs('LBL, false) .\n",
            "red in META-LEVEL : upMbs('MBX, false) .\n",
            "red in META-LEVEL : upRls('RLX, false) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "nonexec up: {out}"
    );
    // The nonexec eq is retained with `[nonexec label('gx)]`, in declaration order after the exec `[none]`.
    assert!(
        out.contains(
            "eq 'f['X:Elt] = 'X:Elt [none] .\neq 'g['X:Elt] = 'X:Elt [nonexec label('gx)] ."
        ),
        "nonexec eq retained in declaration order: {out}"
    );
    // An executable equation's own `[label]` is retained.
    assert!(
        out.contains("eq 'f['X:S] = 'X:S [label('fx)] ."),
        "executable eq label: {out}"
    );
    // Nonexec memberships (plain + conditional) retained with their labels.
    assert!(
        out.contains("mb 'a.S : 'T [nonexec label('mbax)] ."),
        "nonexec mb: {out}"
    );
    assert!(
        out.contains("cmb 'p['X:S] : 'T if 'X:S : 'T [nonexec label('cmbax)] ."),
        "nonexec cmb: {out}"
    );
    // Nonexec rule retained (with its label), then the executable rule as `[none]`, in declaration order.
    assert!(
        out.contains("rl 'f['X:S] => 'X:S [nonexec label('rax)] .\nrl 'f['a.S] => 'b.S [none] ."),
        "nonexec rule retained in declaration order: {out}"
    );
}

/// Multi-token operator names (residual: the inter-token blank in an op name). An op name may carry a blank
/// between two text tokens — `op a b`, `op c d_`, `op _e f_` — and it is load-bearing: `c d_` is the mixfix
/// `c`, `d`, `_`, distinct from the single literal `cd_`. tnk now preserves it (canonical name keeps it as a
/// backquote, `` c`d_ ``), so such ops lex, parse, reduce, and print byte-identically to the reference; the
/// space form (`a b`) and the backquote form (`` a`b ``) tokenize to the same name, and an escaped special
/// (`` _`[_`] ``) is unaffected. Verified against `conformance/multitoken-op.maude`.
#[test]
fn multitoken_op_through_repl() {
    let out = repl().eval(conformance_file!("multitoken-op.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error"),
        "multitoken op: {out}"
    );
    assert!(out.contains("result S: a b"), "2-token constant: {out}");
    assert!(
        out.contains("result S: c d a b"),
        "mixfix over a 2-token arg: {out}"
    );
    assert!(
        out.contains("result S: a b e f a b"),
        "infix with multiple literals: {out}"
    );
    assert!(
        out.contains("result S: done[done]"),
        "escaped-bracket op still works: {out}"
    );
    // `g(a b) = done` fires over a multi-token subterm, via BOTH the space and backquote forms.
    assert_eq!(
        out.matches("result S: done\n").count(),
        2,
        "the equation fires for both `g(a b)` and `g(a`b)`: {out}"
    );
}

/// META round-trip of multi-token op names: `upModule` spells the inter-token blank as a backquote
/// (`` 'a`b ``, `` 'c`d_ ``), matching the reference, and `metaReduce` over a hand-written meta term whose
/// head is such a Qid (`` 'c`d_['a`b.S] ``) lexes the backquote, resolves the op, and reduces. Byte-verified
/// against the reference.
#[test]
fn multitoken_op_meta_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude")); // the META-LEVEL tower
    let out = r
        .eval(concat!(
            "fmod MT is\n",
            "  sorts S .\n",
            "  op a b : -> S [ctor] .\n",
            "  op c d_ : S -> S .\n",
            "  op z : -> S [ctor] .\n",
            "  eq c d (a b) = z .\n",
            "endfm\n",
            "red in META-LEVEL : upModule('MT, false) .\n",
            "red in META-LEVEL : metaReduce(upModule('MT, false), 'c`d_['a`b.S]) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "multitoken meta: {out}"
    );
    // upModule spells the blank as a backquote in each op's name.
    assert!(
        out.contains("op 'a`b : nil -> 'S [ctor] ."),
        "up: 2-token constant name: {out}"
    );
    assert!(
        out.contains("op 'c`d_ : 'S -> 'S [none] ."),
        "up: mixfix name: {out}"
    );
    // metaReduce down-translates the backquote Qid and reduces `c d (a b)` to `z`.
    assert!(
        out.contains("result ResultPair: {'z.S, 'S}"),
        "down: metaReduce over a backquote Qid: {out}"
    );
}

/// A signature-owned compound identity survives the complete metalevel module round-trip. `upModule`
/// emits the identity as a structural meta-term, and feeding that module directly to `metaReduce`
/// down-translates the identity against the rebuilt target symbols so construction collapses it. Exact
/// shapes and rewrite count were transcribed from Maude 3.5.1.
#[test]
fn compound_identity_meta_roundtrip_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(concat!(
            "fmod ID-META is\n",
            "  sort S .\n",
            "  ops a b : -> S [ctor] .\n",
            "  op pair : S S -> S [ctor] .\n",
            "  op join : S S -> S [assoc id: pair(a,b)] .\n",
            "endfm\n",
            "red in META-LEVEL : upModule('ID-META, false) .\n",
            "red in META-LEVEL : metaReduce(upModule('ID-META, false), ",
            "'join['pair['a.S, 'b.S], 'a.S]) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "compound id meta: {out}"
    );
    assert!(
        out.contains("op 'join : 'S 'S -> 'S [assoc id('pair['a.S, 'b.S])] ."),
        "upModule structural identity: {out}"
    );
    assert!(
        out.contains("rewrites: 2") && out.contains("result ResultPair: {'a.S, 'S}"),
        "down-translated identity collapse: {out}"
    );
}

/// Down-module identity leaves retain their meta-term sort qualification rather than collapsing to a
/// constant spelling. The two `a` declarations share one connected component, so `(a).S` is load-bearing
/// when `upModule` is rebuilt as the target signature.
#[test]
fn overloaded_constant_identity_meta_roundtrip_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(concat!(
            "fmod ID-META-OVERLOAD is\n",
            "  sorts S U . subsort U < S .\n",
            "  op a : -> S [ctor] .\n",
            "  op a : -> U [ctor] .\n",
            "  op b : -> S [ctor] .\n",
            "  op pair : S S -> S [ctor] .\n",
            "  op join : S S -> S [assoc id: pair((a).S,b)] .\n",
            "endfm\n",
            "red in META-LEVEL : metaReduce(upModule('ID-META-OVERLOAD, false), ",
            "'join['pair['a.S, 'b.S], 'b.S]) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "qualified id meta: {out}"
    );
    assert!(
        out.contains("rewrites: 2") && out.contains("result ResultPair: {'b.S, 'S}"),
        "qualified overload identity collapse: {out}"
    );
}

/// The same metalevel identity path stays compact for an iterated million-count subterm: neither
/// `upModule` nor rebuilding its `id(...)` expands the static term into a recursive unary chain.
#[test]
fn compact_iter_identity_meta_roundtrip_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(concat!(
            "fmod ID-META-ITER is\n",
            "  sort S .\n",
            "  op a : -> S [ctor] .\n",
            "  op g : S -> S [ctor iter] .\n",
            "  op f : S -> S .\n",
            "  op join : S S -> S [assoc id: g^1000000(a)] .\n",
            "  eq f(g^1000000(a)) = a .\n",
            "endfm\n",
            "red in META-LEVEL : upModule('ID-META-ITER, false) .\n",
            "red in META-LEVEL : metaReduce(upModule('ID-META-ITER, false), ",
            "'join['g^1000000['a.S], 'a.S]) .\n",
            "red in META-LEVEL : metaReduce(upModule('ID-META-ITER, false), ",
            "'f['g^1000000['a.S]]) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "compact id meta: {out}"
    );
    assert!(
        out.contains("id('g^1000000['a.S])"),
        "upModule preserves the compact compound identity: {out}"
    );
    assert!(
        out.contains("rewrites: 2") && out.contains("result ResultPair: {'a.S, 'S}"),
        "down-translated compact identity collapse: {out}"
    );
    assert!(
        out.contains("rewrites: 3"),
        "inline equation's compact static Term::Iter down/up path: {out}"
    );
}

fn variant_sequence_lines(output: &str) -> Vec<String> {
    output
        .lines()
        .filter_map(|line| {
            if let Some(rest) = line.strip_prefix("rewrites: ") {
                return Some(format!(
                    "rewrites: {}",
                    rest.split_whitespace().next().unwrap_or("?")
                ));
            }
            [
                "get variants",
                "variant unify",
                "variant match",
                "Variant ",
                "Unifier ",
                "Matcher ",
                "S:",
                "X -->",
                "Y -->",
                "Z -->",
                "No more ",
            ]
            .iter()
            .any(|prefix| line.starts_with(prefix))
            .then(|| line.to_string())
        })
        .collect()
}

fn one_rewrite_count(output: &str) -> u64 {
    output
        .lines()
        .find_map(|line| {
            line.strip_prefix("rewrites: ")?
                .split_whitespace()
                .next()?
                .parse()
                .ok()
        })
        .unwrap_or_else(|| panic!("missing rewrite count in: {output}"))
}

const META_VARIANT_XOR: &str = r#"
set show timing off .
fmod XOR is
  sort XOR .
  sort Elem .
  ops cst1 cst2 cst3 cst4 : -> Elem .
  subsort Elem < XOR .
  op _+_ : XOR XOR -> XOR [ctor assoc comm] .
  op 0 : -> XOR .
  vars X Y : XOR .
  eq Y + 0 = Y [variant] .
  eq X + X = 0 [variant] .
  eq X + X + Y = Y [variant] .
endfm
fmod META-TEST is
  inc XOR .
  inc META-LEVEL .
endfm
"#;

fn meta_variant_repl() -> Repl {
    let mut r = repl();
    let prelude = r.eval(conformance_file!("prelude-meta.maude")).output;
    assert!(
        !prelude.contains("error in module") && !prelude.contains("no parse"),
        "meta prelude: {prelude}"
    );
    let setup = r.eval(META_VARIANT_XOR).output;
    assert!(
        !setup.contains("error in module") && !setup.contains("no parse"),
        "variant meta setup: {setup}"
    );
    r
}

/// Oracle sequence from Maude 3.5.1: this pins incremental numbering, the `%` family layer,
/// continuation state, plain variant-unifier order, and complete variant matching end to end.
#[test]
fn variant_sequences_and_continuation_match_oracle() {
    let mut r = repl();
    r.eval(
        r#"
fmod IDEM is
  sort S .
  ops a b c : -> S .
  op _*_ : S S -> S [assoc comm] .
  vars X Y : S .
  eq X * X = X [variant] .
endfm
"#,
    );
    let mut output = r.eval("get variants [1] X * Y .").output;
    output.push('\n');
    output.push_str(&r.eval("continue 1 .").output);
    output.push('\n');
    output.push_str(&r.eval("continue 1 .").output);
    output.push('\n');
    output.push_str(&r.eval("variant unify X * a =? Y * b .").output);

    r.eval(
        r#"
fmod FOO is
  sort Foo .
  ops f g : Foo Foo -> Foo .
  op 1f : -> Foo .
  ops x y z : -> Foo .
  vars X Y Z : Foo .
  eq f(X, 1f) = X [variant] .
  eq f(1f, X) = X [variant] .
endfm
"#,
    );
    output.push('\n');
    output.push_str(
        &r.eval("variant match f(X, g(Y, Z)) <=? f(X, g(Y, Z)) .")
            .output,
    );

    assert_eq!(
        variant_sequence_lines(&output),
        [
            "get variants [1] in IDEM : X * Y .",
            "Variant 1",
            "rewrites: 0",
            "S: #1:S * #2:S",
            "X --> #1:S",
            "Y --> #2:S",
            "Variant 2",
            "rewrites: 1",
            "S: %1:S",
            "X --> %1:S",
            "Y --> %1:S",
            "No more variants.",
            "rewrites: 0",
            "variant unify in IDEM : X * a =? Y * b .",
            "Unifier 1",
            "rewrites: 2",
            "X --> b * %1:S",
            "Y --> a * %1:S",
            "Unifier 2",
            "rewrites: 2",
            "X --> b",
            "Y --> a",
            "No more unifiers.",
            "rewrites: 4",
            "variant match in FOO : f(X, g(Y, Z)) <=? f(X, g(Y, Z)) .",
            "rewrites: 1",
            "Matcher 1",
            "X --> X",
            "Y --> Y",
            "Z --> Z",
            "No more matchers.",
        ]
        .map(str::to_string)
    );
}

/// Oracle-indexed cache sequences from Maude 3.5.1. Besides the returned variants/unifiers/matcher,
/// the counts distinguish forward resume, equal-index reuse, backward restart, terminal-state deletion,
/// and exact four-entry MRU eviction; recomputing every request or retaining all historical answers fails.
#[test]
fn meta_variant_index_cache_matches_oracle() {
    let mut get = meta_variant_repl();
    let get_command =
        |n| format!("red metaGetVariant(['XOR], upTerm(X:XOR + cst1), empty, '#, {n}) .");
    let get_outputs: Vec<String> = [0, 1, 1, 0, 1, 2, 3]
        .into_iter()
        .map(|n| get.eval(&get_command(n)).output)
        .collect();
    assert_eq!(
        get_outputs
            .iter()
            .map(|out| one_rewrite_count(out))
            .collect::<Vec<_>>(),
        [3, 6, 3, 3, 6, 3, 3]
    );
    assert!(
        get_outputs[0].contains(
            "result Variant: {'_+_['cst1.Elem, '%1:XOR], \n  'X:XOR <- '%1:XOR, '%, (none).Parent, false}"
        ),
        "initial tuple: {}",
        get_outputs[0]
    );
    assert!(
        get_outputs[1]
            .contains("result Variant: {'cst1.Elem, \n  'X:XOR <- '0.XOR, '@, (0).Zero, true}"),
        "first child tuple: {}",
        get_outputs[1]
    );
    assert!(
        get_outputs[6].contains(
            "result Variant: {'@1:XOR, \n  'X:XOR <- '_+_['cst1.Elem, '@1:XOR], '@, (0).Zero, false}"
        ),
        "last layer tuple: {}",
        get_outputs[6]
    );

    let mut capacity = meta_variant_repl();
    let capacity_requests = [
        ("cst1", "#"),
        ("cst2", "#"),
        ("cst3", "#"),
        ("cst4", "#"),
        ("cst1", "#"),
        ("cst1", "@"),
        ("cst2", "#"),
        ("cst1", "#"),
    ];
    let capacity_counts: Vec<_> = capacity_requests
        .into_iter()
        .map(|(constant, family)| {
            let command = format!(
                "red metaGetVariant(['XOR], upTerm(X:XOR + {constant}), empty, '{family}, 1) ."
            );
            one_rewrite_count(&capacity.eval(&command).output)
        })
        .collect();
    assert_eq!(capacity_counts, [6, 6, 6, 6, 3, 6, 6, 3]);

    let mut unify = meta_variant_repl();
    let unify_command = |n| {
        format!(
            "red metaVariantUnify(['XOR], upTerm(X:XOR + cst1) =? \
             upTerm(Y:XOR + cst2), empty, '#, none, {n}) ."
        )
    };
    let unify_outputs: Vec<String> = [0, 1, 1, 0, 1]
        .into_iter()
        .map(|n| unify.eval(&unify_command(n)).output)
        .collect();
    assert_eq!(
        unify_outputs
            .iter()
            .map(|out| one_rewrite_count(out))
            .collect::<Vec<_>>(),
        [10, 4, 4, 10, 4]
    );
    assert!(
        unify_outputs[0].contains(
            "'X:XOR <- '_+_['cst2.Elem, '@1:XOR] ; \n  'Y:XOR <- '_+_['cst1.Elem, '@1:XOR], '@}"
        ),
        "first meta unifier: {}",
        unify_outputs[0]
    );
    assert!(
        unify_outputs[1].contains("'X:XOR <- 'cst2.Elem ; \n  'Y:XOR <- 'cst1.Elem, '@}"),
        "second meta unifier: {}",
        unify_outputs[1]
    );

    let match_command = |n| {
        format!(
            "red metaVariantMatch(['XOR], upTerm(cst1 + X:XOR) <=? \
             upTerm(cst2 + Y:XOR), empty, '#, none, {n}) ."
        )
    };
    let match_outputs: Vec<String> = [0, 1, 1, 0, 1]
        .into_iter()
        .map(|n| unify.eval(&match_command(n)).output)
        .collect();
    assert_eq!(
        match_outputs
            .iter()
            .map(|out| one_rewrite_count(out))
            .collect::<Vec<_>>(),
        [7, 4, 7, 7, 4]
    );
    assert!(
        match_outputs[0].contains("'X:XOR <- '_+_['cst1.Elem, 'cst2.Elem, 'Y:XOR]"),
        "meta matcher: {}",
        match_outputs[0]
    );
    assert!(
        match_outputs[1].contains("result Substitution?: (noMatch).Substitution?"),
        "terminal meta match: {}",
        match_outputs[1]
    );
}

/// Maude 3.5.1 returns `noUnifierIncomplete` after the two reported associative unifiers; exhaustion
/// must preserve the unifier's incompleteness bit rather than silently returning plain `noUnifier`.
#[test]
fn meta_variant_incomplete_result_matches_oracle() {
    let mut r = meta_variant_repl();
    let output = r
        .eval(
            r#"
fmod A-UNIF is
  sorts List Elt .
  subsort Elt < List .
  op __ : List List -> List [assoc] .
  ops a b c : -> Elt .
  vars A B C : List .
endfm
fmod META-A-TEST is
  inc A-UNIF .
  inc META-LEVEL .
endfm
red metaVariantUnify(['A-UNIF], upTerm(A:List B:List) =?
    upTerm(B:List C:List), empty, '%, none, 2) .
"#,
        )
        .output;
    assert_eq!(one_rewrite_count(&output), 4, "oracle count: {output}");
    assert!(
        output.contains("result UnificationPair?: (noUnifierIncomplete).UnificationPair?"),
        "associative incompleteness: {output}"
    );
}

/// TNK-018: a child interpreter receives a view through the real `upView -> down_view -> insertView`
/// path. The reflected op-to-term sources carry typed variables but no separate variable-declaration
/// field; both mixfix variable positions must still recover as operator holes.
#[test]
fn reflected_mixfix_term_map_survives_child_insert_view() {
    let mut r = repl();
    let prelude = r.eval(conformance_file!("prelude-meta.maude"));
    assert!(
        !prelude.exit && !prelude.output.contains("error in module"),
        "META-LEVEL prelude loads: {}",
        prelude.output
    );
    let stock = r.eval(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../metaInterpreter.maude"
    )));
    assert!(
        !stock.exit && !stock.output.contains("error in module"),
        "stock meta-interpreter loads: {}",
        stock.output
    );
    let output = r
        .eval(
            r#"
set include BOOL off .

fth TNK18-SOURCE is
  sorts Elt Oid Msg .
  op to_from_get : Oid Oid -> Msg .
  op to_from_answer(_) : Oid Oid Elt -> Msg .
endfth

fmod TNK18-TARGET is
  sorts Item Oid Msg .
  op fetch : Oid Oid -> Msg .
  op reply : Oid Oid Item -> Msg .
endfm

view TNK18-VIEW from TNK18-SOURCE to TNK18-TARGET is
  sort Elt to Item .
  vars O O' : Oid .
  var X : Elt .
  msg to O from O' get to term fetch(O, O') .
  msg to O from O' answer(X) to term reply(O, O', X) .
endv

mod TNK18-DRIVER is
  protecting TNK18-SOURCE .
  protecting TNK18-TARGET .
  protecting META-INTERPRETER .

  sort ViewCmd ModuleCmd Seq .
  subsort ViewCmd ModuleCmd < Seq .
  op v : Qid -> ViewCmd .
  op m : Qid -> ModuleCmd .
  op __ : Seq Seq -> Seq [assoc id: nil] .
  op nil : -> Seq .
  op predef : -> Seq .
  eq predef = m('TNK18-SOURCE) m('TNK18-TARGET) v('TNK18-VIEW) .

  op me : -> Oid .
  op User : -> Cid .
  op pending:_ : Seq -> Attribute .

  vars X Y Z : Oid .
  var Q : Qid .
  var Rest : Seq .
  var AS : AttributeSet .

  rl < X : User | pending: (m(Q) Rest), AS > createdInterpreter(X, Y, Z) =>
     < X : User | pending: Rest, AS > insertModule(Z, X, upModule(Q, false)) .
  rl < X : User | pending: (m(Q) Rest), AS > insertedModule(X, Y) =>
     < X : User | pending: Rest, AS > insertModule(Y, X, upModule(Q, false)) .
  rl < X : User | pending: (v(Q) Rest), AS > insertedModule(X, Y) =>
     < X : User | pending: Rest, AS > insertView(Y, X, upView(Q)) .
endm

erewrite in TNK18-DRIVER :
  <> < me : User | pending: predef >
  createInterpreter(interpreterManager, me, none) .
"#,
        )
        .output;

    assert!(
        !output.contains("Bad view.")
            && !output.contains("interpreterError")
            && !output.contains("error in module"),
        "reflected view insertion succeeds: {output}"
    );
    assert!(
        output.contains("rewrites: 7"),
        "oracle-compatible count: {output}"
    );
    assert!(
        output.contains("insertedView(me, interpreter(0))") && output.contains("pending: nil"),
        "child accepted the reflected mixfix term map: {output}"
    );
}

/// COV-003: the full reflected-view matrix must survive `upView -> insertView`, instantiate a
/// parameterized client in the child, and execute every mapped form rather than merely accepting it.
#[test]
fn reflected_term_map_matrix_survives_child_execution() {
    let mut r = repl();
    let prelude = r.eval(conformance_file!("prelude-meta.maude"));
    assert!(
        !prelude.exit && !prelude.output.contains("error in module"),
        "META-LEVEL prelude loads: {}",
        prelude.output
    );
    let stock = r.eval(include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../metaInterpreter.maude"
    )));
    assert!(
        !stock.exit && !stock.output.contains("error in module"),
        "stock meta-interpreter loads: {}",
        stock.output
    );
    let fixture = conformance_file!("subsystems/I28-reflected-view-term-maps.maude").replacen(
        "load metaInterpreter\n",
        "",
        1,
    );
    let output = r.eval(&fixture).output;

    assert!(
        !output.contains("Bad view.")
            && !output.contains("interpreterError")
            && !output.contains("error in module"),
        "reflected view and child modules load: {output}"
    );
    assert!(
        output.contains("functional: reducedTerm(me, interpreter(0), 21")
            && output.contains("'probe['s_^6['0.Zero]")
            && output.contains("'s_^16['0.Zero]")
            && output.contains("'s_^4['0.Zero]")
            && output.contains("'s_^5['0.Zero]")
            && output.contains("'s_^26['0.Zero]")
            && output.contains("'s_^37[")
            && output.contains("'aux1.AuxT]"),
        "all functional mappings execute in the child: {output}"
    );
    assert!(
        output.contains("messaging: rewroteTerm(me, interpreter(0),")
            && output.contains("4, '__['done['s_^8['0.Zero]]")
            && output.contains("pending: nil"),
        "both inherited message mappings execute in the child: {output}"
    );
}

/// COV-002 / OUT-003: retain tnk's known context-free cross-kind suffix spelling without
/// ratifying it as an accepted divergence. Maude prints `.B`; tnk currently prints `.[B]`.
#[test]
fn cross_kind_ill_sorted_suffix_remains_classified() {
    let output = repl()
        .eval(conformance_file!(
            "probes/cross-kind-ill-sorted-output.maude"
        ))
        .output;
    assert!(
        output.contains(
            "reduce in COV002-ILL-SORTED-OUTPUT : (f(a1)).B .\n\
             rewrites: 1 in 0ms cpu (0ms real) (~ rewrites/second)\n\
             result B: b"
        ),
        "applicable first profile: {output}"
    );
    assert!(
        output.contains(
            "reduce in COV002-ILL-SORTED-OUTPUT : (f(a2)).[B] .\n\
             rewrites: 0 in 0ms cpu (0ms real) (~ rewrites/second)\n\
             result [B]: (f(a2)).[B]"
        ),
        "classified ill-sorted spelling: {output}"
    );
}
