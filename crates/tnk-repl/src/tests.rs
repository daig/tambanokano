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

/// A rule in a functional module (`fmod`) is rejected — rules belong only to system modules (`mod`).
#[test]
fn rule_in_fmod_is_rejected() {
    let out = repl()
        .eval("fmod F is sort S . ops a b : -> S . rl a => b . endfm")
        .output;
    assert!(out.contains("not allowed in a functional module"), "rejection: {out}");
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
