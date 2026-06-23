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
/// becomes newSort`. `cmb` fires as a membership but its trial uses the `cmb …` body.
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
