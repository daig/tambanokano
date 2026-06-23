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
