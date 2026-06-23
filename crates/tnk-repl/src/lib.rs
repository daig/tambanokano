//! `tnk-repl` — the tambanokano interactive shell (the Phase-1 end milestone).
//!
//! [`Repl`] is the terminal-free engine: it holds the persistent interner, the module database, the
//! built (flattened) modules, and the current module, and turns one input submission into output via
//! [`Repl::eval`]. The `tnk-repl` binary ([`main`](../main.rs)) is a thin `rustyline` driver that buffers
//! multi-line input ([`Repl::input_complete`]) and prints `eval`'s output. Everything below the dispatch
//! is reused as-is: flatten + build (`tnk-modules`/`tnk-frontend`), `reduce_command`/`match_command`/
//! `format_matchers`, and the pretty-printer.

use std::collections::HashMap;
use tnk_frontend::lex::{tokenize, Interner, Token, TokKind};
use tnk_frontend::load::{
    build_loaded_module, format_matchers, match_command, reduce_command, LoadedModule,
};
use tnk_frontend::pretty::print_pretty;
use tnk_frontend::surface::ast::{Command, PreModule, TopItem};
use tnk_frontend::surface::parser::Parser;
use tnk_modules::db::ModuleDb;
use tnk_modules::flatten::flatten;

/// The result of evaluating one input submission: the text to print, and whether to exit the loop.
#[derive(Debug, Default)]
pub struct Eval {
    pub output: String,
    pub exit: bool,
}

/// The interactive shell's state. One persistent [`Interner`] backs all submissions so module names,
/// operators, and command terms intern consistently.
pub struct Repl {
    interner: Interner,
    /// Parsed `PreModule`s (the input to flattening — an importer re-flattens its closure from here).
    db: ModuleDb,
    /// Flattened + built modules, keyed by name.
    modules: HashMap<String, LoadedModule>,
    /// Module names in entry order (for `show modules`).
    order: Vec<String>,
    /// The current module commands run against (Maude's selected module).
    current: Option<String>,
    /// Colorize printed results (true interactively, false in tests).
    color: bool,
}

impl Repl {
    pub fn new(color: bool) -> Self {
        Self {
            interner: Interner::new(),
            db: ModuleDb::new(),
            modules: HashMap::new(),
            order: Vec::new(),
            current: None,
            color,
        }
    }

    /// The current module's name, if any (for the prompt / introspection).
    pub fn current(&self) -> Option<&str> {
        self.current.as_deref()
    }

    /// Evaluate one (complete) input submission: a module, a command, or a REPL meta-command.
    pub fn eval(&mut self, input: &str) -> Eval {
        let trimmed = input.trim();
        if trimmed.is_empty() {
            return Eval::default();
        }
        // REPL meta-commands dispatch on the first word.
        match trimmed.split_whitespace().next().unwrap_or("") {
            "quit" | "q" | "exit" => return Eval { output: "Bye.".into(), exit: true },
            "select" => return self.meta_select(trimmed),
            "show" => return self.meta_show(trimmed),
            "set" => {
                return Eval {
                    output: "set: no options in this build (trace/options are a follow-up)".into(),
                    exit: false,
                }
            }
            _ => {}
        }

        // Otherwise: module definitions and reduce/match commands. Collect the parsed items first so the
        // `Parser`'s shared borrow of the interner is released before we mutate it (flatten/build/reduce).
        let mut output = String::new();
        let toks = tokenize(input, &mut self.interner);
        let items = {
            let mut p = Parser::new(&toks, &self.interner);
            let mut items = Vec::new();
            loop {
                match p.parse_top_item() {
                    Ok(Some(it)) => items.push(it),
                    Ok(None) => break,
                    Err(e) => {
                        output.push_str(&format!("parse error: {e}\n"));
                        break;
                    }
                }
            }
            items
        };
        for item in items {
            match item {
                TopItem::Module(pm) => self.enter_module(pm, &mut output),
                TopItem::Command(c) => self.run_command(c, &mut output),
            }
        }
        Eval { output: output.trim_end().to_string(), exit: false }
    }

    /// Define (or redefine) a module: insert into the DB, flatten its import closure, build it, and make
    /// it current. Silent on success (as Maude is); flatten/build errors become output.
    fn enter_module(&mut self, pm: PreModule, out: &mut String) {
        let name = pm.name.clone();
        self.db.insert(pm);
        let built = flatten(&name, &self.db, &mut self.interner)
            .and_then(|flat| build_loaded_module(&flat, &mut self.interner));
        match built {
            Ok(lm) => {
                if !self.modules.contains_key(&name) {
                    self.order.push(name.clone());
                }
                self.modules.insert(name.clone(), lm);
                self.current = Some(name);
            }
            Err(e) => out.push_str(&format!("error in module `{name}`: {e}\n")),
        }
    }

    /// Run a `reduce`/`match` command against the current module.
    fn run_command(&mut self, c: Command, out: &mut String) {
        let Some(cur) = self.current.clone() else {
            out.push_str("no current module — enter a module first.\n");
            return;
        };
        match c {
            Command::Reduce { term } => {
                let echo = join_tokens(&term, &self.interner);
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                match reduce_command(lm, &self.interner, &term) {
                    Ok((dag, rw)) => {
                        let eng = &lm.built.engine;
                        let sort = eng.sorts().name(eng.sort_of(dag)).to_string();
                        let value = print_pretty(&lm.built, &self.interner, dag, self.color);
                        out.push_str(&format!(
                            "reduce in {cur} : {echo} .\n\
                             rewrites: {rw} in 0ms cpu (0ms real) (~ rewrites/second)\n\
                             result {sort}: {value}\n"
                        ));
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Match { pattern, subject, xmatch } => {
                let (pe, se) =
                    (join_tokens(&pattern, &self.interner), join_tokens(&subject, &self.interner));
                let kw = if xmatch { "xmatch" } else { "match" };
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                match match_command(lm, &self.interner, &pattern, &subject, xmatch) {
                    Ok(blocks) => out.push_str(&format!(
                        "{kw} in {cur} : {pe} <=? {se} .\n\
                         Decision time: 0ms cpu (0ms real)\n\n{}\n",
                        format_matchers(&blocks)
                    )),
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
        }
    }

    /// `select <NAME> .` — make `NAME` the current module.
    fn meta_select(&mut self, line: &str) -> Eval {
        let name = line.split_whitespace().nth(1).map(|s| s.trim_end_matches('.')).unwrap_or("");
        let out = if name.is_empty() {
            "select: expected a module name.".to_string()
        } else if self.modules.contains_key(name) {
            self.current = Some(name.to_string());
            String::new()
        } else {
            format!("select: no module `{name}` — enter it first.")
        };
        Eval { output: out, exit: false }
    }

    /// `show modules` (the entered names) or `show module [NAME]` (a module's sorts + ops).
    fn meta_show(&mut self, line: &str) -> Eval {
        let words: Vec<&str> =
            line.split_whitespace().map(|s| s.trim_end_matches('.')).filter(|s| !s.is_empty()).collect();
        let out = match words.get(1).copied() {
            Some("modules") => {
                let list = if self.order.is_empty() { "(none)".into() } else { self.order.join(" ") };
                format!("modules: {list}")
            }
            Some("module") => {
                let name = words.get(2).map(|s| s.to_string()).or_else(|| self.current.clone());
                match name.as_deref().and_then(|n| self.modules.get(n).map(|lm| (n, lm))) {
                    Some((n, lm)) => render_module(n, lm),
                    None => "show module: no such module (and no current module).".into(),
                }
            }
            _ => "show: try `show module .` or `show modules .`".into(),
        };
        Eval { output: out, exit: false }
    }

    /// Whether `input` forms a complete submission — the multi-line buffer boundary for the binary.
    /// Complete iff it is a bare `quit`/`q`/`exit`, or its last token closes a module (`endfm`/…) or is a
    /// terminator `.` at module-depth 0 (so a half-typed module body keeps buffering).
    pub fn input_complete(&mut self, input: &str) -> bool {
        let trimmed = input.trim();
        if trimmed.is_empty() {
            return false;
        }
        if matches!(trimmed, "quit" | "q" | "exit") {
            return true;
        }
        let toks = tokenize(input, &mut self.interner);
        let Some(last) = toks.last().copied() else { return false };
        let mut open = false;
        for t in &toks {
            match self.interner.resolve(t.sym) {
                "fmod" | "mod" | "fth" | "th" => open = true,
                "endfm" | "endm" | "endfth" | "endth" => open = false,
                _ => {}
            }
        }
        let last_txt = self.interner.resolve(last.sym);
        matches!(last_txt, "endfm" | "endm" | "endfth" | "endth")
            || (last.kind == TokKind::Dot && !open)
    }
}

/// Join a token bubble back to text (the command echo). Spaces between every token — readable, not a
/// faithful re-render (the *result* is pretty-printed; this is just the `reduce in M : …` line).
fn join_tokens(toks: &[Token], i: &Interner) -> String {
    toks.iter().map(|t| i.resolve(t.sym)).collect::<Vec<_>>().join(" ")
}

/// A `show module` rendering: name + sorts + ops (name/arity). (Statements live in the engine, not the
/// `BuiltModule`, so they are not counted here.)
fn render_module(name: &str, lm: &LoadedModule) -> String {
    let b = &lm.built;
    let mut sorts: Vec<&str> = b.sorts.keys().map(String::as_str).collect();
    sorts.sort_unstable();
    let mut ops: Vec<String> = b.ops.keys().map(|(n, a)| format!("{n}/{a}")).collect();
    ops.sort_unstable();
    format!("fmod {name}\n  sorts: {}\n  ops: {}", sorts.join(" "), ops.join(" "))
}

#[cfg(test)]
mod tests;
