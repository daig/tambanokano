//! `tnk-repl` — the tambanokano interactive shell (the Phase-1 end milestone).
//!
//! [`Repl`] is the terminal-free engine: it holds the persistent interner, the module database, the
//! built (flattened) modules, and the current module, and turns one input submission into output via
//! [`Repl::eval`]. The `tnk-repl` binary ([`main`](../main.rs)) is a thin `rustyline` driver that buffers
//! multi-line input ([`Repl::input_complete`]) and prints `eval`'s output. Everything below the dispatch
//! is reused as-is: flatten + build (`tnk-modules`/`tnk-frontend`), `reduce_command`/`match_command`/
//! `format_matchers`, and the pretty-printer.

mod trace;
mod wrap;

use std::collections::HashMap;
use tnk_frontend::lex::{tokenize, Interner, Token, TokKind};
use tnk_core::dag::DagId;
use tnk_core::rewrite::Rewriting;
use tnk_core::search::Search;
use tnk_frontend::build_term::VarIndex;
use tnk_frontend::load::{
    build_command_dag, build_loaded_module, command_echo, erewrite_command, format_matchers,
    frewrite_command, match_command, rewrite_command, search_command, LoadedModule,
};
use tnk_frontend::pretty::print_pretty;
use tnk_frontend::surface::ast::{Command, ModuleExpr, OpMap, PreModule, SearchArrow, TopItem, ViewDecl};
use tnk_frontend::surface::parser::Parser;
use tnk_modules::db::ModuleDb;
use tnk_modules::flatten::flatten;
use tnk_modules::meta::MetaDescent;
use tnk_modules::view::{validate_view, ViewDb};
use trace::{render_trace, TraceFlags};

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
    /// Validated view definitions (B-ii), keyed by name.
    views: ViewDb,
    /// Module names in entry order (for `show modules`).
    order: Vec<String>,
    /// View names in entry order (for `show views`).
    view_order: Vec<String>,
    /// The current module commands run against (Maude's selected module).
    current: Option<String>,
    /// Colorize printed results (true interactively, false in tests).
    color: bool,
    /// The full `trace` flags (`set trace [<option>] on|off`); `master` off by default.
    trace: TraceFlags,
    /// The last resumable session (`rewrite`/`frewrite` or `search`) and the module name it ran in, for
    /// `continue` (and `show path`/`show search graph`). Any non-`continue` command (or a module rebuild /
    /// `select`) clears it — Maude's continuation invalidation. Stays valid between commands because the
    /// REPL runs with in-reduction GC off, so the session's terms are never collected.
    last: Option<(String, Continuation)>,
    /// Pending `stdin` for `erewrite`'s `getLine` (Pillar 2.5-C). Set via [`set_stdin`](Self::set_stdin)
    /// (tests / piped input); moved into the running module's engine when an `erewrite` command starts.
    stdin: String,
}

/// A resumable session stored for `continue` / `show`.
enum Continuation {
    /// A `rewrite`/`frewrite` session.
    Rewrite(Rewriting),
    /// A `search` session (the state graph + the goal's variable index for rendering). Boxed: the search
    /// state graph is much larger than a `Rewriting`, so this keeps the enum (and the `last` slot) small.
    Search(Box<SearchSession>),
}

/// A `search` session plus what the REPL needs to render and resume it.
struct SearchSession {
    search: Search,
    /// The goal pattern's variables (for the `X:Sort --> value` solution lines).
    vars: VarIndex,
}

impl Repl {
    pub fn new(color: bool) -> Self {
        Self {
            interner: Interner::new(),
            db: ModuleDb::new(),
            modules: HashMap::new(),
            views: ViewDb::new(),
            order: Vec::new(),
            view_order: Vec::new(),
            current: None,
            color,
            trace: TraceFlags::default(),
            last: None,
            stdin: String::new(),
        }
    }

    /// Provide `stdin` input for `erewrite`'s `getLine` (Pillar 2.5-C) — the scripted/piped input stream.
    pub fn set_stdin(&mut self, input: impl Into<String>) {
        self.stdin = input.into();
    }

    /// The current module's name, if any (for the prompt / introspection).
    pub fn current(&self) -> Option<&str> {
        self.current.as_deref()
    }

    /// Evaluate one (complete) input submission: a module, a command, or a REPL meta-command. The output
    /// is line-wrapped exactly as Maude's stdout wrapper ([`wrap::auto_wrap`]) so a long result (e.g.
    /// `fib(22)`'s numeral) is laid out byte-for-byte like the reference binary (C13).
    pub fn eval(&mut self, input: &str) -> Eval {
        let mut ev = self.eval_dispatch(input);
        ev.output = wrap::auto_wrap(&ev.output);
        ev
    }

    /// The dispatch behind [`eval`](Self::eval): produces the unwrapped output text. A submission may
    /// hold several statements — a loaded `.maude` file freely mixes module definitions, commands, and
    /// `set`/`show`/`select`/`quit` meta-commands — so it is split into complete statements (the same
    /// boundary [`input_complete`](Self::input_complete) uses, so a multi-line module stays one chunk)
    /// and each is dispatched in turn. This is why a file's mid-stream `set trace on .` is handled rather
    /// than mis-parsed as a term.
    fn eval_dispatch(&mut self, input: &str) -> Eval {
        let mut output = String::new();
        let mut buffer = String::new();
        for line in input.lines() {
            buffer.push_str(line);
            buffer.push('\n');
            if self.input_complete(&buffer) {
                let ev = self.dispatch_one(&buffer);
                buffer.clear();
                append_block(&mut output, &ev.output);
                if ev.exit {
                    return Eval { output: output.trim_end().to_string(), exit: true };
                }
            }
        }
        // A trailing statement with no terminator (e.g. a partial interactive line) — dispatch it
        // best-effort so its parse error surfaces rather than being silently dropped.
        if !buffer.trim().is_empty() {
            let ev = self.dispatch_one(&buffer);
            append_block(&mut output, &ev.output);
        }
        Eval { output: output.trim_end().to_string(), exit: false }
    }

    /// Dispatch ONE complete statement: a `set`/`show`/`select`/`quit` meta-command (by its first word),
    /// or a module definition / command parsed via [`Parser::parse_top_item`].
    fn dispatch_one(&mut self, input: &str) -> Eval {
        let trimmed = input.trim();
        if trimmed.is_empty() {
            return Eval::default();
        }
        // REPL meta-commands dispatch on the first word.
        match trimmed.split_whitespace().next().unwrap_or("") {
            "quit" | "q" | "exit" => return Eval { output: "Bye.".into(), exit: true },
            "select" => return self.meta_select(trimmed),
            "show" => return self.meta_show(trimmed),
            "set" => return self.meta_set(trimmed),
            _ => {}
        }

        // Otherwise: module definitions and reduce/match/rewrite/search commands. Collect the parsed
        // items first so the `Parser`'s shared borrow of the interner is released before we mutate it.
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
                TopItem::View(v) => self.enter_view(v, &mut output),
                TopItem::Command(c) => self.run_command(c, &mut output),
            }
        }
        Eval { output: output.trim_end().to_string(), exit: false }
    }

    /// Define (or redefine) a module: insert into the DB, flatten its import closure, build it, and make
    /// it current. Silent on success (as Maude is); flatten/build errors become output.
    fn enter_module(&mut self, pm: PreModule, out: &mut String) {
        let name = pm.name.clone();
        self.last = None; // a (re)built module invalidates any saved rewrite continuation
        self.db.insert(pm);
        let built = flatten(&name, &self.db, &self.views, &mut self.interner)
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

    /// Define (or redefine) a view (B-ii): validate it against the module DB and store it. Silent on
    /// success (as Maude is); a validation error becomes output. A view is the argument of an
    /// instantiation `M{V}` (B-iv); on its own it is just validated and shown (`show view`).
    fn enter_view(&mut self, v: ViewDecl, out: &mut String) {
        match validate_view(&v, &self.db, &mut self.interner) {
            Ok(()) => {
                if !self.views.contains(&v.name) {
                    self.view_order.push(v.name.clone());
                }
                self.views.insert(v);
            }
            Err(e) => out.push_str(&format!("error: {e}\n")),
        }
    }

    /// Run a `reduce`/`match` command against the current module.
    fn run_command(&mut self, c: Command, out: &mut String) {
        // An `in <MODULE> :` qualifier overrides the current module for this one command (Maude's
        // `red in NAT : t .`); without it, the current module is used.
        let m_override = match &c {
            Command::Reduce { module, .. }
            | Command::Match { module, .. }
            | Command::Rewrite { module, .. }
            | Command::Frewrite { module, .. }
            | Command::ERewrite { module, .. }
            | Command::Search { module, .. }
            | Command::Srewrite { module, .. } => module.clone(),
            Command::Continue { .. } => None,
        };
        let Some(cur) = m_override.or_else(|| self.current.clone()) else {
            out.push_str("no current module — enter a module first.\n");
            return;
        };
        if !self.modules.contains_key(&cur) {
            out.push_str(&format!("error: module `{cur}` does not exist.\n"));
            return;
        }
        match c {
            Command::Reduce { term, .. } => {
                self.last = None; // a non-continue command invalidates the saved rewrite continuation
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                // Maude echoes the *normalized, pretty-printed* parsed term (special constants collapsed,
                // AC args canonically ordered), not the raw input; fall back to the token join if it
                // somehow does not parse (the reduce below then reports the real error).
                let echo = command_echo(lm, &self.interner, &term, self.color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                lm.built.engine.set_trace(self.trace.master);
                lm.built.engine.set_record_whole(self.trace.master && self.trace.whole);
                // Build the subject, then reduce driving META-LEVEL descent: a `metaReduce(…)` redex is
                // handed to `MetaDescent`, which down-translates its meta-module argument into a real
                // object module (resolving imports from the db) and reduces in it. The descent borrows the
                // interner mutably, so it is dropped before the (immutable-interner) pretty-print.
                let reduced = build_command_dag(lm, &self.interner, &term).map(|dag| {
                    let mut descent =
                        MetaDescent { interner: &mut self.interner, db: &self.db, views: &self.views };
                    let result = lm.built.engine.reduce_with(dag, &mut descent);
                    (result, lm.built.engine.rewrites())
                });
                match reduced {
                    Ok((dag, rw)) => {
                        let events = lm.built.engine.take_trace();
                        let trace = render_trace(&lm.built, &self.interner, &events, self.trace, self.color);
                        let eng = &lm.built.engine;
                        let sort = eng.sorts().name(eng.sort_of(dag)).to_string();
                        let value = print_pretty(&lm.built, &self.interner, dag, self.color);
                        out.push_str(&format!(
                            "reduce in {cur} : {echo} .\n{trace}\
                             rewrites: {rw} in 0ms cpu (0ms real) (~ rewrites/second)\n\
                             result {sort}: {value}\n"
                        ));
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Match { pattern, subject, xmatch, .. } => {
                self.last = None;
                let (pe, se) =
                    (join_tokens(&pattern, &self.interner), join_tokens(&subject, &self.interner));
                let kw = if xmatch { "xmatch" } else { "match" };
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.set_trace(false); // the match's subject-reduce is not traced (yet)
                lm.built.engine.set_record_whole(false);
                match match_command(lm, &self.interner, &pattern, &subject, xmatch) {
                    Ok(blocks) => out.push_str(&format!(
                        "{kw} in {cur} : {pe} <=? {se} .\n\
                         Decision time: 0ms cpu (0ms real)\n\n{}\n",
                        format_matchers(&blocks)
                    )),
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Rewrite { bound, term, .. } => {
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.reset_counter(); // a fresh `rewrite` restarts the `counter` built-in
                let echo = command_echo(lm, &self.interner, &term, self.color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                lm.built.engine.set_trace(self.trace.master);
                lm.built.engine.set_record_whole(self.trace.master && self.trace.whole);
                let bound_str = bound.map(|n| format!(" [{n}]")).unwrap_or_default();
                match rewrite_command(lm, &self.interner, &term) {
                    Ok(mut rw) => {
                        let body = render_rewriting(lm, &self.interner, self.trace, self.color, &mut rw, bound);
                        out.push_str(&format!("rewrite{bound_str} in {cur} : {echo} .\n{body}"));
                        // `lm`'s borrow ends above; save the session so `continue` can resume it.
                        self.last = Some((cur.clone(), Continuation::Rewrite(rw)));
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Frewrite { bound, term, .. } => {
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.reset_counter(); // a fresh `frewrite` restarts the `counter` built-in
                let echo = command_echo(lm, &self.interner, &term, self.color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                lm.built.engine.set_trace(self.trace.master);
                lm.built.engine.set_record_whole(self.trace.master && self.trace.whole);
                let bound_str = bound.map(|n| format!(" [{n}]")).unwrap_or_default();
                // Maude's `frewrite` default gas is one rule application per position per pass.
                match frewrite_command(lm, &self.interner, &term, 1) {
                    Ok(mut rw) => {
                        let body = render_rewriting(lm, &self.interner, self.trace, self.color, &mut rw, bound);
                        out.push_str(&format!("frewrite{bound_str} in {cur} : {echo} .\n{body}"));
                        self.last = Some((cur.clone(), Continuation::Rewrite(rw)));
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::ERewrite { bound, gas, term, .. } => {
                let stdin = std::mem::take(&mut self.stdin); // move the scripted input in before borrowing lm
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.reset_counter(); // a fresh `erewrite` restarts the `counter` built-in
                lm.built.engine.reset_external(); // and the EXTERNAL-mode stream output + reply mailbox
                lm.built.engine.set_external_input(stdin); // `getLine` reads from here
                let echo = command_echo(lm, &self.interner, &term, self.color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                lm.built.engine.set_trace(self.trace.master);
                lm.built.engine.set_record_whole(self.trace.master && self.trace.whole);
                // Maude's `erewrite [n]` / `[n, g]`: `n` bounds deliveries, `g` (default 1) is the gas.
                // The echo shows the bound exactly as written (`[n]` or `[n, g]`).
                let bound_str = match (bound, gas) {
                    (Some(n), Some(g)) => format!(" [{n}, {g}]"),
                    (Some(n), None) => format!(" [{n}]"),
                    _ => String::new(),
                };
                match erewrite_command(lm, &self.interner, &term, gas.unwrap_or(1)) {
                    Ok(mut rw) => {
                        let body = render_rewriting(lm, &self.interner, self.trace, self.color, &mut rw, bound);
                        // Side-channel `stdout` writes (Pillar 2.5-C) are interleaved by Maude after the
                        // command echo, before the `rewrites:`/`result` lines — surface them there.
                        let ext = lm.built.engine.take_external_out();
                        out.push_str(&format!("erewrite{bound_str} in {cur} : {echo} .\n{ext}{body}"));
                        self.last = Some((cur.clone(), Continuation::Rewrite(rw)));
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
                // Thread the unread `stdin` back (a command that didn't `getLine` leaves it intact, so a
                // later command in another module can still read it). Re-borrow after `lm`'s use ends.
                if let Some(lm) = self.modules.get_mut(&cur) {
                    self.stdin = lm.built.engine.take_external_input();
                }
            }
            Command::Search { max_solutions, max_depth, subject, arrow, pattern, such_that, .. } => {
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.set_trace(false); // search is not traced (yet)
                lm.built.engine.set_record_whole(false);
                let header = search_header(lm, &self.interner, &subject, arrow, &pattern, such_that.as_deref(), self.color);
                let bound_str = match (max_solutions, max_depth) {
                    (None, None) => String::new(),
                    (Some(n), None) => format!(" [{n}]"),
                    (Some(n), Some(m)) => format!(" [{n}, {m}]"),
                    (None, Some(m)) => format!(" [, {m}]"),
                };
                match search_command(lm, &self.interner, &subject, arrow, &pattern, such_that.as_deref(), max_depth) {
                    Ok((search, vars)) => {
                        let mut session = SearchSession { search, vars };
                        let body = render_search(&mut session, lm, &self.interner, self.color, max_solutions);
                        out.push_str(&format!("search{bound_str} in {cur} : {header} .\n{body}"));
                        self.last = Some((cur.clone(), Continuation::Search(Box::new(session))));
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Srewrite { depth_first, term, strategy, .. } => {
                self.last = None;
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                let kw = if depth_first { "dsrewrite" } else { "srewrite" };
                let echo = command_echo(lm, &self.interner, &term, self.color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                let strat_str = tnk_frontend::strategy::print_strategy(&strategy, &self.interner);
                match tnk_frontend::strategy::srewrite_command(
                    lm, &self.interner, &term, &strategy, depth_first,
                ) {
                    Ok((sols, total)) => {
                        let rate = "0ms cpu (0ms real) (~ rewrites/second)";
                        let mut body = String::new();
                        if sols.is_empty() {
                            body.push_str(&format!("\nNo solution.\nrewrites: {total} in {rate}\n"));
                        } else {
                            let eng = &lm.built.engine;
                            for (k, s) in sols.iter().enumerate() {
                                let sort = eng.sorts().name(eng.sort_of(s.term)).to_string();
                                let value = print_pretty(&lm.built, &self.interner, s.term, self.color);
                                body.push_str(&format!(
                                    "\nSolution {}\nrewrites: {} in {rate}\nresult {sort}: {value}\n",
                                    k + 1,
                                    s.rewrites
                                ));
                            }
                            body.push_str(&format!("\nNo more solutions.\nrewrites: {total} in {rate}\n"));
                        }
                        out.push_str(&format!("{kw} in {cur} : {echo} using {strat_str} .\n{body}"));
                    }
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                }
            }
            Command::Continue { bound } => match self.last.take() {
                Some((m, Continuation::Rewrite(mut rw))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    lm.built.engine.set_trace(self.trace.master);
                    lm.built.engine.set_record_whole(self.trace.master && self.trace.whole);
                    // `continue` reports the rewrites done in this continuation (Maude resets the count).
                    lm.built.engine.reset_rewrites();
                    let body = render_rewriting(lm, &self.interner, self.trace, self.color, &mut rw, bound);
                    out.push_str(&body);
                    self.last = Some((m, Continuation::Rewrite(rw)));
                }
                Some((m, Continuation::Search(mut session))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    // `continue` reports the rewrites done in this continuation (Maude resets the count),
                    // so states generated now snapshot a fresh count.
                    lm.built.engine.reset_rewrites();
                    let body = render_search(&mut session, lm, &self.interner, self.color, bound);
                    out.push_str(&body);
                    self.last = Some((m, Continuation::Search(session)));
                }
                // (`session` is a `Box<SearchSession>`; `&mut session` derefs to the inner session.)
                _ => out.push_str("No previous rewriting or search to continue in this module.\n"),
            },
        }
    }

    /// `select <NAME> .` — make `NAME` the current module.
    fn meta_select(&mut self, line: &str) -> Eval {
        let name = line.split_whitespace().nth(1).map(|s| s.trim_end_matches('.')).unwrap_or("");
        let out = if name.is_empty() {
            "select: expected a module name.".to_string()
        } else if self.modules.contains_key(name) {
            self.current = Some(name.to_string());
            self.last = None; // switching modules invalidates the saved rewrite continuation
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
            Some("views") => {
                let list =
                    if self.view_order.is_empty() { "(none)".into() } else { self.view_order.join(" ") };
                format!("views: {list}")
            }
            Some("view") => match words.get(2).and_then(|n| self.views.get(n)) {
                Some(v) => render_view(v, &self.interner),
                None => "show view: no such view (usage: `show view NAME .`).".into(),
            },
            // `show path N .` — the transition path from the initial state to state N of the last search.
            Some("path") => {
                let n: Option<usize> = words.get(2).and_then(|s| s.parse().ok());
                match (n, self.current.as_deref()) {
                    (Some(n), Some(cur)) => match &self.last {
                        Some((m, Continuation::Search(session))) if m == cur => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_path(&session.search, lm, &self.interner, n, self.color)
                        }
                        _ => "show path: no current search (run `search` first).".into(),
                    },
                    (None, _) => "show path: expected a state number.".into(),
                    _ => "show path: no current module.".into(),
                }
            }
            // `show search graph .` — the whole reachable-state graph of the last search.
            Some("search") if words.get(3).copied() == Some("graph") || words.get(2).copied() == Some("graph") => {
                match self.current.as_deref() {
                    Some(cur) => match &self.last {
                        Some((m, Continuation::Search(session))) if m == cur => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_graph(&session.search, lm, &self.interner, self.color)
                        }
                        _ => "show search graph: no current search.".into(),
                    },
                    None => "show search graph: no current module.".into(),
                }
            }
            _ => "show: try `show module .` / `show modules .` / `show view NAME .` / `show views .` / `show path N .` / `show search graph .`".into(),
        };
        Eval { output: out, exit: false }
    }

    /// `set trace [<option>] on|off` — the full `trace` flag surface (master + body / substitution /
    /// rewrite / whole / condition / eqs / mbs / builtin). Other `set` options are a follow-up.
    fn meta_set(&mut self, line: &str) -> Eval {
        let words: Vec<&str> =
            line.split_whitespace().map(|s| s.trim_end_matches('.')).filter(|s| !s.is_empty()).collect();
        let out = match words.get(1).copied() {
            Some("trace") => self.trace.apply(&words[2..]).err().unwrap_or_default(),
            // Every other interpreter directive (`set show advisories off`, `set include … on/off`,
            // `set oo include … on`, …) is a silent no-op, as the file-loading parser already treats
            // `set` (we never auto-import, and these toggles do not affect our output). Silence matches
            // Maude — it applies these without echoing — so loaded `.maude` files stay byte-comparable.
            _ => String::new(),
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
        // Track module nesting, but only count a module keyword (`fmod`/`endfm`/…) when it is a real
        // delimiter: at bracket depth 0 and in statement-leading position. The meta-level's
        // module-constructor operators put `fmod`/`is`/`sorts`/`endfm` *inside* a term
        // (`getName(fmod Q is … endfm) = Q`), where they are operator-name fragments, not delimiters —
        // counting those would close the module early and submit it without its `endfm`.
        let is_close =
            |s: &str| matches!(s, "endfm" | "endm" | "endfth" | "endth" | "endv" | "endsm" | "endsth");
        let mut open = false;
        let mut saw_open = false;
        let mut depth = 0i32;
        let mut leading = true; // start, just after a depth-0 `.`, or just after a module delimiter
        for t in &toks {
            let txt = self.interner.resolve(t.sym);
            // An *open* keyword only starts a module in statement-leading position at depth 0: this keeps
            // a command's module-constructor term (`reduce metaReduce(['NAT], …)` / `red fmod … endfm .`)
            // from looking like a module. A *close* keyword only counts at depth 0, so the meta-level's
            // module-constructor operators (`getName(fmod Q is … endfm)`) — whose `endfm` is an
            // operator-name fragment inside brackets — never close the surrounding module early.
            if depth == 0 && leading && matches!(txt, "fmod" | "mod" | "fth" | "th" | "smod" | "sth" | "view") {
                open = true;
                saw_open = true;
            }
            if depth == 0 && is_close(txt) {
                open = false;
            }
            match txt {
                "(" | "[" | "{" => depth += 1,
                ")" | "]" | "}" => depth -= 1,
                _ => {}
            }
            leading = (t.kind == TokKind::Dot && depth == 0) || is_close(txt);
        }
        let last_txt = self.interner.resolve(last.sym);
        let module_closed = is_close(last_txt) && saw_open && !open && depth == 0;
        module_closed || (last.kind == TokKind::Dot && depth == 0 && !open)
    }
}

/// Append a non-empty per-statement output block to the accumulated submission output, separating
/// consecutive blocks by a single newline.
fn append_block(out: &mut String, block: &str) {
    if !block.is_empty() {
        if !out.is_empty() {
            out.push('\n');
        }
        out.push_str(block);
    }
}

/// Join a token bubble back to text for the command echo (the `reduce in M : … .` / `match …` line),
/// applying Maude's mixfix spacing rules (`prettyPrint.cc::printTokens`): no space before a `,` or a
/// bracket, no space *after* an opening bracket, a single space elsewhere. This re-spaces the input
/// tokens — `g ( g ( a ) )` → `g(g(a))`, `< z , s z >` → `< z, s z >` — to match the reference binary's
/// echo on the common command forms. It preserves the input's surface form (numerals stay numerals,
/// operands keep their order) rather than re-parsing, so the one place it can differ from Maude is
/// redundant input parentheses (kept here; Maude's re-render drops them).
fn join_tokens(toks: &[Token], i: &Interner) -> String {
    let mut out = String::new();
    let mut no_space = true; // suppress the leading space, and the space after an opening bracket
    for t in toks {
        let text = i.resolve(t.sym);
        let open = matches!(text, "(" | "[" | "{");
        let close = matches!(text, ")" | "]" | "}");
        if !(no_space || open || close || text == ",") {
            out.push(' ');
        }
        out.push_str(text);
        no_space = open;
    }
    out
}

/// Run a `rewrite`/`continue` session and render the `rewrites: … / result …` block (shared by the
/// `rewrite` and `continue` commands). Runs `rw` for `bound` steps, renders any recorded trace, then the
/// count and the result — `result (sort not calculated): …` when a bounded `frewrite` stop left a
/// non-canonical term (Pillar A-ii).
fn render_rewriting(
    lm: &mut LoadedModule,
    i: &Interner,
    flags: TraceFlags,
    color: bool,
    rw: &mut Rewriting,
    bound: Option<u64>,
) -> String {
    let step = rw.run(&mut lm.built.engine, bound);
    let events = lm.built.engine.take_trace();
    let trace = render_trace(&lm.built, i, &events, flags, color);
    let eng = &lm.built.engine;
    let rw_count = eng.rewrites();
    let value = print_pretty(&lm.built, i, step.term, color);
    let result_line = if step.sort_known {
        let sort = eng.sorts().name(eng.sort_of(step.term)).to_string();
        format!("result {sort}: {value}")
    } else {
        format!("result (sort not calculated): {value}")
    };
    format!("{trace}rewrites: {rw_count} in 0ms cpu (0ms real) (~ rewrites/second)\n{result_line}\n")
}

/// The `search` command's echoed query: `{subject} {arrow} {pattern}[ such that {cond}]`.
fn search_header(
    lm: &mut LoadedModule,
    i: &Interner,
    subject: &[Token],
    arrow: SearchArrow,
    pattern: &[Token],
    such_that: Option<&[Token]>,
    color: bool,
) -> String {
    let subj = command_echo(lm, i, subject, color).unwrap_or_else(|_| join_tokens(subject, i));
    let arrow_str = match arrow {
        SearchArrow::One => "=>1",
        SearchArrow::Plus => "=>+",
        SearchArrow::Star => "=>*",
        SearchArrow::Bang => "=>!",
    };
    let mut h = format!("{subj} {arrow_str} {}", join_tokens(pattern, i));
    if let Some(c) = such_that {
        h.push_str(&format!(" such that {}", join_tokens(c, i)));
    }
    h
}

/// Pull up to `limit` more solutions from a search session, rendering each `Solution N (state K)` block;
/// on exhaustion append `No more solutions.` + the final stats. Shared by `search` and `continue`.
fn render_search(
    session: &mut SearchSession,
    lm: &mut LoadedModule,
    i: &Interner,
    color: bool,
    limit: Option<u64>,
) -> String {
    let mut out = String::new();
    let mut shown = 0u64;
    loop {
        if limit == Some(shown) {
            return out; // hit the per-invocation solution bound — continuable, no "No more solutions"
        }
        match session.search.next_solution(&mut lm.built.engine) {
            Some(sol) => {
                shown += 1;
                let bindings = render_search_bindings(lm, i, &session.vars, &sol.bindings, color);
                out.push_str(&format!(
                    "\nSolution {} (state {})\nstates: {}  rewrites: {} in 0ms cpu (0ms real) (~ rewrites/second)\n{bindings}\n",
                    sol.number, sol.state, sol.states, sol.rewrites
                ));
            }
            None => {
                let states = session.search.states();
                let rewrites = lm.built.engine.rewrites();
                out.push_str(&format!(
                    "\nNo more solutions.\nstates: {states}  rewrites: {rewrites} in 0ms cpu (0ms real) (~ rewrites/second)\n"
                ));
                return out;
            }
        }
    }
}

/// `Var --> value` lines for a search solution. The variable is rendered by its written name (Maude
/// echoes a goal variable as written: a declared `X` prints `X`, an on-the-fly `X:Sort` prints
/// `X:Sort` — the colon form is part of the variable name once on-the-fly variables are supported).
fn render_search_bindings(lm: &LoadedModule, i: &Interner, vars: &VarIndex, bindings: &[DagId], color: bool) -> String {
    if vars.count() == 0 {
        return "empty substitution".to_string();
    }
    (0..vars.count())
        .map(|k| {
            let value = print_pretty(&lm.built, i, bindings[k as usize], color);
            format!("{} --> {value}", vars.name(k))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Render `show path N`: the transition sequence from state 0 to state `n` — `state K, Sort: value`
/// lines separated by `===[ rule ]===>` arcs.
fn render_path(search: &Search, lm: &LoadedModule, i: &Interner, n: usize, color: bool) -> String {
    let steps = search.path(n);
    if steps.is_empty() {
        return format!("show path: no state {n}.");
    }
    let mut out = String::new();
    for (idx, step) in steps.iter().enumerate() {
        if idx > 0 {
            let rb = step.via.map(|r| trace::rule_body(&lm.built, i, r, color)).unwrap_or_default();
            out.push_str(&format!("===[ {rb} ]===>\n"));
        }
        let sort = lm.built.engine.sorts().name(lm.built.engine.sort_of(step.term));
        let value = print_pretty(&lm.built, i, step.term, color);
        out.push_str(&format!("state {}, {sort}: {value}\n", step.state));
    }
    out.trim_end().to_string()
}

/// Render `show search graph`: every state and its forward arcs (`arc N ===> state T (rule)`).
fn render_graph(search: &Search, lm: &LoadedModule, i: &Interner, color: bool) -> String {
    let graph = search.graph();
    let mut out = String::new();
    for (idx, (sidx, term, arcs)) in graph.iter().enumerate() {
        if idx > 0 {
            out.push('\n');
        }
        let sort = lm.built.engine.sorts().name(lm.built.engine.sort_of(*term));
        let value = print_pretty(&lm.built, i, *term, color);
        out.push_str(&format!("state {sidx}, {sort}: {value}\n"));
        let mut arc_n = 0;
        for (target, rules) in arcs {
            for rid in rules {
                let rb = trace::rule_body(&lm.built, i, *rid, color);
                out.push_str(&format!("arc {arc_n} ===> state {target} ({rb})\n"));
                arc_n += 1;
            }
        }
    }
    out.trim_end().to_string()
}

/// A `show view` rendering (B-ii): the `view N from T to M is … endv` form, sort maps then op maps. Close
/// to the reference binary's layout (two-space indent); the exact-spacing fidelity of `show` is a REPL
/// concern, like `show module`.
fn render_view(v: &ViewDecl, i: &Interner) -> String {
    let mut s = format!(
        "view {} from {} to {} is\n",
        v.name,
        module_expr_str(&v.from),
        module_expr_str(&v.to)
    );
    for (a, b) in &v.sort_maps {
        s.push_str(&format!("  sort {a} to {b} .\n"));
    }
    for m in &v.op_maps {
        match m {
            OpMap::Op { from, to } => {
                s.push_str(&format!("  op {} to {} .\n", join_tokens(from, i), join_tokens(to, i)));
            }
            OpMap::Term { from, to } => {
                s.push_str(&format!("  op {} to term {} .\n", join_tokens(from, i), join_tokens(to, i)));
            }
        }
    }
    s.push_str("endv");
    s
}

/// Render a module expression as text (for `show view`'s from/to). B-ii from/to are named modules.
fn module_expr_str(e: &ModuleExpr) -> String {
    match e {
        ModuleExpr::Named(n) => n.clone(),
        ModuleExpr::Sum(a, b) => format!("{} + {}", module_expr_str(a), module_expr_str(b)),
        ModuleExpr::Rename(inner, _) => format!("{} * (…)", module_expr_str(inner)),
        ModuleExpr::Instantiation(base, args) => {
            let parts: Vec<String> = args.iter().map(module_expr_str).collect();
            format!("{}{{{}}}", module_expr_str(base), parts.join(", "))
        }
    }
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
