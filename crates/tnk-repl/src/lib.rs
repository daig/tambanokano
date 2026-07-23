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

use std::collections::{HashMap, HashSet};
use tnk_core::dag::DagId;
use tnk_core::rewrite::Rewriting;
use tnk_core::search::Search;
use tnk_core::smt::{ConfiguredSmtEngine, SmtEngine, SmtResult};
use tnk_frontend::build_term::VarIndex;
use tnk_frontend::lex::{Interner, TokKind, Token, tokenize};
use tnk_frontend::load::{
    InternerNames, LoadedModule, build_command_dag, build_logic_command_dag, command_echo,
    command_variable_display_name, erewrite_command, format_matchers, frewrite_command,
    match_command, maude_variable_name_rank, narrow_command, render_unifier, rewrite_command,
    search_command, smt_search_command, unify_command, variant_command, variant_match_command,
    variant_unify_command,
};
use tnk_frontend::pretty::{print_pretty, print_pretty_with_variables};
use tnk_frontend::surface::ast::{
    Command, ModuleExpr, NarrowDisplay, OpMap, PreModule, SearchArrow, TopItem, ViewDecl,
};
use tnk_frontend::surface::parser::Parser;
use tnk_modules::db::ModuleDb;
use tnk_modules::load::{flatten_and_build, module_dep_names, view_dep_names};
use tnk_modules::meta::{MetaDescent, MetaState};
use tnk_modules::view::{ViewDb, validate_view};
use trace::{TraceFlags, render_trace};

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
    /// Reflection-core search state retained across commands, including Maude's metalevel
    /// variant-unification cache.
    meta_state: MetaState,
    /// The direct dependency set of every defined module **and** view, keyed by name (a module/view name →
    /// the module/view names its flatten closure references directly). Maintained on every (re)definition
    /// so that redefining a name can re-flatten its transitive dependents (A4c): a redefinition of `M`
    /// leaves the *cached* build of an importer `N` referring to the old `M`, so we rebuild the importers.
    deps: HashMap<String, HashSet<String>>,
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
    /// `set include BOOL on|off` (decision D11): while on, every entered module gets an implicit
    /// `protecting BOOL .` (Maude's auto-import, prelude.maude:3233 turns it on after BOOL exists;
    /// the prelude's own early modules build while it is off). Default off — the engine/library
    /// layer stays prelude-free; the standing prelude flips it via its own `set include` line.
    include_bool: bool,
    /// Canonicalized paths already `load`ed — `sload` (skip-load) consults this and loads only once.
    loaded_files: std::collections::HashSet<std::path::PathBuf>,
    /// `set show timing on|off` (Maude default on): gates the `Decision time:` line of
    /// `match`/`xmatch`/`unify` (the only commands whose output the flag affects — `reduce`/`rewrite`
    /// timing tails are already normalized away). Other timing-tail lines are hardcoded 0ms.
    show_timing: bool,
    show_breakdown: bool,
    /// `set verbose on|off`: show narrowing fold decisions and terminal state counts.
    verbose: bool,
    /// Unequal identity-collapse notices already emitted by a lazy symbolic command. Maude
    /// computes this property once per operator, so `set verbose on` prints each notice once.
    reported_identity_collapses: HashSet<(String, tnk_core::symbol::SymbolId)>,
}

/// A resumable session stored for `continue` / `show`.
enum Continuation {
    /// A `rewrite`/`frewrite` session.
    Rewrite(Rewriting),
    /// A `search` session (the state graph + the goal's variable index for rendering). Boxed: the search
    /// state graph is much larger than a `Rewriting`, so this keeps the enum (and the `last` slot) small.
    Search(Box<SearchSession>),
    /// An SMT rewrite-sequence search with accumulated constraints.
    SmtSearch(Box<SmtSearchSession>),
    /// A folding-variant enumeration, including its external numbering and output mode.
    Variants(Box<VariantSession>),
    /// A plain/filtered variant-unification enumeration.
    VariantUnifiers(Box<VariantUnifySession>),
    Narrow(Box<NarrowSession>),
}

/// A `search` session plus what the REPL needs to render and resume it.
struct SearchSession {
    search: Search,
    /// The goal pattern's variables (for the `X:Sort --> value` solution lines).
    vars: VarIndex,
}

struct SmtSearchSession {
    search: tnk_core::smt_search::SmtSearch,
    goal_variables: VarIndex,
    target_variable_count: u32,
    shown_total: u32,
}

/// A `get variants` session plus the source names needed for substitution rendering.
struct VariantSession {
    search: tnk_core::variant::VariantSearch,
    var_names: Vec<String>,
    irredundant: bool,
    reported_total: bool,
}

struct VariantUnifySession {
    search: tnk_core::variant::VariantSearch,
    var_names: Vec<String>,
    upfront: bool,
    matching: bool,
    subject: Option<DagId>,
    restorations: Vec<(DagId, DagId)>,
    fresh_base: String,
    prepared: bool,
    exhausted: bool,
    reported_total: bool,
    next_number: u64,
    stream: tnk_core::variant::FilteredVariantUnifierStream,
}

struct NarrowSession {
    search: tnk_core::narrow::NarrowSearch,
    variables: VarIndex,
    initial_variable_count: usize,
    initial_variables: Option<Vec<VarIndex>>,
    initial_echoes: Vec<String>,
    next_number: u64,
    path: bool,
}

impl Repl {
    pub fn new(color: bool) -> Self {
        Self {
            interner: Interner::new(),
            db: ModuleDb::new(),
            modules: HashMap::new(),
            views: ViewDb::new(),
            meta_state: MetaState::default(),
            deps: HashMap::new(),
            order: Vec::new(),
            view_order: Vec::new(),
            current: None,
            color,
            trace: TraceFlags::default(),
            last: None,
            stdin: String::new(),
            include_bool: false,
            loaded_files: std::collections::HashSet::new(),
            show_timing: true,
            show_breakdown: false,
            verbose: false,
            reported_identity_collapses: HashSet::new(),
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
                    return Eval {
                        output: output.trim_end().to_string(),
                        exit: true,
                    };
                }
            }
        }
        // A trailing statement with no terminator (e.g. a partial interactive line) — dispatch it
        // best-effort so its parse error surfaces rather than being silently dropped.
        if !buffer.trim().is_empty() {
            let ev = self.dispatch_one(&buffer);
            append_block(&mut output, &ev.output);
        }
        Eval {
            output: output.trim_end().to_string(),
            exit: false,
        }
    }

    /// Dispatch ONE complete statement: a `set`/`show`/`select`/`quit` meta-command (by its first word),
    /// or a module definition / command parsed via [`Parser::parse_top_item`].
    fn dispatch_one(&mut self, input: &str) -> Eval {
        if input.trim().is_empty() {
            return Eval::default();
        }
        // Tokenize once so the meta-command dispatch keys on the first *token* (comments already stripped
        // by the lexer) rather than the first raw word: a `***`/`---` comment on the line before
        // `select`/`show`/`set` no longer desyncs it (fable-audit.md §3.4 — the comment-before-select bug).
        // The meta handlers re-space the tokens (`join_tokens`), which keeps structured names (`LIST{Nat}`)
        // intact and drops the comment prefix.
        let toks = tokenize(input, &mut self.interner);
        let Some(first) = toks.first().map(|t| self.interner.resolve(t.sym)) else {
            return Eval::default(); // comment-only / blank submission
        };
        match first {
            "quit" | "q" | "exit" => {
                return Eval {
                    output: "Bye.".into(),
                    exit: true,
                };
            }
            "load" | "sload" => {
                // Filename = the raw text after the keyword on ITS line, to end of line (Maude:
                // no `.` terminator). Comments may precede the load line in the chunk, so find
                // the line whose first word is the keyword rather than slicing the raw input.
                let path = input
                    .lines()
                    .map(str::trim)
                    .find(|l| l.split_whitespace().next() == Some(first))
                    .and_then(|l| l.split_once(char::is_whitespace))
                    .map(|(_, rest)| rest.trim())
                    .unwrap_or("");
                return self.meta_load(first == "sload", path);
            }
            "select" => return self.meta_select(&join_tokens(&toks, &self.interner)),
            "show" => return self.meta_show(&join_tokens(&toks, &self.interner)),
            "set" => return self.meta_set(&join_tokens(&toks, &self.interner)),
            _ => {}
        }

        // Otherwise: module definitions and reduce/match/rewrite/search commands. Collect the parsed
        // items first so the `Parser`'s shared borrow of the interner is released before we mutate it.
        let mut output = String::new();
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
        // Two commands on one line: Maude rejects the whole line (its command reader takes everything up to
        // the terminating `.`, so trailing tokens make the command ill-formed). tnk buffers one physical
        // submission at a time, so a *single-line* `red a . red b .` arrives here as several parsed items —
        // reject the whole submission when any command is followed by another item. Commands on SEPARATE
        // lines are separate submissions (each its own `dispatch_one`), so multi-command files are
        // unaffected (fable-audit.md §3.4). A module/view followed by a trailing command is Maude-legal and
        // left alone (the command is the last item — nothing follows it).
        if items
            .iter()
            .enumerate()
            .any(|(k, it)| matches!(it, TopItem::Command(_)) && k + 1 < items.len())
        {
            // The diagnostic text is stripped by the diff harness; the pin is that no results appear.
            output.push_str("error: more than one command on a line.\n");
            return Eval {
                output: output.trim_end().to_string(),
                exit: false,
            };
        }
        for item in items {
            match item {
                TopItem::Module(pm) => self.enter_module(pm, &mut output),
                TopItem::View(v) => self.enter_view(v, &mut output),
                TopItem::Command(c) => self.run_command(c, &mut output),
            }
        }
        Eval {
            output: output.trim_end().to_string(),
            exit: false,
        }
    }

    /// Define (or redefine) a module: insert into the DB, flatten its import closure, build it, and make
    /// it current. Silent on success (as Maude is); flatten/build errors become output.
    fn enter_module(&mut self, pm: PreModule, out: &mut String) {
        let mut pm = pm;
        let name = pm.name.clone();
        // Implicit BOOL (D11 / fable-audit.md §3.4): while `set include BOOL on`, every module
        // gets `protecting BOOL .` injected (Maude's auto-import). An explicit BOOL import
        // dedups in flatten's visited set, so injection is idempotent.
        if self.include_bool && name != "BOOL" && self.db.get("BOOL").is_some() {
            pm.imports.insert(
                0,
                tnk_frontend::surface::ast::Import {
                    mode: tnk_frontend::surface::ast::ImportMode::Protecting,
                    expr: tnk_frontend::surface::ast::ModuleExpr::Named("BOOL".into()),
                },
            );
        }
        self.last = None; // a (re)built module invalidates any saved rewrite continuation
        self.meta_state.clear(); // rebuilt engines invalidate persistent metalevel DAG keys
        // Record this module's direct dependencies (imports + parameter theories) so a later redefinition
        // of anything it references can find and re-flatten it (A4c).
        self.deps.insert(name.clone(), module_dep_names(&pm));
        // Inject any built-in prelude module this module imports (e.g. an `omod`'s auto-imported
        // `CONFIGURATION`) that the user has not defined, so flattening can resolve it.
        let imports = pm.imports.clone();
        self.db.insert(pm);
        tnk_modules::prelude::ensure_builtins(&imports, &mut self.db, &mut self.interner);
        // Flatten + build with the D1a import-reparse point-fix: an imported statement the flattened
        // grammar parses ambiguously re-parses against its home module's own (already-built) grammar. The
        // module cache resolves each statement's home; the borrow of `self.modules` is scoped so this
        // module's own insertion below is unobstructed.
        let built = {
            let mods = &self.modules;
            let home_mod = |n: &str| mods.get(n);
            flatten_and_build(&name, &self.db, &self.views, &home_mod, &mut self.interner)
        };
        match built {
            Ok(lm) => {
                if !self.modules.contains_key(&name) {
                    self.order.push(name.clone());
                }
                self.reported_identity_collapses
                    .retain(|(module, _)| module != &name);
                self.modules.insert(name.clone(), lm);
                self.current = Some(name.clone());
            }
            Err(e) => out.push_str(&format!("error in module `{name}`: {e}\n")),
        }
        // A (re)definition of `name` invalidates the cached builds of every module that transitively
        // depends on it: re-flatten and rebuild them so `reduce in <dependent>` uses the new definition.
        // On a first definition this is a no-op (nothing built imports a name that was undefined until
        // now), so ordinary loads pay only a cheap empty reverse-reachability walk.
        self.rebuild_dependents(&name, out);
    }

    /// Define (or redefine) a view (B-ii): validate it against the module DB and store it. Silent on
    /// success (as Maude is); a validation error becomes output. A view is the argument of an
    /// instantiation `M{V}` (B-iv); on its own it is just validated and shown (`show view`).
    fn enter_view(&mut self, v: ViewDecl, out: &mut String) {
        match validate_view(&v, &self.db, &self.views, &mut self.interner) {
            Ok(()) => {
                let name = v.name.clone();
                // Record the view's direct dependencies (its from/to modules + parameter theories) and
                // store it.
                self.deps.insert(name.clone(), view_dep_names(&v));
                if !self.views.contains(&v.name) {
                    self.view_order.push(v.name.clone());
                }
                self.views.insert(v);
                self.meta_state.clear(); // view semantics participate in reflected module construction
                // A redefined view leaves the cached builds of modules that instantiate with it stale
                // (`M{V}` was flattened with the old view), so re-flatten its transitive dependents (A4c).
                self.rebuild_dependents(&name, out);
            }
            Err(e) => out.push_str(&format!("error: {e}\n")),
        }
    }

    /// Re-flatten and rebuild every currently-built module that transitively depends on `changed` (a
    /// module or view name that was just (re)defined). Flattening reads the module database and view store
    /// directly — never the cached [`modules`](Self::modules) map — so each dependent is rebuilt
    /// independently (rebuild order is irrelevant) and picks up the new definition. A dependent's own
    /// source is unchanged, so its recorded direct dependencies stay valid and need no refresh. If any
    /// module is rebuilt, the saved rewrite/search continuation is dropped (its engine is replaced).
    fn rebuild_dependents(&mut self, changed: &str, out: &mut String) {
        // Reverse-reachability over the direct-dependency graph: every name that reaches `changed`.
        let mut dependents: HashSet<String> = HashSet::new();
        let mut frontier = vec![changed.to_string()];
        while let Some(cur) = frontier.pop() {
            for (name, ds) in &self.deps {
                if ds.contains(&cur) && dependents.insert(name.clone()) {
                    frontier.push(name.clone());
                }
            }
        }
        // Rebuild only the ones that are actually built modules (views aren't built; a dependent that
        // failed to build earlier isn't cached). The changed name itself was already (re)built by the
        // caller, so exclude it.
        let mut rebuilt = false;
        for name in dependents {
            if name == changed || !self.modules.contains_key(&name) {
                continue;
            }
            let built = {
                let mods = &self.modules;
                let home_mod = |n: &str| mods.get(n);
                flatten_and_build(&name, &self.db, &self.views, &home_mod, &mut self.interner)
            };
            match built {
                Ok(lm) => {
                    self.reported_identity_collapses
                        .retain(|(module, _)| module != &name);
                    self.modules.insert(name, lm);
                    rebuilt = true;
                }
                Err(e) => out.push_str(&format!("error in module `{name}`: {e}\n")),
            }
        }
        if rebuilt {
            self.last = None;
        }
    }

    /// Run a `reduce`/`match` command against the current module.
    fn run_command(&mut self, c: Command, out: &mut String) {
        // A `[0]` component in a bracketed bound (`rewrite`/`frewrite`/`erewrite`/`search`) is illegal:
        // Maude rejects it at parse ("bad token in / no parse for term|command") — before resolving the
        // module — so the command produces no output, while the following legal commands still run
        // (fable-audit.md §3.6, C4e). Every bound slot rejects a 0 (verified against the oracle: bound and
        // gas for `frewrite [n, g]`/`erewrite`, and both solution/depth bounds for `search [n, m]`).
        // `continue`'s bare number is a different grammar and DOES allow 0, so it is not checked here.
        let zero_bound = match &c {
            Command::Rewrite { bound, .. } => *bound == Some(0),
            Command::Frewrite { bound, gas, .. } | Command::ERewrite { bound, gas, .. } => {
                *bound == Some(0) || *gas == Some(0)
            }
            Command::Search {
                max_solutions,
                max_depth,
                ..
            }
            | Command::SmtSearch {
                max_solutions,
                max_depth,
                ..
            } => *max_solutions == Some(0) || *max_depth == Some(0),
            Command::GetVariants { bound, .. }
            | Command::VariantUnify { bound, .. }
            | Command::VariantMatch { bound, .. } => *bound == Some(0),
            Command::Narrow {
                max_solutions,
                max_depth,
                ..
            } => *max_solutions == Some(0) || *max_depth == Some(0),
            _ => false,
        };
        if zero_bound {
            // The diagnostic is stripped by the diff harness (a `parse error:` line); the pin is that the
            // rejected command emits no echo/result.
            out.push_str("parse error: a `[0]` bound is not allowed.\n");
            return;
        }
        // An `in <MODULE> :` qualifier overrides the current module for this one command (Maude's
        // `red in NAT : t .`); without it, the current module is used.
        let m_override = match &c {
            Command::Reduce { module, .. }
            | Command::Check { module, .. }
            | Command::Match { module, .. }
            | Command::Rewrite { module, .. }
            | Command::Frewrite { module, .. }
            | Command::ERewrite { module, .. }
            | Command::Search { module, .. }
            | Command::SmtSearch { module, .. }
            | Command::Unify { module, .. }
            | Command::GetVariants { module, .. }
            | Command::VariantUnify { module, .. }
            | Command::VariantMatch { module, .. }
            | Command::Narrow { module, .. }
            | Command::Srewrite { module, .. } => module.clone(),
            Command::ShowNarrowing { .. } | Command::Continue { .. } => None,
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
                    let mut descent = MetaDescent::new(
                        &mut self.interner,
                        &self.db,
                        &self.views,
                        &mut self.meta_state,
                    );
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
            Command::Check { term, .. } => {
                self.last = None;
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                let echo = command_echo(lm, &self.interner, &term, self.color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                match build_logic_command_dag(lm, &self.interner, &term) {
                    Ok(dag) => {
                        let mut solver = ConfiguredSmtEngine::default();
                        let result = solver.check_dag(&lm.built.engine, dag);
                        out.push_str(&format!("check in {cur} : {echo} .\n"));
                        match result {
                            SmtResult::Sat => {
                                out.push_str("Result from sat solver is: sat\n");
                            }
                            SmtResult::Unsat => {
                                out.push_str("Result from sat solver is: unsat\n");
                            }
                            SmtResult::Unknown => {
                                out.push_str("Result from sat solver is: undecided\n");
                            }
                            SmtResult::BadDag => {}
                        }
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
                let dtime = if self.show_timing { "Decision time: 0ms cpu (0ms real)\n" } else { "" };
                match match_command(lm, &self.interner, &pattern, &subject, xmatch) {
                    Ok(blocks) => out.push_str(&format!(
                        "{kw} in {cur} : {pe} <=? {se} .\n{dtime}\n{}\n",
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
            Command::Frewrite { bound, gas, term, .. } => {
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.reset_counter(); // a fresh `frewrite` restarts the `counter` built-in
                let echo = command_echo(lm, &self.interner, &term, self.color)
                    .unwrap_or_else(|_| join_tokens(&term, &self.interner));
                lm.built.engine.set_trace(self.trace.master);
                lm.built.engine.set_record_whole(self.trace.master && self.trace.whole);
                // The echo shows the bound exactly as written (`[n]` or `[n, g]`); Maude's default gas is
                // one rule application per position per pass (fable-audit.md §3.4).
                let bound_str = match (bound, gas) {
                    (Some(n), Some(g)) => format!(" [{n}, {g}]"),
                    (Some(n), None) => format!(" [{n}]"),
                    (None, Some(g)) => format!(" [, {g}]"),
                    _ => String::new(),
                };
                match frewrite_command(lm, &self.interner, &term, gas.unwrap_or(1)) {
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
            Command::SmtSearch {
                max_solutions,
                max_depth,
                subject,
                arrow,
                pattern,
                such_that,
                ..
            } => {
                self.last = None;
                if matches!(arrow, SearchArrow::Bang) {
                    return;
                }
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                lm.built.engine.set_trace(false);
                lm.built.engine.set_record_whole(false);
                let header = search_header(
                    lm,
                    &self.interner,
                    &subject,
                    arrow,
                    &pattern,
                    such_that.as_deref(),
                    self.color,
                );
                let bound_str = match (max_solutions, max_depth) {
                    (None, None) => String::new(),
                    (Some(n), None) => format!(" [{n}]"),
                    (Some(n), Some(m)) => format!(" [{n}, {m}]"),
                    (None, Some(m)) => format!(" [, {m}]"),
                };
                match smt_search_command(
                    lm,
                    &mut self.interner,
                    &subject,
                    arrow,
                    &pattern,
                    such_that.as_deref(),
                    max_depth,
                ) {
                    Ok(command) => {
                        let mut session = SmtSearchSession {
                            search: command.search,
                            goal_variables: command.goal_variables,
                            target_variable_count: command.target_variable_count,
                            shown_total: 0,
                        };
                        let body = render_smt_search(
                            &mut session,
                            lm,
                            &self.interner,
                            self.color,
                            self.show_timing,
                            max_solutions,
                        );
                        out.push_str(&format!(
                            "smt-search{bound_str} in {cur} : {header} .\n{body}"
                        ));
                        self.last =
                            Some((cur.clone(), Continuation::SmtSearch(Box::new(session))));
                    }
                    Err(_) => {}
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
            Command::Unify { bound, irredundant, body, .. } => {
                self.last = None;
                let limit = bound.unwrap_or(u64::MAX);
                let irr = if irredundant { "irredundant " } else { "" };
                let bnd = bound.map(|n| format!("[{n}] ")).unwrap_or_default();
                // The interner and the module engine are disjoint fields — borrow both.
                let (interner, modules) = (&mut self.interner, &mut self.modules);
                let lm = modules.get_mut(&cur).expect("current module is built");
                match unify_command(lm, interner, &body) {
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                    Ok(mut uc) => {
                        out.push_str(&format!("{irr}unify {bnd}in {cur} : {} .\n", uc.echo));
                        if !uc.names_ok || !uc.problem.problem_okay() {
                            // Screening failure (unimplemented theory) or an unsafe variable name —
                            // Maude emits only the (stripped) warning, no Decision time / unifiers.
                        } else {
                            // Collect unifiers (up to the bound) while the engine is borrowed, then
                            // render — print_pretty needs the interner immutably afterwards.
                            let mut unifiers: Vec<Vec<DagId>> = Vec::new();
                            let incomplete;
                            {
                                let mut names = InternerNames(interner);
                                let mut env = tnk_core::unify::UnifyEnv {
                                    e: &mut lm.built.engine,
                                    names: &mut names,
                                };
                                while (unifiers.len() as u64) < limit {
                                    match uc.problem.find_next(&mut env) {
                                        Some(b) => unifiers.push(b),
                                        None => break,
                                    }
                                }
                                incomplete = uc.problem.is_incomplete();
                            }
                            let _ = incomplete; // the incomplete-warning text is phase-E (stripped)
                            // `irredundant`: keep only the most-general unifiers (Maude's
                            // UnifierFilter), in enumeration order, then renumber on display.
                            if irredundant {
                                unifiers =
                                    tnk_core::unify::filter::irredundant(&mut lm.built.engine, unifiers);
                            }
                            if self.show_timing {
                                out.push_str("Decision time: 0ms cpu (0ms real)\n");
                            }
                            if unifiers.is_empty() {
                                out.push_str("No unifier.\n");
                            } else {
                                for (n, u) in unifiers.iter().enumerate() {
                                    out.push_str(&format!(
                                        "\nUnifier {}\n{}\n",
                                        n + 1,
                                        render_unifier(&lm.built, interner, &uc.var_names, u)
                                    ));
                                }
                            }
                        }
                    }
                }
            }
            Command::GetVariants { bound, irredundant, term, blockers, .. } => {
                self.last = None;
                let irr = if irredundant { "irredundant " } else { "" };
                let bnd = bound.map(|n| format!(" [{n}]")).unwrap_or_default();
                let (interner, modules) = (&mut self.interner, &mut self.modules);
                let lm = modules.get_mut(&cur).expect("current module is built");
                let blocker_terms = (!blockers.is_empty()).then_some(blockers.as_slice());
                match variant_command(lm, interner, &term, blocker_terms, irredundant) {
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                    Ok(vc) => {
                        out.push_str(&format!("get {irr}variants{bnd} in {cur} : {} .\n", vc.echo));
                        if vc.names_ok {
                            let mut session = VariantSession {
                                search: vc.search,
                                var_names: vc.var_names,
                                irredundant,
                                reported_total: false,
                            };
                            let body = render_variants(&mut session, lm, interner, self.color, bound);
                            out.push_str(&body);
                            self.last = Some((cur.clone(), Continuation::Variants(Box::new(session))));
                        }
                    }
                }
            }
            Command::VariantUnify { bound, filtered, body, blockers, .. } => {
                self.last = None;
                let prefix = if filtered { "filtered " } else { "" };
                let bnd = bound.map(|n| format!(" [{n}]")).unwrap_or_default();
                let (interner, modules) = (&mut self.interner, &mut self.modules);
                let lm = modules.get_mut(&cur).expect("current module is built");
                let blocker_terms = (!blockers.is_empty()).then_some(blockers.as_slice());
                match variant_unify_command(lm, interner, &body, blocker_terms, filtered) {
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                    Ok(vc) => {
                        out.push_str(&format!(
                            "{prefix}variant unify{bnd} in {cur} : {} .\n",
                            vc.echo
                        ));
                        if vc.names_ok {
                            let mut session = VariantUnifySession {
                                search: vc.search,
                                var_names: vc.var_names,
                                stream: tnk_core::variant::FilteredVariantUnifierStream::new(filtered),
                                upfront: filtered,
                                matching: false,
                                subject: None,
                                restorations: Vec::new(),
                                fresh_base: "0".to_string(),
                                prepared: false,
                                exhausted: false,
                                reported_total: false,
                                next_number: 0,
                            };
                            let body =
                                render_variant_unifiers(&mut session, lm, interner, bound);
                            out.push_str(&body);
                            self.last =
                                Some((cur.clone(), Continuation::VariantUnifiers(Box::new(session))));
                        }
                    }
                }
            }
            Command::VariantMatch { bound, pattern, subject, blockers, .. } => {
                self.last = None;
                let bnd = bound.map(|n| format!(" [{n}]")).unwrap_or_default();
                let (interner, modules) = (&mut self.interner, &mut self.modules);
                let lm = modules.get_mut(&cur).expect("current module is built");
                let blocker_terms = (!blockers.is_empty()).then_some(blockers.as_slice());
                match variant_match_command(lm, interner, &pattern, &subject, blocker_terms) {
                    Err(e) => out.push_str(&format!("error: {e}\n")),
                    Ok(vc) => {
                        out.push_str(&format!(
                            "variant match{bnd} in {cur} : {} .\n",
                            vc.echo
                        ));
                        if vc.names_ok {
                            let mut session = VariantUnifySession {
                                search: vc.search,
                                var_names: vc.var_names,
                                stream: tnk_core::variant::FilteredVariantUnifierStream::new(false),
                                upfront: true,
                                matching: true,
                                subject: Some(vc.subject),
                                restorations: vc.restorations,
                                fresh_base: vc.fresh_base,
                                prepared: false,
                                exhausted: false,
                                reported_total: false,
                                next_number: 0,
                            };
                            let body =
                                render_variant_unifiers(&mut session, lm, interner, bound);
                            out.push_str(&body);
                            self.last = Some((
                                cur.clone(),
                                Continuation::VariantUnifiers(Box::new(session)),
                            ));
                        }
                    }
                }
            }
            Command::Narrow {
                max_solutions,
                max_depth,
                subject,
                arrow,
                goal,
                condition,
                fold,
                vfold,
                path,
                filter,
                delay,
                fvu,
                ..
            } => {
                self.last = None;
                if condition.is_some() {
                    out.push_str("error: conditions are not currently supported for narrowing.\n");
                    return;
                }
                let bound_str = match (max_solutions, max_depth) {
                    (None, None) => String::new(),
                    (Some(n), None) => format!(" [{n}]"),
                    (Some(n), Some(m)) => format!(" [{n}, {m}]"),
                    (None, Some(m)) => format!(" [, {m}]"),
                };
                let prefix = if fvu {
                    String::new()
                } else {
                    let mut options = Vec::new();
                    if fold {
                        options.push("fold");
                    }
                    if vfold {
                        options.push("vfold");
                    }
                    if path {
                        options.push("path");
                    }
                    if options.is_empty() {
                        String::new()
                    } else {
                        format!("{{{}}} ", options.join(", "))
                    }
                };
                let keyword = if fvu { "fvu-narrow" } else { "vu-narrow" };
                let mut stream_options = Vec::new();
                if delay {
                    stream_options.push("delay");
                }
                if filter {
                    stream_options.push("filter");
                }
                let stream_options = if stream_options.is_empty() {
                    String::new()
                } else {
                    format!(" {{{}}}", stream_options.join(", "))
                };
                let arrow_echo = match arrow {
                    SearchArrow::One => "=>1",
                    SearchArrow::Plus => "=>+",
                    SearchArrow::Star => "=>*",
                    SearchArrow::Bang => "=>!",
                };
                let verbose = self.verbose;
                let (interner, modules, reported_identity_collapses) = (
                    &mut self.interner,
                    &mut self.modules,
                    &mut self.reported_identity_collapses,
                );
                let lm = modules.get_mut(&cur).expect("current module is built");
                match narrow_command(
                    lm,
                    interner,
                    &subject,
                    arrow,
                    &goal,
                    max_depth,
                    fold,
                    vfold,
                    path,
                    filter,
                    delay,
                ) {
                    Err(error) => out.push_str(&format!("error: {error}\n")),
                    Ok(command) => {
                        if verbose {
                            append_verbose_identity_collapse_diagnostics(
                                lm,
                                &cur,
                                reported_identity_collapses,
                                out,
                            );
                        }
                        out.push_str(&format!(
                            "{prefix}{keyword}{stream_options}{bound_str} in {cur} : {} \
                             {arrow_echo} {} .\n",
                            command.subject_echo, command.goal_echo
                        ));
                        let mut session = NarrowSession {
                            search: command.search,
                            variables: command.variables,
                            initial_variable_count: command.initial_variable_count,
                            initial_variables: command.initial_variables,
                            initial_echoes: command.initial_echoes,
                            next_number: 0,
                            path,
                        };
                        let body = render_narrowing(
                            &mut session,
                            lm,
                            interner,
                            self.color,
                            self.show_timing,
                            self.show_breakdown,
                            verbose,
                            path,
                            max_solutions,
                        );
                        out.push_str(&body);
                        self.last = Some((cur.clone(), Continuation::Narrow(Box::new(session))));
                    }
                }
            }
            Command::ShowNarrowing { display, state } => {
                let Some((module, Continuation::Narrow(session))) = &mut self.last else {
                    out.push_str("error: no narrowing state graph is available.\n");
                    return;
                };
                if *module != cur {
                    out.push_str("error: the narrowing state graph belongs to another module.\n");
                    return;
                }
                let lm = self.modules.get_mut(&cur).expect("current module is built");
                let body = render_narrowing_display(
                    session,
                    lm,
                    &self.interner,
                    self.color,
                    display,
                    state.map(|number| number as usize),
                );
                out.push_str(&body);
                out.push('\n');
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
                Some((m, Continuation::SmtSearch(mut session))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    lm.built.engine.reset_rewrites();
                    let body = render_smt_search(
                        &mut session,
                        lm,
                        &self.interner,
                        self.color,
                        self.show_timing,
                        bound,
                    );
                    out.push_str(&body);
                    self.last = Some((m, Continuation::SmtSearch(session)));
                }
                Some((m, Continuation::Variants(mut session))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    lm.built.engine.reset_rewrites();
                    let body =
                        render_variants(&mut session, lm, &mut self.interner, self.color, bound);
                    out.push_str(&body);
                    self.last = Some((m, Continuation::Variants(session)));
                }
                Some((m, Continuation::VariantUnifiers(mut session))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    lm.built.engine.reset_rewrites();
                    let body =
                        render_variant_unifiers(&mut session, lm, &mut self.interner, bound);
                    out.push_str(&body);
                    self.last = Some((m, Continuation::VariantUnifiers(session)));
                }
                Some((m, Continuation::Narrow(mut session))) if m == cur => {
                    let lm = self.modules.get_mut(&cur).expect("current module is built");
                    lm.built.engine.reset_rewrites();
                    let show_state_number = session.path;
                    let body = render_narrowing(
                        &mut session,
                        lm,
                        &mut self.interner,
                        self.color,
                        self.show_timing,
                        self.show_breakdown,
                        self.verbose,
                        show_state_number,
                        bound,
                    );
                    out.push_str(&body);
                    self.last = Some((m, Continuation::Narrow(session)));
                }
                _ => out.push_str(
                    "No previous rewriting, search, or variant enumeration to continue in this module.\n",
                ),
            },
        }
    }

    /// `select <NAME> .` — make `NAME` the current module.
    fn meta_select(&mut self, line: &str) -> Eval {
        let name = line
            .split_whitespace()
            .nth(1)
            .map(|s| s.trim_end_matches('.'))
            .unwrap_or("");
        let out = if name.is_empty() {
            "select: expected a module name.".to_string()
        } else if self.modules.contains_key(name) {
            if self.current.as_deref() != Some(name) {
                self.meta_state.clear();
            }
            self.current = Some(name.to_string());
            self.last = None; // switching modules invalidates the saved rewrite continuation
            String::new()
        } else {
            format!("select: no module `{name}` — enter it first.")
        };
        Eval {
            output: out,
            exit: false,
        }
    }

    /// `show modules` (the entered names) or `show module [NAME]` (a module's sorts + ops).
    fn meta_show(&mut self, line: &str) -> Eval {
        let words: Vec<&str> = line
            .split_whitespace()
            .map(|s| s.trim_end_matches('.'))
            .filter(|s| !s.is_empty())
            .collect();
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
            // `show path [states] N .` — regular-search or narrowing history.
            Some("path") => {
                let path_states = words.get(2).copied() == Some("states");
                let number_slot = if path_states { 3 } else { 2 };
                let n: Option<usize> = words.get(number_slot).and_then(|s| s.parse().ok());
                match (n, self.current.as_deref()) {
                    (Some(n), Some(cur)) => match &self.last {
                        Some((m, Continuation::Search(session))) if m == cur && !path_states => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_path(&session.search, lm, &self.interner, n, self.color)
                        }
                        Some((m, Continuation::Narrow(session))) if m == cur => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_narrowing_display(
                                session,
                                lm,
                                &self.interner,
                                self.color,
                                if path_states {
                                    NarrowDisplay::PathStates
                                } else {
                                    NarrowDisplay::Path
                                },
                                Some(n),
                            )
                        }
                        _ => "show path: no current search (run `search` first).".into(),
                    },
                    (None, _) => "show path: expected a state number.".into(),
                    _ => "show path: no current module.".into(),
                }
            }
            Some("frontier") if words.get(2).copied() == Some("states") => {
                match self.current.as_deref() {
                    Some(cur) => match &self.last {
                        Some((m, Continuation::Narrow(session))) if m == cur => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_narrowing_display(
                                session,
                                lm,
                                &self.interner,
                                self.color,
                                NarrowDisplay::Frontier,
                                None,
                            )
                        }
                        _ => "Warning: no narrowing state forest.".into(),
                    },
                    None => "show frontier states: no current module.".into(),
                }
            }
            Some("most")
                if words.get(2).copied() == Some("general")
                    && words.get(3).copied() == Some("states") =>
            {
                match self.current.as_deref() {
                    Some(cur) => match &self.last {
                        Some((m, Continuation::Narrow(session))) if m == cur => {
                            let lm = self.modules.get(cur).expect("current module is built");
                            render_narrowing_display(
                                session,
                                lm,
                                &self.interner,
                                self.color,
                                NarrowDisplay::MostGeneral,
                                None,
                            )
                        }
                        _ => "Warning: no narrowing state forest.".into(),
                    },
                    None => "show most general states: no current module.".into(),
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
        Eval {
            output: out,
            exit: false,
        }
    }

    /// `set trace [<option>] on|off` — the full `trace` flag surface (master + body / substitution /
    /// rewrite / whole / condition / eqs / mbs / builtin). Other `set` options are a follow-up.
    fn meta_set(&mut self, line: &str) -> Eval {
        let words: Vec<&str> = line
            .split_whitespace()
            .map(|s| s.trim_end_matches('.'))
            .filter(|s| !s.is_empty())
            .collect();
        let out = match words.get(1).copied() {
            Some("trace") => self.trace.apply(&words[2..]).err().unwrap_or_default(),
            // `set include BOOL on|off` (D11): toggle the implicit-BOOL auto-import. Other
            // `set include <MOD>` names remain silent no-ops (nothing else is auto-imported).
            Some("include") if words.get(2).copied() == Some("BOOL") => {
                match words.get(3).copied() {
                    Some("on") => self.include_bool = true,
                    Some("off") => self.include_bool = false,
                    _ => {}
                }
                String::new()
            }
            // `set show timing on|off`: gates the `Decision time:` line of match/xmatch/unify.
            Some("show") if words.get(2).copied() == Some("timing") => {
                match words.get(3).copied() {
                    Some("on") => self.show_timing = true,
                    Some("off") => self.show_timing = false,
                    _ => {}
                }
                String::new()
            }
            Some("show") if words.get(2).copied() == Some("breakdown") => {
                match words.get(3).copied() {
                    Some("on") => self.show_breakdown = true,
                    Some("off") => self.show_breakdown = false,
                    _ => {}
                }
                String::new()
            }
            Some("verbose") => {
                match words.get(2).copied() {
                    Some("on") => self.verbose = true,
                    Some("off") => self.verbose = false,
                    _ => {}
                }
                String::new()
            }
            // Every other interpreter directive (`set show advisories off`, `set include … on/off`,
            // `set oo include … on`, …) is a silent no-op, as the file-loading parser already treats
            // `set` (we never auto-import, and these toggles do not affect our output). Silence matches
            // Maude — it applies these without echoing — so loaded `.maude` files stay byte-comparable.
            _ => String::new(),
        };
        Eval {
            output: out,
            exit: false,
        }
    }

    /// `load <file>` / `sload <file>` (D11): read the file and evaluate its contents in place
    /// (modules + commands), resolving relative to the CWD then `$MAUDE_LIB` (colon-separated),
    /// with and without an appended `.maude`. `sload` skips a file that was already loaded.
    fn meta_load(&mut self, sload: bool, path: &str) -> Eval {
        if path.is_empty() {
            return Eval {
                output: "error: load needs a file name".into(),
                exit: false,
            };
        }
        let mut candidates: Vec<std::path::PathBuf> = Vec::new();
        for base in [path.to_string(), format!("{path}.maude")] {
            candidates.push(std::path::PathBuf::from(&base));
            if let Ok(lib) = std::env::var("MAUDE_LIB") {
                for dir in lib.split(':').filter(|d| !d.is_empty()) {
                    candidates.push(std::path::Path::new(dir).join(&base));
                }
            }
        }
        let Some(found) = candidates.iter().find(|p| p.is_file()) else {
            return Eval {
                output: format!("error: cannot open file `{path}`"),
                exit: false,
            };
        };
        let canonical = std::fs::canonicalize(found).unwrap_or_else(|_| found.clone());
        if sload && self.loaded_files.contains(&canonical) {
            return Eval::default(); // already loaded: sload is a silent skip
        }
        let src = match std::fs::read_to_string(found) {
            Ok(s) => s,
            Err(e) => {
                return Eval {
                    output: format!("error: cannot read `{path}`: {e}"),
                    exit: false,
                };
            }
        };
        self.loaded_files.insert(canonical);
        self.eval_dispatch(&src)
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
        // `load`/`sload` are line-terminated (no `.`): a submission whose first TOKEN is the
        // keyword (leading comments stripped by the lexer) is complete at its line end — both
        // drivers append whole lines, so the buffer already ends at one.
        {
            let toks = tokenize(input, &mut self.interner);
            if let Some(t) = toks.first()
                && matches!(self.interner.resolve(t.sym), "load" | "sload")
            {
                return true;
            }
        }
        let toks = tokenize(input, &mut self.interner);
        let Some(last) = toks.last().copied() else {
            return false;
        };
        // Track module nesting, but only count a module keyword (`fmod`/`endfm`/…) when it is a real
        // delimiter: at bracket depth 0 and in statement-leading position. The meta-level's
        // module-constructor operators put `fmod`/`is`/`sorts`/`endfm` *inside* a term
        // (`getName(fmod Q is … endfm) = Q`), where they are operator-name fragments, not delimiters —
        // counting those would close the module early and submit it without its `endfm`.
        let is_close = |s: &str| {
            matches!(
                s,
                "endfm"
                    | "endm"
                    | "endfth"
                    | "endth"
                    | "endv"
                    | "endsm"
                    | "endsth"
                    | "endom"
                    | "endoth"
            )
        };
        // A command keyword *claims* the statement it leads (`red …`, `search …`): a module-open keyword
        // inside a command's term (`red fmod … endfm .`, `reduce metaReduce(…)`) is then an operator-name
        // fragment, not a real module. Junk tokens do NOT claim the statement, so a module preceded by
        // top-level junk (`junkalpha … fmod MC …`, fable-audit.md §3.4) is still recognized — the buffer
        // must not complete mid-module at the module's first inner `.`.
        let is_command = |s: &str| {
            matches!(
                s,
                "reduce"
                    | "red"
                    | "rewrite"
                    | "rew"
                    | "frewrite"
                    | "frew"
                    | "erewrite"
                    | "erew"
                    | "search"
                    | "smt-search"
                    | "match"
                    | "xmatch"
                    | "continue"
                    | "cont"
                    | "srewrite"
                    | "srew"
                    | "dsrewrite"
                    | "dsrew"
                    | "unify"
                    | "irredundant"
                    | "irred"
            )
        };
        let mut open = false;
        let mut saw_open = false;
        let mut depth = 0i32;
        let mut leading = true; // start, just after a depth-0 `.`, or just after a module delimiter
        let mut claimed = false; // the current statement is a command (its body is a term, not a module)
        for t in &toks {
            let txt = self.interner.resolve(t.sym);
            // A command keyword at statement-leading position claims the statement (its module keywords are
            // term fragments). A module-open keyword at depth 0 opens a module unless the statement is a
            // command — the leading requirement is dropped so top-level junk before it stays transparent.
            if depth == 0 && leading && is_command(txt) {
                claimed = true;
            }
            if depth == 0
                && !claimed
                && matches!(
                    txt,
                    "fmod" | "mod" | "fth" | "th" | "smod" | "sth" | "omod" | "oth" | "view"
                )
            {
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
            let boundary = (t.kind == TokKind::Dot && depth == 0) || is_close(txt);
            leading = boundary;
            if boundary {
                claimed = false; // a new statement begins after a depth-0 `.` / module close
            }
        }
        let last_txt = self.interner.resolve(last.sym);
        let module_closed = is_close(last_txt) && saw_open && !open && depth == 0;
        module_closed || (last.kind == TokKind::Dot && depth == 0 && !open)
    }
}

/// Maude defers binary-symbol sort checks until a symbolic command first needs them. Under
/// `set verbose on`, an identity whose collapse lowers the result sort therefore reports once,
/// immediately before that command's echo.
fn append_verbose_identity_collapse_diagnostics(
    lm: &LoadedModule,
    module: &str,
    reported: &mut HashSet<(String, tnk_core::symbol::SymbolId)>,
    out: &mut String,
) {
    let mut symbols: Vec<_> = lm.built.ops.values().copied().collect();
    symbols.sort_unstable();
    symbols.dedup();
    for symbol in symbols {
        let Some((result, collapsed)) =
            tnk_core::unify::unequal_left_identity_collapse(&lm.built.engine, symbol)
        else {
            continue;
        };
        if !reported.insert((module.to_string(), symbol)) {
            continue;
        }
        out.push_str(&format!(
            "op {} left-identity collapse from {} to {} is unequal.\n",
            lm.built.engine.symbol(symbol).name(),
            lm.built.engine.sorts().name(result),
            lm.built.engine.sorts().name(collapsed),
        ));
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
    format!(
        "{trace}rewrites: {rw_count} in 0ms cpu (0ms real) (~ rewrites/second)\n{result_line}\n"
    )
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

/// Pull object-level SMT-search results. SMT-sorted goal variables are represented by equalities in
/// the final `where` constraint; only non-SMT goal variables appear as substitution lines.
fn render_smt_search(
    session: &mut SmtSearchSession,
    lm: &mut LoadedModule,
    i: &Interner,
    color: bool,
    show_timing: bool,
    limit: Option<u64>,
) -> String {
    let mut out = String::new();
    let mut shown = 0u64;
    loop {
        if limit == Some(shown) {
            return out;
        }
        let Some(solution) = session.search.next_solution(&mut lm.built.engine) else {
            let message = if session.shown_total == 0 {
                "No solution."
            } else {
                "No more solutions."
            };
            out.push_str(&format!(
                "\n{message}\n{}\n",
                narrowing_rewrite_line(lm.built.engine.rewrites(), show_timing)
            ));
            return out;
        };
        shown += 1;
        session.shown_total += 1;
        let names = session.search.variable_names();
        let state = session
            .search
            .state_term(solution.state)
            .expect("SMT solution references a live state");
        let state = print_pretty_with_variables(&lm.built, i, state, names, color);
        let constraint =
            print_pretty_with_variables(&lm.built, i, solution.constraint, names, color);
        out.push_str(&format!(
            "\nSolution {}\n{}\nstate: {state}\n",
            solution.number,
            narrowing_rewrite_line(solution.rewrites, show_timing)
        ));
        let mut rendered_binding = false;
        for slot in 0..session.target_variable_count {
            if lm
                .built
                .engine
                .smt_type(session.goal_variables.sort(slot))
                .is_some()
            {
                continue;
            }
            rendered_binding = true;
            let value = print_pretty_with_variables(
                &lm.built,
                i,
                solution.bindings[slot as usize],
                names,
                color,
            );
            out.push_str(&format!(
                "{} --> {value}\n",
                session.goal_variables.name(slot)
            ));
        }
        if !rendered_binding {
            out.push_str("empty substitution\n");
        }
        out.push_str(&format!("where {constraint}\n"));
    }
}

/// Pull up to `limit` variants from one resumable folding search. Incremental mode reports the rewrite
/// snapshot for each layer; irredundant mode computes the survivor set first and reports one total.
fn render_variants(
    session: &mut VariantSession,
    lm: &mut LoadedModule,
    i: &mut Interner,
    color: bool,
    limit: Option<u64>,
) -> String {
    let mut out = String::new();
    let mut shown = 0u64;
    loop {
        if limit == Some(shown) {
            return out;
        }
        let next = {
            let mut names = InternerNames(i);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut lm.built.engine,
                names: &mut names,
            };
            session.search.find_next(&mut env)
        };
        if session.irredundant && !session.reported_total {
            let rewrites = lm.built.engine.rewrites();
            out.push_str(&format!(
                "rewrites: {rewrites} in 0ms cpu (0ms real) (~ rewrites/second)\n"
            ));
            session.reported_total = true;
        }
        match next {
            Some(variant) => {
                shown += 1;
                let eng = &lm.built.engine;
                let sort = eng.sorts().name(eng.sort_of(variant.term));
                let value = print_pretty(&lm.built, i, variant.term, color);
                out.push_str(&format!("\nVariant {}\n", variant.index + 1));
                if !session.irredundant {
                    out.push_str(&format!(
                        "rewrites: {} in 0ms cpu (0ms real) (~ rewrites/second)\n",
                        variant.rewrites
                    ));
                }
                out.push_str(&format!("{sort}: {value}\n"));
                for (slot, &binding) in variant.substitution.iter().enumerate() {
                    let value = print_pretty(&lm.built, i, binding, color);
                    out.push_str(&format!("{} --> {value}\n", session.var_names[slot]));
                }
            }
            None => {
                out.push_str("\nNo more variants.\n");
                if !session.irredundant {
                    let rewrites = lm.built.engine.rewrites();
                    out.push_str(&format!(
                        "rewrites: {rewrites} in 0ms cpu (0ms real) (~ rewrites/second)\n"
                    ));
                }
                return out;
            }
        }
    }
}

impl VariantUnifySession {
    fn advance(&mut self, lm: &mut LoadedModule, i: &mut Interner) {
        if self.exhausted {
            return;
        }
        let mut names = InternerNames(i);
        let mut env = tnk_core::unify::UnifyEnv {
            e: &mut lm.built.engine,
            names: &mut names,
        };
        if self.matching {
            let subject = self.subject.expect("variant matching subject");
            while let Some(variant) = self.search.find_next(&mut env) {
                let matches = tnk_core::variant::variant_match_bindings(
                    &mut env,
                    &variant,
                    subject,
                    &self.fresh_base,
                );
                if matches.is_empty() {
                    continue;
                }
                let rewrites = env.e.rewrites();
                for bindings in matches {
                    let equations = self.search.variant_equations();
                    self.stream
                        .insert(&mut env, bindings, variant.family, rewrites, &equations);
                }
                return;
            }
            self.exhausted = true;
            return;
        }
        let Some(variant) = self.search.find_next(&mut env) else {
            self.exhausted = true;
            return;
        };
        debug_assert!(variant.unifier);
        let rewrites = env.e.rewrites();
        let equations = self.search.variant_equations();
        self.stream.insert(
            &mut env,
            variant.substitution,
            variant.family,
            rewrites,
            &equations,
        );
    }

    fn prepare_filtered(&mut self, lm: &mut LoadedModule, i: &mut Interner) {
        if self.prepared {
            return;
        }
        while !self.exhausted {
            self.advance(lm, i);
        }
        self.stream.finish();
        self.prepared = true;
    }
}

fn render_variant_unifiers(
    session: &mut VariantUnifySession,
    lm: &mut LoadedModule,
    i: &mut Interner,
    limit: Option<u64>,
) -> String {
    let mut out = String::new();
    if session.upfront {
        session.prepare_filtered(lm, i);
        if !session.reported_total {
            out.push_str(&format!(
                "rewrites: {} in 0ms cpu (0ms real) (~ rewrites/second)\n",
                lm.built.engine.rewrites()
            ));
            session.reported_total = true;
        }
    }
    let mut shown = 0;
    loop {
        if limit == Some(shown) {
            return out;
        }
        let index = loop {
            if let Some(index) = session.stream.pop_pending() {
                break Some(index);
            }
            if session.exhausted {
                break None;
            }
            session.advance(lm, i);
        };
        let Some(index) = index else {
            let noun = if session.matching {
                "matchers"
            } else {
                "unifiers"
            };
            let message = if session.next_number == 0 {
                format!("No {noun}.")
            } else {
                format!("No more {noun}.")
            };
            out.push_str(&format!("\n{message}\n"));
            if !session.upfront {
                out.push_str(&format!(
                    "rewrites: {} in 0ms cpu (0ms real) (~ rewrites/second)\n",
                    lm.built.engine.rewrites()
                ));
            }
            return out;
        };
        shown += 1;
        session.next_number += 1;
        let result_rewrites = session.stream.rewrites(index);
        let label = if session.matching {
            "Matcher"
        } else {
            "Unifier"
        };
        out.push_str(&format!("\n{label} {}\n", session.next_number));
        if !session.upfront {
            out.push_str(&format!(
                "rewrites: {} in 0ms cpu (0ms real) (~ rewrites/second)\n",
                result_rewrites
            ));
        }
        let bindings = if session.matching {
            session
                .stream
                .bindings(index)
                .iter()
                .map(|&dag| {
                    tnk_core::variant::restore_subject_variables(
                        &mut lm.built.engine,
                        dag,
                        &session.restorations,
                    )
                })
                .collect::<Vec<_>>()
        } else {
            session.stream.bindings(index).to_vec()
        };
        out.push_str(&render_unifier(&lm.built, i, &session.var_names, &bindings));
        out.push('\n');
    }
}

/// `Var --> value` lines for a search solution. The variable is rendered by its written name (Maude
/// echoes a goal variable as written: a declared `X` prints `X`, an on-the-fly `X:Sort` prints
fn narrowing_rewrite_line(rewrites: u64, show_timing: bool) -> String {
    if show_timing {
        format!("rewrites: {rewrites} in 0ms cpu (0ms real) (~ rewrites/second)")
    } else {
        format!("rewrites: {rewrites}")
    }
}

fn render_narrow_accumulated(
    session: &NarrowSession,
    lm: &LoadedModule,
    i: &Interner,
    state: usize,
    color: bool,
) -> String {
    let (_, substitution, _, _) = session.search.state(state);
    let (variables, count) = if let Some(initials) = &session.initial_variables {
        let variables = &initials[session.search.root_index(state)];
        (variables, variables.count() as usize)
    } else {
        (&session.variables, session.initial_variable_count)
    };
    (0..count)
        .map(|slot| {
            let value = print_pretty(&lm.built, i, substitution[slot], color);
            let name = command_variable_display_name(
                &lm.grammar,
                i,
                variables.name(slot as u32),
                variables.sort(slot as u32),
            );
            format!("{name} --> {value}")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn render_narrow_variant_unifier(
    lm: &LoadedModule,
    i: &Interner,
    variables: &[tnk_core::unify::problem::VarSpec],
    bindings: &[DagId],
    color: bool,
    source_variables: Option<(&VarIndex, usize)>,
) -> String {
    variables
        .iter()
        .zip(bindings)
        .map(|(variable, &binding)| {
            let source_name = source_variables.and_then(|(variables, first_goal)| {
                (first_goal..variables.count() as usize).find_map(|slot| {
                    let source = variables.name(slot as u32);
                    let base = source.split_once(':').map_or(source, |(name, _)| name);
                    let code = i.get(base)?.index();
                    (variable.name == maude_variable_name_rank(base, code)
                        && variable.sort == variables.sort(slot as u32))
                    .then(|| {
                        command_variable_display_name(
                            &lm.grammar,
                            i,
                            source,
                            variables.sort(slot as u32),
                        )
                    })
                })
            });
            let name = source_name.unwrap_or_else(|| {
                let base = i.resolve(tnk_frontend::lex::Sym::from_raw(variable.name));
                if matches!(base.as_bytes().first(), Some(b'#' | b'%' | b'@')) {
                    format!("{base}:{}", lm.built.engine.sorts().name(variable.sort))
                } else {
                    base.to_string()
                }
            });
            let value = print_pretty(&lm.built, i, binding, color);
            format!("{name} --> {value}")
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn narrowing_breakdown(lm: &LoadedModule, enabled: bool) -> String {
    if !enabled {
        return String::new();
    }
    let total = lm.built.engine.rewrites();
    let (variant, narrowing) = lm.built.engine.narrowing_breakdown();
    let equational = total.saturating_sub(variant + narrowing);
    format!(
        "\nmb applications: 0  equational rewrites: {equational}  rule rewrites: 0  \
         variant narrowing steps: {variant}  narrowing steps: {narrowing}"
    )
}

fn render_narrow_folding_events(
    session: &mut NarrowSession,
    lm: &LoadedModule,
    i: &Interner,
    color: bool,
) -> String {
    let mut out = String::new();
    for event in session.search.take_folding_events() {
        match event {
            tnk_core::narrow::FoldingEvent::Subsumed { state, by, .. } => {
                let candidate = print_pretty(&lm.built, i, session.search.state(state).0, color);
                let retained = print_pretty(&lm.built, i, session.search.state(by).0, color);
                out.push_str(&format!("New state {candidate} subsumed by {retained}\n"));
            }
            tnk_core::narrow::FoldingEvent::Evicted { state, by } => {
                let candidate = print_pretty(&lm.built, i, session.search.state(by).0, color);
                let victim = print_pretty(&lm.built, i, session.search.state(state).0, color);
                out.push_str(&format!(
                    "New state {candidate} subsumed older state {victim}\n"
                ));
            }
        }
    }
    out
}

fn render_narrowing(
    session: &mut NarrowSession,
    lm: &mut LoadedModule,
    i: &mut Interner,
    color: bool,
    show_timing: bool,
    show_breakdown: bool,
    verbose: bool,
    show_state_number: bool,
    limit: Option<u64>,
) -> String {
    let mut out = String::new();
    let mut shown = 0;
    loop {
        if limit == Some(shown) {
            return out;
        }
        let solution = {
            let mut names = InternerNames(i);
            let mut env = tnk_core::unify::UnifyEnv {
                e: &mut lm.built.engine,
                names: &mut names,
            };
            session.search.find_next(&mut env)
        };
        if verbose {
            out.push_str(&render_narrow_folding_events(session, lm, i, color));
        }
        let Some(solution) = solution else {
            if verbose {
                out.push_str(&format!(
                    "Total number of states seen = {}\n\
                     Of which {} were considered for further narrowing.\n",
                    session.search.state_count(),
                    session.search.states_expanded(),
                ));
            }
            let message = if session.next_number == 0 {
                "No solution."
            } else {
                "No more solutions."
            };
            out.push_str(&format!(
                "\n{message}\n{}{}\n",
                narrowing_rewrite_line(lm.built.engine.rewrites(), show_timing),
                narrowing_breakdown(lm, show_breakdown),
            ));
            return out;
        };
        shown += 1;
        session.next_number += 1;
        let (term, _, _, _) = session.search.state(solution.state);
        let state = print_pretty(&lm.built, i, term, color);
        let state_number = if show_state_number {
            format!(" (state {})", solution.state)
        } else {
            String::new()
        };
        let initial_state = session
            .initial_variables
            .as_ref()
            .map_or_else(String::new, |_| {
                format!(
                    "\ninitial state: {}",
                    session.initial_echoes[session.search.root_index(solution.state)]
                )
            });
        let accumulated = render_narrow_accumulated(session, lm, i, solution.state, color);
        let accumulated_newline = if accumulated.is_empty() { "" } else { "\n" };
        let unifier = render_narrow_variant_unifier(
            lm,
            i,
            &solution.variables,
            &solution.bindings,
            color,
            Some((&session.variables, session.initial_variable_count)),
        );
        let unifier_newline = if unifier.is_empty() { "" } else { "\n" };
        out.push_str(&format!(
            "\nSolution {}{state_number}\n{}{}\nstate: {state}{initial_state}\n\
             accumulated substitution:\n{accumulated}{accumulated_newline}variant unifier:\n{unifier}{unifier_newline}",
            session.next_number,
            narrowing_rewrite_line(lm.built.engine.rewrites(), show_timing),
            narrowing_breakdown(lm, show_breakdown),
        ));
    }
}

fn render_narrow_state(
    session: &NarrowSession,
    lm: &LoadedModule,
    i: &Interner,
    state: usize,
    color: bool,
) -> String {
    let (term, _, _, _) = session.search.state(state);
    let sort = lm.built.engine.sorts().name(lm.built.engine.sort_of(term));
    let value = print_pretty(&lm.built, i, term, color);
    let accumulated = render_narrow_accumulated(session, lm, i, state, color);
    format!("state {state}, {sort}: {value}\naccumulated substitution:\n{accumulated}")
}

fn render_narrowing_display(
    session: &NarrowSession,
    lm: &LoadedModule,
    i: &Interner,
    color: bool,
    display: NarrowDisplay,
    requested: Option<usize>,
) -> String {
    match display {
        NarrowDisplay::MostGeneral | NarrowDisplay::Frontier => {
            let states: Vec<_> = if matches!(display, NarrowDisplay::MostGeneral) {
                session.search.alive_states().collect()
            } else {
                session.search.frontier_states().collect()
            };
            if states.is_empty() {
                return if matches!(display, NarrowDisplay::Frontier) {
                    "*** frontier is empty ***".to_string()
                } else {
                    "*** there are no most general states ***".to_string()
                };
            }
            states
                .iter()
                .map(|&state| {
                    let (term, _, _, _) = session.search.state(state);
                    print_pretty(&lm.built, i, term, color)
                })
                .collect::<Vec<_>>()
                .join(" \\/\n")
        }
        NarrowDisplay::Path | NarrowDisplay::PathStates => {
            let state = requested.expect("show path carries a state");
            let path = session.search.path_indices(state);
            if path.is_empty() {
                return format!("show path: no state {state}.");
            }
            let mut out = String::new();
            for (position, &index) in path.iter().enumerate() {
                if position > 0 {
                    let step = session.search.step(index).expect("non-root path state");
                    let rule = &lm.built.engine.narrowing_rules()[step.rule_index];
                    if matches!(display, NarrowDisplay::PathStates) {
                        out.push_str(&format!(
                            "--- {} --->\n",
                            rule.label.as_deref().unwrap_or("unlabeled")
                        ));
                    } else {
                        out.push_str(&format!(
                            "===[ {} ]===>\nvariant unifier:\n",
                            trace::rule_body(&lm.built, i, step.rule_id, color)
                        ));
                        for (name, &binding) in
                            rule.variable_names.iter().zip(&step.source_substitution)
                        {
                            let value = print_pretty(&lm.built, i, binding, color);
                            out.push_str(&format!("{name} --> {value}\n"));
                        }
                        let parent = session.search.parent(index).expect("path child has parent");
                        let variables = session.search.state_variables(parent);
                        let rendered = render_narrow_variant_unifier(
                            lm,
                            i,
                            variables,
                            &step.state_unifier,
                            color,
                            None,
                        );
                        if !rendered.is_empty() {
                            out.push_str(&rendered);
                            out.push('\n');
                        }
                    }
                }
                out.push_str(&render_narrow_state(session, lm, i, index, color));
                if position + 1 != path.len() {
                    out.push('\n');
                }
            }
            out
        }
    }
}

/// `X:Sort` — the colon form is part of the variable name once on-the-fly variables are supported).
fn render_search_bindings(
    lm: &LoadedModule,
    i: &Interner,
    vars: &VarIndex,
    bindings: &[DagId],
    color: bool,
) -> String {
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
            let rb = step
                .via
                .map(|r| trace::rule_body(&lm.built, i, r, color))
                .unwrap_or_default();
            out.push_str(&format!("===[ {rb} ]===>\n"));
        }
        let sort = lm
            .built
            .engine
            .sorts()
            .name(lm.built.engine.sort_of(step.term));
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
        // One arc per distinct successor state; all rules reaching it are listed on that single arc, each
        // in its own parens (Maude merges arcs by target — fable-audit.md §3.3 B5).
        for (arc_n, (target, rules)) in arcs.iter().enumerate() {
            let bodies: String = rules
                .iter()
                .map(|rid| format!(" ({})", trace::rule_body(&lm.built, i, *rid, color)))
                .collect();
            out.push_str(&format!("arc {arc_n} ===> state {target}{bodies}\n"));
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
                s.push_str(&format!(
                    "  op {} to {} .\n",
                    join_tokens(from, i),
                    join_tokens(to, i)
                ));
            }
            OpMap::Term { from, to } => {
                s.push_str(&format!(
                    "  op {} to term {} .\n",
                    join_tokens(from, i),
                    join_tokens(to, i)
                ));
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
    format!(
        "fmod {name}\n  sorts: {}\n  ops: {}",
        sorts.join(" "),
        ops.join(" ")
    )
}

#[cfg(test)]
mod tests;
