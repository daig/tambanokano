//! Loading: drive a whole `.maude` source end-to-end. Surface-parse it, then for each module build the
//! signature ([`build_module`]), the mixfix grammar ([`build_grammar`]), and add its parsed statements;
//! commands are run against the module they follow (Maude's current module). The B4.4c entry point and
//! the basis for the B5 REPL.
//!
//! Scope: unconditional and conditional `eq`/`mb` (`ceq`/`cmb`/condition fragments/`owise`, B4.5c) and
//! the `reduce` (B4.4c) and `match`/`xmatch` (B4.5d, via [`match_command`]) commands. The `match`
//! command drives the kernel's public multi-solution stream (`Engine::match_solutions`). Still open in
//! B4.5: `__` juxtaposition (B4.5e, blocks `au`) and the whole-prelude differential test.

use crate::build_term::{build_dag, build_term, VarIndex};
use crate::cfparser::compile::CompiledGrammar;
use crate::cfparser::forest::PTree;
use crate::cfparser::{earley, forest};
use crate::grammar::build::build_grammar;
use crate::grammar::{Action, Nt, NtType};
use crate::lex::{tokenize, Interner, Token};
use crate::oo_complete;
use crate::pretty::{print_pretty, print_term};
use crate::sig::build_sig::build_module;
use crate::sig::syntax::{BuiltModule, EqTrace, MbTrace, RlTrace};
use crate::surface::ast::{Command, PreModule, SearchArrow, Source, Statement};
use crate::surface::parser::Parser;
use std::collections::{BTreeSet, HashMap};
use tnk_core::dag::DagId;
use tnk_core::engine::MatchedPortion;
use tnk_core::rewrite::Rewriting;
use tnk_core::search::{Arrow, Search};
use tnk_core::sort::{KindId, SortId};
use tnk_core::symbol::SymbolId;
use tnk_core::term::{ConditionFragment, Equation, Membership, Term};

/// A fully loaded module: its kernel state (signature + statements) and its mixfix grammar (for parsing
/// command/REPL terms).
pub struct LoadedModule {
    pub built: BuiltModule,
    pub grammar: CompiledGrammar,
}

/// A loaded source: the shared interner, the modules (file order), and the commands tagged with the
/// module-index they run against.
pub struct Loaded {
    pub interner: Interner,
    pub modules: Vec<LoadedModule>,
    pub commands: Vec<(usize, Command)>,
}

/// Build one `PreModule` into a runnable [`LoadedModule`]: signature ([`build_module`]) + mixfix grammar
/// ([`build_grammar`]) + its statements ([`load_statements`]). The module system (`tnk-modules`) calls
/// this on a *flattened* `PreModule` (the import closure merged into one), so imports need no kernel
/// change — flattening is a pure `PreModule → PreModule` transform upstream of here.
pub fn build_loaded_module(pm: &PreModule, interner: &mut Interner) -> Result<LoadedModule, String> {
    let mut built = build_module(pm, interner)?;
    let grammar = CompiledGrammar::compile(&build_grammar(&built, interner));
    load_statements(pm, &mut built, &grammar, interner)?;
    Ok(LoadedModule { built, grammar })
}

/// Build a flattened `PreModule` into a [`LoadedModule`] with the **D1a import-reparse point-fix**: each
/// statement whose flattened-grammar parse is ambiguous is re-parsed against its home module's own grammar
/// (see [`load_statements_homed`]). `homes` (parallel to `pm.statements`, from
/// `tnk_modules::flatten::flatten_with_homes`) tags each statement's origin module; `home_mod` resolves a
/// home name to an already-built [`LoadedModule`] (the loader's / REPL's module cache). Signature-identical
/// to [`build_loaded_module`] up to those two extra inputs; the module system routes flattened modules here.
pub fn build_loaded_module_homed<'m>(
    pm: &PreModule,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    interner: &mut Interner,
) -> Result<LoadedModule, String> {
    let mut built = build_module(pm, interner)?;
    let grammar = CompiledGrammar::compile(&build_grammar(&built, interner));
    load_statements_homed(pm, &mut built, &grammar, homes, home_mod, interner)?;
    Ok(LoadedModule { built, grammar })
}

/// Produce a copy of `home`'s compiled grammar whose semantic **actions** resolve symbols and sorts in
/// `flat`'s tables instead of `home`'s — so a bubble parsed against the home module's (unambiguous) grammar
/// builds a kernel term over the *flattened* module's symbols (the D1a point-fix seam). The grammar's
/// structure (nonterminals/terminals/precedence) is `home`'s, so it disambiguates exactly as the home
/// module does; only the resolved [`SymbolId`]/[`SortId`] each action carries is re-pointed.
///
/// Matching is by intrinsic identity: an operator by `(name, domain kinds, range kind)` — the same key
/// `build_module` uses, and invariant across a symbol's subsort-overloaded declarations — with kinds
/// translated home→flat through any shared declared sort name; a sort by name (an error/kind sort by its
/// kind). Because a plain import copies every home sort/operator into the flattened module under the same
/// name and profile, every action resolves. Returns `None` if any action references a home symbol/sort with
/// no flattened counterpart (e.g. a renamed donation reached here) — the caller then keeps the flattened
/// grammar, i.e. the pre-fix behavior; never a *wrong* symbol.
pub fn remap_home_grammar(home: &LoadedModule, flat: &BuiltModule) -> Option<CompiledGrammar> {
    let hsorts = home.built.engine.sorts();
    let fsorts = flat.engine.sorts();
    // home kind → flat kind, via any declared sort the two modules share by name (a plain import copies
    // home's sorts verbatim, so every home kind has such a witness).
    let mut kind_map: HashMap<KindId, KindId> = HashMap::new();
    for (name, &hsort) in &home.built.sorts {
        if let Some(&fsort) = flat.sorts.get(name) {
            kind_map.entry(hsorts.kind_of(hsort)).or_insert_with(|| fsorts.kind_of(fsort));
        }
    }
    // flat operator table keyed by intrinsic identity (name, domain kinds, range kind).
    let mut flat_by_profile: HashMap<(&str, Vec<KindId>, KindId), SymbolId> = HashMap::new();
    for (&fsym, syn) in &flat.syntax {
        let name = flat.engine.symbol(fsym).name();
        let dom: Vec<KindId> = syn.domain.iter().map(|&s| fsorts.kind_of(s)).collect();
        flat_by_profile.insert((name, dom, fsorts.kind_of(syn.range)), fsym);
    }
    let map_sort = |hs: SortId| -> Option<SortId> {
        // A declared sort maps by name; an error/kind sort by its kind (its name isn't in the `sorts` map).
        let name = hsorts.name(hs);
        if let Some(&f) = flat.sorts.get(name) {
            return Some(f);
        }
        Some(fsorts.error_sort(*kind_map.get(&hsorts.kind_of(hs))?))
    };
    let map_sym = |hsym: SymbolId| -> Option<SymbolId> {
        let syn = home.built.syntax.get(&hsym)?;
        let name = home.built.engine.symbol(hsym).name();
        let dom: Vec<KindId> =
            syn.domain.iter().map(|&s| kind_map.get(&hsorts.kind_of(s)).copied()).collect::<Option<_>>()?;
        let rng = *kind_map.get(&hsorts.kind_of(syn.range))?;
        flat_by_profile.get(&(name, dom, rng)).copied()
    };
    let remap = |a: Action| -> Option<Action> {
        Some(match a {
            Action::MakeTerm(s) => Action::MakeTerm(map_sym(s)?),
            Action::MakeVariable(s) => Action::MakeVariable(map_sort(s)?),
            Action::MakeNatural(s) => Action::MakeNatural(map_sym(s)?),
            Action::MakeInteger(s) => Action::MakeInteger(map_sym(s)?),
            Action::MakeIter(s) => Action::MakeIter(map_sym(s)?),
            Action::MakeString(s) => Action::MakeString(map_sym(s)?),
            Action::MakeQid(s) => Action::MakeQid(map_sym(s)?),
            Action::MakeFloat(s) => Action::MakeFloat(map_sym(s)?),
            Action::MakeRational { division, minus } => {
                Action::MakeRational { division: map_sym(division)?, minus: map_sym(minus)? }
            }
            keep @ (Action::PassThru | Action::AssocList | Action::Nop) => keep,
        })
    };
    let mut g = home.grammar.clone();
    for prod in &mut g.prods {
        prod.action = remap(prod.action)?;
    }
    Some(g)
}

/// Surface-parse `src`, then build every module (signature + grammar + statements). This loader builds
/// each module **standalone** (no import resolution); a module with `imports` is rejected — use the
/// `tnk-modules` `load_program`, which flattens first. (Keeps the frontend's own import-free tests here.)
pub fn load_source(src: &str) -> Result<Loaded, String> {
    let mut interner = Interner::new();
    let toks = tokenize(src, &mut interner);
    // The frontend loader is import-free and view-free (the module system, `tnk-modules`, handles both);
    // any `view` in the source is ignored here.
    let Source { modules: pre, commands, .. } = Parser::new(&toks, &interner).parse_source()?;

    let mut modules = Vec::with_capacity(pre.len());
    for pm in &pre {
        if !pm.imports.is_empty() {
            return Err(format!(
                "module `{}` has imports — load it through tnk-modules `load_program` (which flattens)",
                pm.name
            ));
        }
        modules.push(build_loaded_module(pm, &mut interner)?);
    }
    Ok(Loaded { interner, modules, commands })
}

/// Parse + build + add each of the module's statement bubbles to the engine, all against the flattened
/// module's own grammar `g`. The import-free / meta / REPL-legacy entry (no home information); the module
/// system's [`build_loaded_module_homed`] adds the D1a per-statement home grammars on top.
fn load_statements(
    pm: &PreModule,
    m: &mut BuiltModule,
    g: &CompiledGrammar,
    i: &Interner,
) -> Result<(), String> {
    load_statements_homed(pm, m, g, &[], &|_| None, i)
}

/// Parse + build + add each statement, with the **D1a import-reparse point-fix**: a statement that fails
/// to parse in the flattened grammar `g` (typically because an importer's operator/constant made an
/// imported bubble ambiguous) is retried against its **home** module's own grammar — re-pointed at this
/// flattened module's symbol table by [`remap_home_grammar`]. `homes[k]` is the home-module name of
/// `pm.statements[k]` (from `flatten_with_homes`), `None` or the flattened module's own name meaning "use
/// the flattened grammar"; `home_mod` resolves a home name to its already-built [`LoadedModule`] (the
/// REPL's / loader's module cache). When `homes` is empty this is exactly the pre-fix loader.
pub fn load_statements_homed<'m>(
    pm: &PreModule,
    m: &mut BuiltModule,
    g: &CompiledGrammar,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    i: &Interner,
) -> Result<(), String> {
    // Object-pattern completion context (Pillar 2.5-E): resolved once for an `omod`'s flattened module
    // (the CONFIGURATION object constructor / AttributeSet symbol / class sorts). `None` for a non-object
    // module, or one with no object constructor in scope — completion then never runs.
    let oo = pm.is_object.then(|| m.engine.oo_info()).flatten();
    // Cache of home-module grammars remapped onto this flattened module's symbols (built lazily, only when
    // a statement actually fails the flattened parse — so the common path pays nothing). `None` = the home
    // is not resolvable / could not be remapped, so no retry.
    let mut home_grammars: HashMap<String, Option<CompiledGrammar>> = HashMap::new();

    for (idx, stmt) in pm.statements.iter().enumerate() {
        // Skip `nonexec` axioms — proof obligations never applied during reduction/rewriting (every
        // theory axiom is `[nonexec]`; a module statement may be too). They still carry through parsing
        // and flattening (for later view-obligation checking) but are not registered in the engine.
        if stmt_is_nonexec(stmt) {
            continue;
        }
        // A statement whose bubbles fail to parse/build is DROPPED (Maude warns per statement and keeps
        // the module — fable-audit.md §3.4), so a later command still sees a whole module rather than a
        // "no current module". `load_one_stmt` registers nothing before its fallible parse completes, so a
        // failed attempt leaves the engine (and the dense trace indices) consistent and can be retried.
        let flat_err = match load_one_stmt(stmt, m, g, false, &oo, i) {
            Ok(()) => continue,
            Err(e) => e,
        };
        // Failed against the flattened grammar. If this statement was donated by a distinct home module,
        // retry against that home's own grammar (re-pointed at this module's symbols) — the D1a point-fix.
        if let Some(home) = homes.get(idx).and_then(|h| h.as_deref())
            && home != m.name
        {
            if !home_grammars.contains_key(home) {
                let remapped = home_mod(home).and_then(|lm| remap_home_grammar(lm, m));
                home_grammars.insert(home.to_string(), remapped);
            }
            if let Some(hg) = home_grammars.get(home).and_then(Option::as_ref)
                && load_one_stmt(stmt, m, hg, true, &oo, i).is_ok()
            {
                continue;
            }
        }
        if std::env::var("TNK_DEBUG_DROP").is_ok() {
            eprintln!("DROP[{}]: {flat_err}", m.name);
        }
        // Drop this statement and keep building the module (the diagnostic is phase E).
    }
    Ok(())
}

/// Parse + build + register one statement's bubbles into `m`, parsing against grammar `g`. `home` selects
/// the D1a home-grammar path: the rhs is then parsed at the universal start (`g` is the statement's own
/// unambiguous home grammar, so the flattened-grammar kind-homogeneity trick is neither needed nor valid —
/// its `Nt::Comp(kind, …)` start would name a *flattened* kind absent from the home grammar). Registers
/// nothing before the last fallible parse, so a returned `Err` leaves `m` unchanged (safe to retry).
fn load_one_stmt(
    stmt: &Statement,
    m: &mut BuiltModule,
    g: &CompiledGrammar,
    home: bool,
    oo: &Option<tnk_core::engine::OoInfo>,
    i: &Interner,
) -> Result<(), String> {
    // Parse + build the rhs: kind-homogeneous with the lhs against the flattened grammar (disambiguates a
    // bare overloaded constant), or universal in the home-grammar path.
    let build_rhs = |rhs: &[Token], lhs_t: &Term, m: &BuiltModule, vars: &mut VarIndex| {
        if home {
            parse_build(rhs, g, m, i, vars)
        } else {
            parse_build_rhs(rhs, lhs_t, g, m, i, vars)
        }
    };
    match stmt {
        Statement::Eq { lhs, rhs, cond, owise, label, .. } => {
            // Build order: lhs → condition (assigns fresh `:=` vars + tracks bound) → rhs, all sharing
            // one variable index. Then add via the matching kernel facade.
            let mut vars = VarIndex::new();
            let mut lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let mut condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            let mut rhs_t = build_rhs(rhs, &lhs_t, m, &mut vars)?;
            if let Some(info) = oo {
                oo_complete::complete_statement(
                    info, m, &mut vars, &mut lhs_t, Some(&mut rhs_t), &mut condition,
                );
            }
            let nr = vars.count();
            // Capture the source-form trace metadata before the Terms are moved into the kernel; the
            // kernel returns the dense equation id, which must index `eq_traces` (asserted).
            reject_rewrite_fragment(&condition, "equation")?;
            if !statement_vars_bound(&lhs_t, &condition, Some(&rhs_t)) {
                return Ok(()); // unbound rhs/condition variable: Maude warns + nonexecs (§3.1 A1c)
            }
            let trace = EqTrace {
                lhs: lhs_t.clone(),
                rhs: rhs_t.clone(),
                condition: condition.clone(),
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                owise: *owise,
                label: label.clone(),
                nonexec: false, // engine-registered ⇒ executable
            };
            let id = if *owise {
                m.engine.add_owise_equation(lhs_t, rhs_t, nr, condition)
            } else if condition.is_empty() {
                m.engine.add_equation(Equation { lhs: lhs_t, rhs: rhs_t, nr_vars: nr })
            } else {
                m.engine.add_conditional_equation(lhs_t, rhs_t, nr, condition)
            };
            assert_eq!(id as usize, m.eq_traces.len(), "equation id is the dense eq_traces index");
            m.eq_traces.push(trace);
        }
        Statement::Mb { lhs, sort, cond, label, .. } => {
            let mut vars = VarIndex::new();
            let mut lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let sort_id = resolve_sort(sort, m, i)?;
            let mut condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            if let Some(info) = oo {
                oo_complete::complete_statement(info, m, &mut vars, &mut lhs_t, None, &mut condition);
            }
            let nr = vars.count();
            reject_rewrite_fragment(&condition, "membership")?;
            if !statement_vars_bound(&lhs_t, &condition, None) {
                return Ok(()); // unbound condition variable: Maude warns + nonexecs (§3.1 A1c)
            }
            let trace = MbTrace {
                lhs: lhs_t.clone(),
                sort: sort_id,
                condition: condition.clone(),
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                label: label.clone(),
                nonexec: false, // engine-registered ⇒ executable
            };
            let id = if condition.is_empty() {
                m.engine.add_membership(Membership { lhs: lhs_t, sort: sort_id, nr_vars: nr })
            } else {
                m.engine.add_conditional_membership(lhs_t, sort_id, nr, condition)
            };
            assert_eq!(id as usize, m.mb_traces.len(), "membership id is the dense mb_traces index");
            m.mb_traces.push(trace);
        }
        Statement::Rule { label, lhs, rhs, cond, .. } => {
            // Same build order as an equation (lhs → condition → rhs, sharing one variable index;
            // matches Maude's `equation.cc` numbering); registered in the kernel's separate rule table.
            let mut vars = VarIndex::new();
            let mut lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let mut condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            let mut rhs_t = build_rhs(rhs, &lhs_t, m, &mut vars)?;
            if let Some(info) = oo {
                oo_complete::complete_statement(
                    info, m, &mut vars, &mut lhs_t, Some(&mut rhs_t), &mut condition,
                );
            }
            let nr = vars.count();
            if !statement_vars_bound(&lhs_t, &condition, Some(&rhs_t)) {
                return Ok(()); // unbound rhs/condition variable: Maude warns + nonexecs (§3.1 A1c)
            }
            let trace = RlTrace {
                lhs: lhs_t.clone(),
                rhs: rhs_t.clone(),
                condition: condition.clone(),
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                label: label.clone(),
                nonexec: false, // engine-registered ⇒ executable
            };
            let id = if condition.is_empty() {
                m.engine.add_rule(lhs_t, rhs_t, nr)
            } else {
                m.engine.add_conditional_rule(lhs_t, rhs_t, nr, condition)
            };
            assert_eq!(id as usize, m.rl_traces.len(), "rule id is the dense rl_traces index");
            m.rl_traces.push(trace);
        }
    }
    Ok(())
}

/// One statement parsed into its trace form (the sum of the three engine-trace kinds). Produced by
/// [`parse_statement_trace`] for statements that carry no engine trace.
pub enum StmtTrace {
    Eq(EqTrace),
    Mb(MbTrace),
    Rl(RlTrace),
}

/// Parse a statement's raw bubbles into its [`StmtTrace`] against an already-built module's grammar and
/// signature, **without** registering it in the engine and **without** object-pattern completion. This is
/// how META up-translation reflects a module's own `[nonexec]` axioms: [`load_statements`] skips them (a
/// proof obligation is applied by neither reduction nor completion, so it carries no engine trace), yet
/// `upEqs`/`upMbs`/`upRls`/`upModule` must still emit them. Mirrors the per-statement parse in
/// [`load_statements`] (lhs → condition → rhs, sharing one variable index); the returned trace carries the
/// statement's `nonexec`/`owise`/`label` for the up-translated `AttrSet`.
pub fn parse_statement_trace(
    stmt: &Statement,
    m: &BuiltModule,
    g: &CompiledGrammar,
    i: &Interner,
) -> Result<StmtTrace, String> {
    match stmt {
        Statement::Eq { lhs, rhs, cond, owise, nonexec, label } => {
            let mut vars = VarIndex::new();
            let lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            let rhs_t = parse_build_rhs(rhs, &lhs_t, g, m, i, &mut vars)?;
            reject_rewrite_fragment(&condition, "equation")?;
            let nr = vars.count();
            Ok(StmtTrace::Eq(EqTrace {
                lhs: lhs_t,
                rhs: rhs_t,
                condition,
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                owise: *owise,
                label: label.clone(),
                nonexec: *nonexec,
            }))
        }
        Statement::Mb { lhs, sort, cond, nonexec, label } => {
            let mut vars = VarIndex::new();
            let lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let sort_id = resolve_sort(sort, m, i)?;
            let condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            reject_rewrite_fragment(&condition, "membership")?;
            let nr = vars.count();
            Ok(StmtTrace::Mb(MbTrace {
                lhs: lhs_t,
                sort: sort_id,
                condition,
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                label: label.clone(),
                nonexec: *nonexec,
            }))
        }
        Statement::Rule { label, lhs, rhs, cond, nonexec } => {
            let mut vars = VarIndex::new();
            let lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            let rhs_t = parse_build_rhs(rhs, &lhs_t, g, m, i, &mut vars)?;
            // (a rule condition may carry a rewrite fragment `t => p`, so no reject here)
            let nr = vars.count();
            Ok(StmtTrace::Rl(RlTrace {
                lhs: lhs_t,
                rhs: rhs_t,
                condition,
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                label: label.clone(),
                nonexec: *nonexec,
            }))
        }
    }
}

/// The connective of a condition fragment.
enum Connective {
    /// `pattern := subject` (matching).
    Match,
    /// `lhs = rhs` (equality).
    Eq,
    /// `term : sort` (sort test).
    Sort,
    /// `lhs => pattern` (rewrite condition — rules only, Pillar A-v).
    Rewrite,
}

/// Parse a condition bubble (the tokens after `if`) into kernel [`ConditionFragment`]s: split on `/\` at
/// paren-depth 0, then each fragment on its connective. Shares the statement's variable index; a `:=`
/// fragment's *fresh* variables are the pattern variables not already bound (by the lhs or an earlier
/// fragment), which the matcher binds.
pub(crate) fn parse_condition(
    bubble: &[Token],
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
    bound: &mut BTreeSet<u32>,
) -> Result<Vec<ConditionFragment>, String> {
    let mut frags = Vec::new();
    for ftoks in split_on_text(bubble, "/\\", i) {
        let Some((left, conn, right)) = split_connective(ftoks, i) else {
            // A bare boolean fragment `b` abbreviates `b = true` (Maude's abbreviated condition). The
            // `true` anchor (SystemTrue) is present whenever BOOL is in scope — which it must be for a
            // boolean-valued condition to typecheck.
            let lhs = parse_build(ftoks, g, m, i, vars)?;
            let true_sym = m
                .true_sym
                .ok_or("bare boolean condition, but no `true` is in scope (import BOOL)")?;
            frags.push(ConditionFragment::Equality { lhs, rhs: Term::constant(true_sym) });
            continue;
        };
        let frag = match conn {
            Connective::Match => {
                let pattern = parse_build(left, g, m, i, vars)?;
                let subject = parse_build(right, g, m, i, vars)?;
                let mut pat_vars = Vec::new();
                term_var_indices(&pattern, &mut pat_vars);
                let fresh: Vec<u32> = pat_vars.iter().copied().filter(|v| !bound.contains(v)).collect();
                bound.extend(pat_vars);
                ConditionFragment::Matching { pattern, subject, fresh_vars: fresh }
            }
            Connective::Eq => ConditionFragment::Equality {
                lhs: parse_build(left, g, m, i, vars)?,
                rhs: parse_build(right, g, m, i, vars)?,
            },
            Connective::Rewrite => {
                // `lhs => pattern`: build the source (its variables already bound), then the target
                // pattern — whose variables not yet bound are fresh (the `=>*` search binds them).
                let lhs = parse_build(left, g, m, i, vars)?;
                let pattern = parse_build(right, g, m, i, vars)?;
                let mut pat_vars = Vec::new();
                term_var_indices(&pattern, &mut pat_vars);
                let fresh: Vec<u32> = pat_vars.iter().copied().filter(|v| !bound.contains(v)).collect();
                bound.extend(pat_vars);
                ConditionFragment::Rewrite { lhs, pattern, fresh_vars: fresh }
            }
            Connective::Sort => ConditionFragment::SortTest {
                term: parse_build(left, g, m, i, vars)?,
                sort: resolve_sort(right, m, i)?,
            },
        };
        frags.push(frag);
    }
    Ok(frags)
}

/// Split `toks` on the `sep`-text token at paren-depth 0 (e.g. `/\`). Always yields ≥ 1 part.
fn split_on_text<'a>(toks: &'a [Token], sep: &str, i: &Interner) -> Vec<&'a [Token]> {
    let mut parts = Vec::new();
    let (mut depth, mut start) = (0i32, 0usize);
    for (k, t) in toks.iter().enumerate() {
        match i.resolve(t.sym) {
            "(" => depth += 1,
            ")" => depth -= 1,
            s if depth == 0 && s == sep => {
                parts.push(&toks[start..k]);
                start = k + 1;
            }
            _ => {}
        }
    }
    parts.push(&toks[start..]);
    parts
}

/// Find a fragment's connective token (`:=` / `=` / `:` / `=>`) at paren-depth 0 and split around it.
/// `None` if the fragment has no connective — a **bare boolean** condition `b`, which the caller
/// desugars to `b = true` (Maude's abbreviated condition, e.g. `ceq X < Z = true if X < Y /\ Y < Z`).
fn split_connective<'a>(
    toks: &'a [Token],
    i: &Interner,
) -> Option<(&'a [Token], Connective, &'a [Token])> {
    let mut depth = 0i32;
    for (k, t) in toks.iter().enumerate() {
        let conn = match i.resolve(t.sym) {
            "(" => {
                depth += 1;
                None
            }
            ")" => {
                depth -= 1;
                None
            }
            ":=" if depth == 0 => Some(Connective::Match),
            // `=>` lexes as a single token, distinct from `=`, so the order of these arms is irrelevant.
            "=>" if depth == 0 => Some(Connective::Rewrite),
            "=" if depth == 0 => Some(Connective::Eq),
            ":" if depth == 0 => Some(Connective::Sort),
            _ => None,
        };
        if let Some(conn) = conn {
            return Some((&toks[..k], conn, &toks[k + 1..]));
        }
    }
    None
}

/// Whether a statement is `[nonexec]` (a proof obligation not applied during execution).
fn stmt_is_nonexec(s: &Statement) -> bool {
    match s {
        Statement::Eq { nonexec, .. }
        | Statement::Mb { nonexec, .. }
        | Statement::Rule { nonexec, .. } => *nonexec,
    }
}

/// Reject a rewrite (`=>`) fragment in a non-rule condition — `=>` conditions are legal only in rules
/// (`crl`), never in an `ceq`/`cmb` (Pillar A-v). The clean user-facing guard ahead of the kernel's
/// defensive `compile_condition` assert.
fn reject_rewrite_fragment(condition: &[ConditionFragment], owner: &str) -> Result<(), String> {
    if condition.iter().any(|f| matches!(f, ConditionFragment::Rewrite { .. })) {
        return Err(format!("a rewrite condition (`=>`) is only allowed in a rule (`crl`), not an {owner}"));
    }
    Ok(())
}

/// Collect a term's distinct variable indices, in first-seen order.
/// Whether every variable a statement *instantiates* is bound by the time it is needed: rhs and each
/// condition fragment's evaluated side may use only lhs variables plus the fresh binders of *earlier*
/// `:=`/`=>` fragments (Maude's "used before it is bound" check). A violating statement is degraded to
/// non-executable — parsed but never registered — instead of panicking at `instantiate` (§3.1 A1c); the
/// warning text is deferred diagnostics (roadmap phase E).
fn statement_vars_bound(lhs: &Term, condition: &[ConditionFragment], rhs: Option<&Term>) -> bool {
    let mut bound = Vec::new();
    term_var_indices(lhs, &mut bound);
    let ok = |t: &Term, bound: &Vec<u32>| {
        let mut used = Vec::new();
        term_var_indices(t, &mut used);
        used.iter().all(|v| bound.contains(v))
    };
    for frag in condition {
        let frag_ok = match frag {
            ConditionFragment::Equality { lhs, rhs } => ok(lhs, &bound) && ok(rhs, &bound),
            ConditionFragment::SortTest { term, .. } => ok(term, &bound),
            ConditionFragment::Matching { subject, fresh_vars, .. } => {
                let r = ok(subject, &bound);
                bound.extend_from_slice(fresh_vars);
                r
            }
            ConditionFragment::Rewrite { lhs, fresh_vars, .. } => {
                let r = ok(lhs, &bound);
                bound.extend_from_slice(fresh_vars);
                r
            }
        };
        if !frag_ok {
            return false;
        }
    }
    rhs.is_none_or(|r| ok(r, &bound))
}

pub(crate) fn term_var_indices(t: &Term, out: &mut Vec<u32>) {
    match t {
        Term::Var(v) => {
            if !out.contains(&v.index) {
                out.push(v.index);
            }
        }
        Term::Na { .. } => {} // a literal introduces no variables
        Term::Op { args, .. } => {
            for a in args {
                term_var_indices(a, out);
            }
        }
    }
}

/// Parse a term token bubble to its (unambiguous) parse tree; rejects empty input, no-parse, and ambiguity.
fn parse_forest(tokens: &[Token], g: &CompiledGrammar, i: &Interner) -> Result<PTree, String> {
    let parsed = parse_forest_any(tokens, g, i)?;
    if parsed.ambiguous {
        let rendered = tokens.iter().map(|t| i.resolve(t.sym)).collect::<Vec<_>>().join(" ");
        return Err(format!("ambiguous parse: `{rendered}`"));
    }
    Ok(parsed.tree)
}

/// Parse a **command** term bubble, warn-and-pick on ambiguity (decision D9): Maude warns and takes
/// its first parse — our extraction is the same `extractFirstSubparse` walk (first split in
/// chart/completion order, pass2.cc), so the picked tree is used; the warning text is deferred
/// diagnostics (phase E). Statement bubbles keep the strict [`parse_forest`]: their ambiguity today
/// is dominated by the import-reparse artifact (D1a), where a noisy error is the safer behavior
/// until the home-grammar fix lands.
fn parse_forest_pick(tokens: &[Token], g: &CompiledGrammar, i: &Interner) -> Result<PTree, String> {
    Ok(parse_forest_any(tokens, g, i)?.tree)
}

fn parse_forest_any(
    tokens: &[Token],
    g: &CompiledGrammar,
    i: &Interner,
) -> Result<forest::Parse, String> {
    if tokens.is_empty() {
        return Err("empty term".into());
    }
    let rendered = || tokens.iter().map(|t| i.resolve(t.sym)).collect::<Vec<_>>().join(" ");
    let chart = earley::parse(g, tokens, Nt::Term, i);
    forest::extract(g, &chart, tokens.len(), Nt::Term).map_err(|e| format!("{e}: `{}`", rendered()))
}

/// Parse a term token bubble and build its kernel [`Term`] (the statement/pattern path).
pub(crate) fn parse_build(
    tokens: &[Token],
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    build_term(&parse_forest(tokens, g, i)?, g, m, tokens, i, vars)
}

/// The kind of a built term's top — its top symbol's range, or `None` for a bare variable (whose kind we
/// don't constrain against). Used to parse an equation's rhs in the *same* kind as its lhs.
fn term_kind(t: &Term, m: &BuiltModule) -> Option<KindId> {
    t.top_symbol().map(|s| m.engine.symbol_kind(s))
}

/// Parse + build the rhs of an equation/rule **kind-homogeneously** with its lhs: an equation's two sides
/// share one kind, so a bare overloaded constant (`none` — declared at a dozen sorts across META-MODULE)
/// is disambiguated by the lhs's kind, exactly as Maude parses `eq … = none .`. The rhs is parsed at the
/// lhs kind's term nonterminal; if that yields no parse (a malformed/cross-kind rhs), we fall back to the
/// unconstrained universal start so the original error surfaces.
fn parse_build_rhs(
    rhs: &[Token],
    lhs: &Term,
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    if let Some(k) = term_kind(lhs, m) {
        let start = Nt::Comp(k, NtType::Term);
        if let Ok(tree) = parse_forest_at(rhs, g, i, start) {
            return build_term(&tree, g, m, rhs, i, vars);
        }
    }
    parse_build(rhs, g, m, i, vars)
}

/// Like [`parse_forest`] but starting at an arbitrary nonterminal (a per-kind term nonterminal), to parse
/// a bubble constrained to one kind.
fn parse_forest_at(tokens: &[Token], g: &CompiledGrammar, i: &Interner, start: Nt) -> Result<PTree, String> {
    if tokens.is_empty() {
        return Err("empty term".into());
    }
    let chart = earley::parse(g, tokens, start, i);
    let parsed = forest::extract(g, &chart, tokens.len(), start).map_err(|e| format!("{e}"))?;
    if parsed.ambiguous {
        return Err("ambiguous parse".into());
    }
    Ok(parsed.tree)
}

/// Resolve a sort token bubble to a [`SortId`]. A plain sort is one token; a **structured** sort
/// (`NeList{X}`) lexes as several tokens (`NeList`, `{`, `X`, `}`) which reassemble — no spaces — into the
/// canonical sort name the signature stored.
fn resolve_sort(tokens: &[Token], m: &BuiltModule, i: &Interner) -> Result<SortId, String> {
    let name: String = tokens.iter().map(|t| t.text(i)).collect();
    m.sorts.get(&name).copied().ok_or_else(|| format!("unknown sort `{name}`"))
}

/// Parse, build, and reduce a ground command term; returns `(result, rewrite count)`. Builds the term
/// directly as a DAG ([`build_dag`]) so built-in literals (string/qid/float) and compact numerals work.
/// The Maude-faithful command echo for `reduce in M : <term> .`: the parsed term, theory-normalized and
/// pretty-printed exactly as the reference binary prints it — so float / rational / negative special
/// constants collapse to their canonical surface form (`1.0e+2`, `2/4`, `-3`), redundant parens drop, and
/// AC arguments appear in the kernel's canonical order, matching Maude's "normalize, then print" echo
/// behaviour. Builds the pre-reduction DAG (a second, cheap parse — the echo is interactive-only) and
/// renders it; returns an error if the term does not parse, so the caller can fall back to a raw rendering.
pub fn command_echo(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &[Token],
    color: bool,
) -> Result<String, String> {
    let tree = parse_forest_pick(term, &lm.grammar, i)?;
    let dag = build_subject_dag(lm, &tree, term, i)?;
    let dag = collapse_one_sided(&mut lm.built.engine, &lm.built.one_sided_id, dag);
    Ok(print_pretty(&lm.built, i, dag, color))
}

pub fn reduce_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &[Token],
) -> Result<(DagId, u64), String> {
    let tree = parse_forest_pick(term, &lm.grammar, i)?;
    // Reset BEFORE building so this command's count starts clean. Construction itself does no rewrites
    // (C1: membership axioms now apply lazily at the reduce normal-form point, not at construction); the
    // `reduce` below is where every equation and membership application is counted (Maude's accounting).
    lm.built.engine.reset_rewrites();
    // C7: build the subject inside a structural-dedup window so a repeated subterm (`< g(a), g(a) >`)
    // becomes one shared node — `reduce` then normalizes it once, matching Maude's hash-consed subject
    // DAG. The window must close before `reduce` (it spans only construction); end it even on a build
    // error, then propagate, so a failed parse never leaks an open window into the next command.
    lm.built.engine.begin_dedup();
    let dag = build_subject_dag(lm, &tree, term, i);
    lm.built.engine.end_dedup();
    let dag = dag?;
    let dag = collapse_one_sided(&mut lm.built.engine, &lm.built.one_sided_id, dag);
    let result = lm.built.engine.reduce(dag);
    Ok((result, lm.built.engine.rewrites()))
}

/// Parse + build a ground command subject DAG, resetting the rewrite counter and building inside a dedup
/// window exactly like [`reduce_command`]. Shared by the `rewrite`/`frewrite` session builders and the
/// REPL's `reduce` (which then drives [`Engine::reduce_with`](tnk_core::engine::Engine::reduce_with) for
/// META-LEVEL descent).
pub fn build_command_dag(lm: &mut LoadedModule, i: &Interner, term: &[Token]) -> Result<DagId, String> {
    let tree = parse_forest_pick(term, &lm.grammar, i)?;
    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let dag = build_subject_dag(lm, &tree, term, i);
    lm.built.engine.end_dedup();
    let dag = dag?;
    Ok(collapse_one_sided(&mut lm.built.engine, &lm.built.one_sided_id, dag))
}

/// Build a command's subject DAG from its parse tree, handling BOTH ground terms (the [`build_dag`] fast
/// path — compact literals/numerals) and **open** terms with variables. Maude reduces open terms (a
/// variable is inert under reduction — `red X:A .`, `red g(X, a) .`, `red N + 1 .`, fable-audit.md §3.4);
/// tnk's kernel DAG has no variable node, so each distinct variable is realized as a fresh nullary
/// constant of its declared sort, named for the variable's print form — a declared var prints bare (`N`),
/// an on-the-fly var with its sort (`X:A`), because that is the variable's source token. The [`VarIndex`]
/// dedups by name, so a repeated variable shares one constant (`g(X, X)` stays linked). The atom is
/// irreducible (no equation names it), so reduction is a no-op on it, exactly like Maude's inert variable.
fn build_subject_dag(
    lm: &mut LoadedModule,
    tree: &PTree,
    term: &[Token],
    i: &Interner,
) -> Result<DagId, String> {
    if !tree_has_var(tree, &lm.grammar) {
        return build_dag(
            tree, &lm.grammar, &mut lm.built.engine, lm.built.nat_zero, lm.built.nat_succ, term, i,
        );
    }
    let mut vars = VarIndex::new();
    let t = build_term(tree, &lm.grammar, &lm.built, term, i, &mut vars)?;
    let bindings: Vec<DagId> = (0..vars.count())
        .map(|idx| {
            let sym = lm.built.engine.add_op(vars.name(idx).to_string(), vec![], vars.sort(idx));
            // Class the atom as a variable: `.=.`'s stability/groundness analysis must see Maude's
            // VariableSymbol (never stable, never ground), and comm/AC canonical ordering must
            // compare same-sort variables by name-token code (the variable's source token is
            // guaranteed interned — it was lexed), not by symbol creation order.
            let rank = i.get(vars.name(idx)).map(|s| s.index()).unwrap_or(u32::MAX);
            lm.built.engine.set_symbol_class(sym, tnk_core::symbol::SymbolClass::Variable { rank });
            lm.built.engine.make_const(sym)
        })
        .collect();
    Ok(lm.built.engine.instantiate_bindings(&t, &bindings))
}

/// Whether a parse tree contains a variable (a [`Action::MakeVariable`] production) — the ground/open
/// dispatch for [`build_subject_dag`].
fn tree_has_var(tree: &PTree, g: &CompiledGrammar) -> bool {
    matches!(g.prods[tree.prod as usize].action, Action::MakeVariable(_))
        || tree.nt_children.iter().any(|c| tree_has_var(c, g))
}

/// Apply the declared-side collapse for one-sided-`id:` operators (`assoc left id: e` / `right id: e`) to a
/// freshly built command DAG. The kernel registered these ops **without** an identity — its collapse is
/// two-sided (fable-audit.md §3.4) — so `make_au`/`make_cui` left the identity arguments in place; here the
/// leading (left) / trailing (right) identity elements are dropped and the node rebuilt. Recurses so nested
/// occurrences are handled. A no-op (returns `dag`) when the module declares no one-sided op (`map` empty),
/// so ordinary reduction pays nothing. (Construction-time only — a faithful one-sided identity in matching
/// and equation-rhs construction needs the kernel `make_au`, which is out of scope here.)
fn collapse_one_sided(
    engine: &mut tnk_core::engine::Engine,
    map: &std::collections::HashMap<tnk_core::symbol::SymbolId, (crate::surface::ast::IdSide, tnk_core::symbol::SymbolId)>,
    dag: DagId,
) -> DagId {
    use crate::surface::ast::IdSide;
    if map.is_empty() {
        return dag;
    }
    let sym = engine.node(dag).symbol();
    let children: Vec<DagId> = engine.node(dag).children().collect();
    if children.is_empty() {
        return dag; // a leaf (constant / built-in literal) has no arguments to collapse
    }
    let new_children: Vec<DagId> =
        children.iter().map(|&c| collapse_one_sided(engine, map, c)).collect();
    let child_changed = new_children != children;
    if let Some(&(side, idc)) = map.get(&sym) {
        // An element is the identity constant iff it is `idc` applied to no arguments.
        let mut kids = new_children;
        match side {
            IdSide::Left => {
                while let Some(&c) = kids.first() {
                    let n = engine.node(c);
                    if n.symbol() == idc && n.children().next().is_none() {
                        kids.remove(0);
                    } else {
                        break;
                    }
                }
            }
            IdSide::Right => {
                while let Some(&c) = kids.last() {
                    let n = engine.node(c);
                    if n.symbol() == idc && n.children().next().is_none() {
                        kids.pop();
                    } else {
                        break;
                    }
                }
            }
            IdSide::Both => {}
        }
        return match kids.len() {
            0 => engine.make_const(idc),            // every element was the identity → the identity itself
            1 => kids.into_iter().next().unwrap(),  // a lone survivor is the term (also avoids CUI's binary assert)
            _ => engine.make_node(sym, kids),
        };
    }
    if child_changed {
        engine.make_node(sym, new_children)
    } else {
        dag
    }
}

/// The token index where a failed command/term parse got stuck — the furthest token a valid partial
/// parse consumed (Maude's `badTokenIndex`). `metaParse` reports this as `noParse(n)` (fable-audit.md
/// §3.3 B4); parsed at the universal `Term` start, matching [`build_command_dag`].
pub fn command_parse_furthest(lm: &LoadedModule, i: &Interner, term: &[Token]) -> usize {
    earley::parse(&lm.grammar, term, Nt::Term, i).furthest()
}

/// Begin a `rewrite` (rule-fair) session over `term` (Pillar A). The caller drives the returned
/// [`Rewriting`] with [`Rewriting::run`] and stores it for `continue`.
pub fn rewrite_command(lm: &mut LoadedModule, i: &Interner, term: &[Token]) -> Result<Rewriting, String> {
    let dag = build_command_dag(lm, i, term)?;
    Ok(lm.built.engine.rewrite(dag))
}

/// Begin a `frewrite` (position-fair) session over `term` (Pillar A-ii); `gas` rule applications per
/// position per pass.
pub fn frewrite_command(lm: &mut LoadedModule, i: &Interner, term: &[Token], gas: u64) -> Result<Rewriting, String> {
    let dag = build_command_dag(lm, i, term)?;
    Ok(lm.built.engine.frewrite(dag, gas))
}

/// Begin an `erewrite` (object-message-fair) session over `term` (Pillar 2.5-B); `gas` is the
/// per-position gas for the non-config fallback (default 1).
pub fn erewrite_command(lm: &mut LoadedModule, i: &Interner, term: &[Token], gas: u64) -> Result<Rewriting, String> {
    let dag = build_command_dag(lm, i, term)?;
    Ok(lm.built.engine.erewrite(dag, gas))
}

/// Begin a `search` (Pillar A-iv): build the subject DAG + the goal pattern (a [`Term`], its variable
/// names tracked for rendering) + the optional `such that` condition over the goal's variables, then
/// open the [`Search`] for `arrow` up to `max_depth`. Returns the session and the goal's [`VarIndex`]
/// (for the `Var:Sort --> value` solution lines).
#[allow(clippy::too_many_arguments)]
pub fn search_command(
    lm: &mut LoadedModule,
    i: &Interner,
    subject: &[Token],
    arrow: SearchArrow,
    pattern: &[Token],
    such_that: Option<&[Token]>,
    max_depth: Option<u64>,
) -> Result<(Search, VarIndex), String> {
    // Goal pattern + such-that condition share one variable index.
    let mut vars = VarIndex::new();
    let pat = parse_build(pattern, &lm.grammar, &lm.built, i, &mut vars)?;
    let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
    let cond = match such_that {
        Some(c) => parse_condition(c, &lm.grammar, &lm.built, i, &mut vars, &mut bound)?,
        None => Vec::new(),
    };
    let nr = vars.count();
    // Subject as a ground DAG (reset the counter so the search's rewrites start clean).
    lm.built.engine.reset_rewrites();
    let subj_tree = parse_forest_pick(subject, &lm.grammar, i)?;
    lm.built.engine.begin_dedup();
    let subj = build_dag(&subj_tree, &lm.grammar, &mut lm.built.engine, lm.built.nat_zero, lm.built.nat_succ, subject, i);
    lm.built.engine.end_dedup();
    let subj = subj?;
    let arrow = match arrow {
        SearchArrow::One => Arrow::One,
        SearchArrow::Plus => Arrow::Plus,
        SearchArrow::Star => Arrow::Star,
        SearchArrow::Bang => Arrow::Bang,
    };
    let search = lm.built.engine.search(subj, pat, nr, cond, arrow, max_depth.map(|d| d as u32));
    Ok((search, vars))
}

/// The matched-portion id (for `xmatch`) and binding ids of one match solution, captured while the
/// kernel [`tnk_core::engine::Solutions`] stream is live; rendered to text only after it drops (the
/// stream holds `&mut Engine`, the pretty-printer needs `&BuiltModule`).
struct RawSolution {
    /// One `DagId` per pattern variable, indexed `0..nr_vars`.
    bindings: Vec<DagId>,
    /// The matched portion (`xmatch` only): `None` prints no `Matched portion` line (plain `match`, or an
    /// `xmatch` whose subject carried no extension info); `Some(Whole)` prints `(whole)`; `Some(Portion)`
    /// prints the built sub-portion.
    portion: Option<MatchedPortion>,
}

/// Parse + build + enumerate the solutions of a `match`/`xmatch` command. Returns one rendered block
/// per solution (each the `Var --> value` lines, prefixed for `xmatch` by `Matched portion = …`), in
/// the kernel matcher's enumeration order; [`format_matchers`] wraps them into Maude's `Matcher N`
/// display. The blocks are the unit the conformance harness compares against the reference binary —
/// **as a set**, since exact ACU/AU solution *order* (Maude's Diophantine order) is a deferred B1
/// follow-up (§4); every solution and its bindings are reproduced, only the order may differ.
///
/// The pattern is built as a kernel [`Term`] (tracking variable names for display); the subject is
/// built as a ground DAG and reduced to normal form, matching Maude's behaviour (and a no-op on the
/// already-normal conformance subjects). `xmatch` enables extension matching (a sub-part of the
/// subject, leaving a residue); plain `match` requires the whole subject to be consumed.
pub fn match_command(
    lm: &mut LoadedModule,
    i: &Interner,
    pattern: &[Token],
    subject: &[Token],
    xmatch: bool,
) -> Result<Vec<String>, String> {
    let mut vars = VarIndex::new();
    let pat = parse_build(pattern, &lm.grammar, &lm.built, i, &mut vars)?;
    let nr = vars.count();

    let subj_tree = parse_forest_pick(subject, &lm.grammar, i)?;
    // C7: dedup the subject's repeated subterms into shared nodes before reducing (see `reduce_command`).
    lm.built.engine.begin_dedup();
    let subj = build_dag(&subj_tree, &lm.grammar, &mut lm.built.engine, lm.built.nat_zero, lm.built.nat_succ, subject, i);
    lm.built.engine.end_dedup();
    let subj = subj?;
    let subj = lm.built.engine.reduce(subj);

    // Enumerate while the stream borrows the engine, capturing only `DagId`s; render afterwards.
    let mut raws: Vec<RawSolution> = Vec::new();
    {
        let mut sols = lm.built.engine.match_solutions(pat, nr, subj, xmatch);
        while sols.advance() {
            let bindings = (0..nr)
                .map(|k| sols.binding(k).expect("the matcher binds every pattern variable"))
                .collect();
            let portion = if xmatch { sols.matched_portion_display() } else { None };
            raws.push(RawSolution { bindings, portion });
        }
    }

    Ok(raws.iter().map(|r| render_solution(&lm.built, i, r, &vars)).collect())
}

/// Render one solution's body: the `Matched portion = …` line (for `xmatch`) followed by the
/// substitution — either `Var --> value` lines (variable order = first occurrence in the pattern,
/// Maude's index order) or `empty substitution` when the pattern is ground.
fn render_solution(m: &BuiltModule, i: &Interner, sol: &RawSolution, vars: &VarIndex) -> String {
    let mut lines: Vec<String> = Vec::new();
    match sol.portion {
        Some(MatchedPortion::Whole) => lines.push("Matched portion = (whole)".to_string()),
        Some(MatchedPortion::Portion(p)) => {
            lines.push(format!("Matched portion = {}", print_pretty(m, i, p, false)));
        }
        None => {}
    }
    if sol.bindings.is_empty() {
        lines.push("empty substitution".to_string());
    } else {
        for (k, &b) in sol.bindings.iter().enumerate() {
            lines.push(format!("{} --> {}", vars.name(k as u32), print_pretty(m, i, b, false)));
        }
    }
    lines.join("\n")
}

/// Wrap rendered solution blocks into Maude's `match`/`xmatch` display: `No match.` when empty, else
/// each block under a `Matcher N` header, blocks separated by a blank line. (The B5 REPL renderer; the
/// header/`Decision time` framing around it is the command layer's.)
pub fn format_matchers(blocks: &[String]) -> String {
    if blocks.is_empty() {
        return "No match.".to_string();
    }
    blocks
        .iter()
        .enumerate()
        .map(|(n, b)| format!("Matcher {}\n{}", n + 1, b))
        .collect::<Vec<_>>()
        .join("\n\n")
}

/// A [`NameCodes`](tnk_core::unify::NameCodes) source over the session interner: fresh-variable
/// names (`#1`, `#2`, …) are interned into the same code space as user variable names, so the
/// kernel's variable ordering (`dag_compare` on name codes) matches Maude's token-code order. `pub`
/// so the REPL can build one for its own `find_next` loop after `unify_command` returns.
pub struct InternerNames<'a>(pub &'a mut Interner);
impl tnk_core::unify::NameCodes for InternerNames<'_> {
    fn code(&mut self, name: &str) -> u32 {
        self.0.intern(name).index()
    }
}

/// The built pieces of a `unify` command: the pretty-printed echo body (`T1 =? T2 /\ …`, without
/// the `unify in M :` frame or trailing ` .`), the original variables' print names (slot order),
/// and the resumable [`UnifyProblem`](tnk_core::unify::problem::UnifyProblem).
pub struct UnifyCommand {
    pub echo: String,
    pub var_names: Vec<String>,
    /// `false` if any unificand variable has a name that could collide with a fresh `#n`/`%n`/`@n`
    /// variable (Maude's `variableNameConflict`) — the caller then emits only the (stripped)
    /// "unsafe variable name" warning, like a screening failure.
    pub names_ok: bool,
    pub problem: tnk_core::unify::problem::UnifyProblem,
}

/// Build a `unify` command: split the body into `=?`-separated pairs (over `/\`), parse both sides
/// of every pair sharing one [`VarIndex`] (so variable slots are assigned in first-encounter order
/// — the observable order), build the echo and the genuine-`Var`-leaf dags, and construct the
/// order-sorted [`UnifyProblem`](tnk_core::unify::problem::UnifyProblem).
pub fn unify_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    body: &[Token],
) -> Result<UnifyCommand, String> {
    use tnk_core::fresh::VariableFamily;
    use tnk_core::unify::problem::{UnifyProblem, VarSpec};

    // Split on `/\` into conjuncts, each on `=?` into (lhs, rhs); parse both sides sharing `vars`.
    let mut vars = VarIndex::new();
    let mut pairs: Vec<(Term, Term)> = Vec::new();
    for conj in split_on_text(body, "/\\", i) {
        let sides = split_on_text(conj, "=?", i);
        if sides.len() != 2 {
            return Err("unify: each conjunct must be `T1 =? T2`".to_string());
        }
        let lhs = parse_build(sides[0], &lm.grammar, &lm.built, i, &mut vars)?;
        let rhs = parse_build(sides[1], &lm.grammar, &lm.built, i, &mut vars)?;
        pairs.push((lhs, rhs));
    }

    // Echo: each side pretty-printed via the Term printer (variables by their source names), joined
    // with ` =? ` and ` /\ `. Line-wrapping is the REPL's global post-process.
    let var_names: Vec<String> = (0..vars.count()).map(|k| vars.name(k).to_string()).collect();

    // Safe-name check (Maude's `variableNameConflict`): a unificand variable named like a fresh
    // variable (`#1`, `%2`, `@3`) would clash. The bare id is the text before the on-the-fly `:Sort`.
    let namegen = tnk_core::fresh::FreshVariableGenerator::new();
    let names_ok = var_names.iter().all(|n| {
        let bare = n.split(':').next().unwrap_or(n);
        !namegen.variable_name_conflict(bare, None)
    });
    let echo = pairs
        .iter()
        .map(|(l, r)| {
            format!(
                "{} =? {}",
                print_term(&lm.built, i, l, &var_names, false),
                print_term(&lm.built, i, r, &var_names, false)
            )
        })
        .collect::<Vec<_>>()
        .join(" /\\ ");

    // Genuine `Var`-leaf dags: instantiate each side's Term over per-slot `Var` bindings. `Var`
    // leaves carry the interned base-name code; the one-sided-id collapse matches Maude's normalize.
    let bindings: Vec<DagId> = (0..vars.count())
        .map(|k| {
            let name = i.intern(vars.name(k)).index();
            lm.built.engine.make_var(vars.sort(k), name, k)
        })
        .collect();
    let mut equations: Vec<(DagId, DagId)> = Vec::new();
    for (l, r) in &pairs {
        let ld = lm.built.engine.instantiate_bindings(l, &bindings);
        let ld = collapse_one_sided(&mut lm.built.engine, &lm.built.one_sided_id, ld);
        let ld = lm.built.engine.normalize_for_unify(ld);
        let rd = lm.built.engine.instantiate_bindings(r, &bindings);
        let rd = collapse_one_sided(&mut lm.built.engine, &lm.built.one_sided_id, rd);
        let rd = lm.built.engine.normalize_for_unify(rd);
        equations.push((ld, rd));
    }

    let specs: Vec<VarSpec> = (0..vars.count())
        .map(|k| VarSpec { sort: vars.sort(k), name: i.intern(vars.name(k)).index() })
        .collect();

    // The object-level command uses the `#` family starting at 0 (metaUnify supplies its own base).
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv { e: &mut lm.built.engine, names: &mut names };
    let problem = UnifyProblem::new(&mut env, equations, specs, VariableFamily::Unify, 0);

    Ok(UnifyCommand { echo, var_names, names_ok, problem })
}

/// Render one unifier's substitution (`name --> value` lines, or `empty substitution`), matching
/// `UserLevelRewritingContext::printSubstitution`.
pub fn render_unifier(
    m: &BuiltModule,
    i: &Interner,
    var_names: &[String],
    values: &[DagId],
) -> String {
    if values.is_empty() {
        return "empty substitution".to_string();
    }
    values
        .iter()
        .enumerate()
        .map(|(k, &v)| format!("{} --> {}", var_names[k], print_pretty(m, i, v, false)))
        .collect::<Vec<_>>()
        .join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One expected command result, transcribed from the reference binary:
    /// `~/Downloads/Maude-3/maude -no-banner conformance/<file>.maude < /dev/null`.
    enum Expect {
        /// A `reduce`: `(result-sort, an expected-term in surface syntax, rewrite-count)`. The expected
        /// term is reduced through the same pipeline and compared by `deep_equal`, so its surface form
        /// just has to denote the same value (e.g. `- 3` for the binary's `-3`, `s s 0` for `s_^2(0)`).
        Reduce { sort: &'static str, term: &'static str, rewrites: u64 },
        /// A `match`/`xmatch`: the expected solution blocks (each the `Var --> value` lines, or for
        /// `xmatch` the `Matched portion = …` line + substitution), rendered by [`render_solution`].
        /// Compared **as a set** (both sides sorted): the binary's exact ACU/AU solution *order* is
        /// Maude's Diophantine order, a deferred B1 follow-up — we reproduce every solution and its
        /// bindings, only the order may differ (CUI's two pairings happen to match order too).
        Match(&'static [&'static str]),
    }

    const fn e(sort: &'static str, term: &'static str, rewrites: u64) -> Expect {
        Expect::Reduce { sort, term, rewrites }
    }

    const fn mat(blocks: &'static [&'static str]) -> Expect {
        Expect::Match(blocks)
    }

    /// A command's tokens, owned so the loop can `&mut`-borrow `loaded.modules` while iterating.
    enum Cmd {
        Reduce(Vec<Token>),
        Match { pattern: Vec<Token>, subject: Vec<Token>, xmatch: bool },
    }

    /// Load `src` and assert each command matches the reference binary: a `reduce`'s result sort, rewrite
    /// count, and value (via reducing the expected term through the same pipeline); a `match`/`xmatch`'s
    /// solution set (rendered blocks, sorted — see [`Expect::Match`]).
    fn conform(src: &str, expected: &[Expect]) {
        let mut loaded = load_source(src).expect("load source");
        let cmds: Vec<(usize, Cmd)> = loaded
            .commands
            .iter()
            .map(|(m, c)| {
                let cmd = match c {
                    Command::Reduce { term, .. } => Cmd::Reduce(term.clone()),
                    Command::Match { pattern, subject, xmatch, .. } => Cmd::Match {
                        pattern: pattern.clone(),
                        subject: subject.clone(),
                        xmatch: *xmatch,
                    },
                    _ => panic!("this conformance harness covers only reduce/match"),
                };
                (*m, cmd)
            })
            .collect();
        assert_eq!(cmds.len(), expected.len(), "command count");

        for (idx, ((m, cmd), exp)) in cmds.iter().zip(expected).enumerate() {
            match (cmd, exp) {
                (Cmd::Reduce(term), Expect::Reduce { sort, term: eterm, rewrites }) => {
                    let (got, rw) = reduce_command(&mut loaded.modules[*m], &loaded.interner, term)
                        .unwrap_or_else(|err| panic!("command {idx}: {err}"));
                    {
                        let eng = &loaded.modules[*m].built.engine;
                        assert_eq!(eng.sorts().name(eng.sort_of(got)), *sort, "command {idx} sort");
                    }
                    assert_eq!(rw, *rewrites, "command {idx} rewrite count");

                    let exp_toks = tokenize(eterm, &mut loaded.interner);
                    let (want, _) = reduce_command(&mut loaded.modules[*m], &loaded.interner, &exp_toks)
                        .unwrap_or_else(|err| panic!("command {idx} expected `{eterm}`: {err}"));
                    let eng = &loaded.modules[*m].built.engine;
                    assert!(eng.deep_equal(got, want), "command {idx} value: expected `{eterm}`");
                }
                (Cmd::Match { pattern, subject, xmatch }, Expect::Match(blocks)) => {
                    let mut got =
                        match_command(&mut loaded.modules[*m], &loaded.interner, pattern, subject, *xmatch)
                            .unwrap_or_else(|err| panic!("command {idx}: {err}"));
                    got.sort();
                    let mut want: Vec<String> = blocks.iter().map(|s| (*s).to_string()).collect();
                    want.sort();
                    assert_eq!(got, want, "command {idx} match solution set");
                }
                _ => panic!("command {idx}: command kind does not match its expectation"),
            }
        }
    }

    macro_rules! conformance_file {
        ($name:expr) => {
            include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../conformance/", $name))
        };
    }

    #[test]
    fn iter_conforms() {
        conform(
            conformance_file!("iter.maude"),
            &[
                e("Zero", "0", 0),
                e("NzNat", "s 0", 0),
                e("NzNat", "s 0", 2),
                e("NzNat", "s 0", 2), // ITER-VAR
                e("NzNat", "s 0", 1),
            ],
        );
    }

    #[test]
    fn bool_conforms() {
        conform(
            conformance_file!("bool.maude"),
            &[
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
                e("Truth", "tt", 1),
                e("Zero", "0", 1),
                e("NzNat", "s s 0", 2),
                e("Zero", "0", 1),
            ],
        );
    }

    #[test]
    fn nat_conforms() {
        conform(
            conformance_file!("nat.maude"),
            &[
                e("NzNat", "5", 1),
                e("NzNat", "4", 1),
                e("NzNat", "5", 1),
                e("NzNat", "12", 1),
                e("NzNat", "4", 1),
                e("NzNat", "3", 1),
                e("NzNat", "1", 1),
                e("NzNat", "1024", 1),
                e("NzNat", "6", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
                e("Truth", "tt", 1),
                e("NzNat", "x + 5", 1),
            ],
        );
    }

    #[test]
    fn int_conforms() {
        conform(
            conformance_file!("int.maude"),
            &[
                e("NzInt", "- 3", 0),
                e("NzNat", "3", 1),
                e("Zero", "0", 1),
                e("NzInt", "- 3", 1),
                e("NzInt", "- 5", 1),
                e("NzInt", "- 3", 1),
                e("NzNat", "3", 1),
                e("NzInt", "- 6", 1),
                e("NzNat", "6", 1),
                e("NzInt", "- 3", 1),
                e("NzInt", "- 1", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
            ],
        );
    }

    // ---- B4.5a: broaden the differential harness to the currently-loadable conformance modules ----

    #[test]
    fn peano_conforms() {
        conform(
            conformance_file!("peano.maude"),
            &[e("Nat", "s s s s 0", 3), e("Nat", "s s s s s s s s s s s s 0", 21)],
        );
    }

    #[test]
    fn strat_conforms() {
        conform(
            conformance_file!("strat.maude"),
            &[e("Nat", "s s z", 1), e("Nat", "z", 1), e("Nat", "z", 1), e("Nat", "s s z", 2)],
        );
    }

    /// Phase 1.5 / C8 — AC matching with "alien" (non-ground non-variable) subterms. `eq s M + N = s
    /// (M + N)` over a commutative `+` matches the alien `s M` recursively; Maude's greedy matcher binds
    /// it to the canonically-smallest element, fixing the rewrite count deterministically. Was a panic
    /// (acu.rs:64). Counts (2/3/3/4/4 and 8/13) are byte-identical to the reference binary.
    #[test]
    fn correctness_ac_alien_conforms() {
        conform(
            conformance_file!("correctness-ac-alien.maude"),
            &[
                e("Nat", "s s s z", 2),
                e("Nat", "s s s s s z", 3),
                e("Nat", "s s s z", 3),
                e("Nat", "s s s z", 4),
                e("Nat", "s s s s s s s z", 4),
                e("Nat", "s s s s s s z", 8),         // 2 * 3
                e("Nat", "s s s s s s s s s z", 13),  // 3 * 3
            ],
        );
    }

    /// Phase 1.5 / C8 — AU (associative, not commutative) alien subterms + non-linear variables. An
    /// alien `s M` under `__` matches one element recursively; a repeated var `X X` re-matches the same
    /// run. Was a panic (au.rs). Counts byte-identical to the reference; the leftmost-alien / maximal-
    /// collector order is Maude's greedy order (so reduce counts are deterministic).
    #[test]
    fn correctness_au_alien_conforms() {
        conform(
            conformance_file!("correctness-au-alien.maude"),
            &[
                e("E", "a b c", 2), // (s s a) b c — peel two successors off the head
                e("E", "a b c", 1), // a (s b) c   — interior successor untouched
                e("E", "a b c", 2), // (s a)(s b) c
                e("E", "a", 1),     // a a         — non-linear collapse
                e("E", "a", 2),     // a a a
                e("E", "s (a b) c", 1), // (s a)(s b) c — two aliens, leading pair + residue c
            ],
        );
    }

    /// Phase 1.5 / C8 — a theory-rooted subterm under a FREE operator (the cross-theory `Sequence`
    /// arm): `eq f(a X) = X` (AU arg) and `eq g(a ; X) = X` (AC arg). The free skeleton binds; the alien
    /// subterm is matched recursively. Was a panic (theory.rs:65). Byte-identical to the reference.
    #[test]
    fn correctness_free_alien_conforms() {
        conform(
            conformance_file!("correctness-free-alien.maude"),
            &[
                e("E", "b c", 1),       // f(a b c) — AU alien under free f
                e("E", "f(b c)", 0),    // f(b c)   — no match (head is not a)
                e("E", "b ; c", 1),     // g(a ; b ; c) — AC alien under free g
                e("E", "g(b ; c)", 0),  // g(b ; c)
                e("E", "c a", 1),       // h(a c, b a) — two aliens, one per argument
            ],
        );
    }

    /// Phase 1.5 / C8 — uniform cross-theory composition: a theory-rooted subterm under an `iter` (S)
    /// or `comm` (CUI) operator now matches modulo its theory (`s (a + X)`, `(a + X) ; Y`), via the same
    /// `enumerate_alien_solutions` seam as ACU/AU aliens and free-with-theory-children. Were panics.
    #[test]
    fn correctness_cross_theory_conforms() {
        conform(
            conformance_file!("correctness-cross-theory.maude"),
            &[
                e("Foo", "s (a + b)", 1), // membership lhs `s (a + X)` matches modulo AC under iter
                e("E", "b", 1),           // eq reduces s(a+a) before the membership (C1 lazy)
                e("E", "s (b + b)", 0),   // no leading a
                e("E", "b ; b", 1),       // AC term as a CUI argument
                e("E", "(b + b) ; a", 0), // no leading a in either pairing
            ],
        );
    }

    /// Phase 1.5 / C5 — membership axioms whose lhs is a theory term, matched modulo the theory. Since
    /// memberships compile to the same `LhsAutomaton` as equations, the C8 cross-theory matching covers
    /// their lhs: AC (non-linear `X + X`, alien `s M + N`), AU (`a L`, alien `(s M) L`), and iter/S
    /// (`s s s X`) membership lhs all match the reference. (Collapse-matching under an identity — Maude
    /// applying `mb a L` to collapsed sub-elements — is the separate deferred count-only gap.)
    #[test]
    fn correctness_membership_theory_conforms() {
        conform(
            conformance_file!("correctness-membership-theory.maude"),
            &[
                // AC-MB
                e("Sym", "a + a", 1),
                e("E", "a + b", 0),
                e("Pair", "s a + b", 1),   // alien membership lhs `s M + N` matches modulo AC
                e("Pair", "s a + s a", 1), // both apply; the tie-break picks Pair
                // AU-MB
                e("Lst", "a b c", 1),
                e("E", "b c", 0),
                e("Spec", "s a b c", 1),   // alien head `(s M) L` matches modulo AU
                // S-MB
                e("Zero", "0", 0),
                e("NzNat", "s s 0", 0),    // too few successors
                e("Big", "s s s 0", 1),    // iter/S membership lhs `s s s X`
                e("Big", "s s s s 0", 1),
            ],
        );
    }

    /// Phase 1.5 / C1 seam 3 — strat × membership. A custom `strat` leaves args unreduced, but Maude
    /// (and now we) still refine their TRUE SORT at the top step: the overloaded `wrap`'s result sort
    /// reflects the refined `mk(e):Sml` (→ WrS, not Wr), and `pick`'s discarded branch still has its
    /// membership counted (4 rewrites). Distinct subterms only — a repeated reducible-membership subterm
    /// was, at C1 time, the separate subject-DAG-sharing divergence (C7, since resolved; see `fable-audit.md`).
    #[test]
    fn correctness_strat_mb_conforms() {
        conform(
            conformance_file!("correctness-strat-mb.maude"),
            &[
                e("WrS", "wrap(mk(e))", 1), // skipped arg refined → overloaded range WrS
                e("Sml", "mkA", 4),         // both branches refined before selection; discarded one counts
            ],
        );
    }

    #[test]
    fn acu_overload_conforms() {
        conform(
            conformance_file!("acu-overload.maude"),
            &[
                e("NzNat", "z + nz", 0),
                e("NzNat", "z + nz", 0),
                e("Nat", "z + z", 0),
                e("NzNat", "nz + nz", 0),
                e("NzNat", "z + z + nz", 0),
                e("NzNat", "g(z, nz)", 0),
                e("NzNat", "g(z, nz)", 0),
                e("Nat", "g(z, z)", 0),
            ],
        );
    }

    #[test]
    fn acu_reduce_conforms() {
        conform(
            conformance_file!("acu-reduce.maude"),
            &[
                e("N", "s 0 + s 0 + s 0", 1),
                e("E", "a + b", 1),
                e("E", "0 ; s 0", 2),
                e("E", "a", 3),
            ],
        );
    }

    #[test]
    fn membership_conforms() {
        conform(
            conformance_file!("membership.maude"),
            &[
                e("SymPair", "< z, z >", 1),
                e("Pair", "< z, s z >", 0),
                e("SymPair", "< s z, s z >", 1),
                e("Nat", "z", 2),
                e("Nat", "f(< z, s z >)", 0),
                e("A", "a", 0),
                e("B", "g(a)", 1),
                e("C", "g(g(a))", 2),
            ],
        );
    }

    /// Phase 1.5 / C1 — eager→lazy sort & membership computation. A membership on a *reducible* operator
    /// (one that also has equations) is applied only at the reduce normal-form point, so a redex an
    /// equation reduces away is never constrained: the counts are 1 / 2 / 1 (not the eager 2 / 3 / hang).
    /// The third command is a `cmb` with a divergent condition that Maude — and now we — never evaluate,
    /// because the equation reduces `g(a)` to `big` first (a *termination* fix, not just a count fix).
    #[test]
    fn correctness_mb_reducible_conforms() {
        conform(
            conformance_file!("correctness-mb-reducible.maude"),
            &[
                e("Big", "big", 1),  // MB-REDUCIBLE: eq g(a)=big fires; mb g(X):Small never reached
                e("S", "g(b)", 2),   // MB-REWRITE-CHAIN: g(a)→g(b) [1] then g(b)'s mb [2]
                e("Big", "big", 1),  // CMB-DIVERGENT: halts at big; the looping cmb condition is unreached
            ],
        );
    }

    /// C7 structure sharing: a repeated reducible subterm reduces once, matching Maude's hash-consed
    /// subject/rhs DAG. Counts are byte-identical to the reference binary (pre-C7 ours over-counted the
    /// duplicate); result + least sort were always faithful. Covers a subject duplicate, a deep shared
    /// chain, an rhs duplicate, a triple, a membership on a shared constant, and the AU/CUI/ACU theories.
    #[test]
    fn correctness_sharing_conforms() {
        conform(
            conformance_file!("correctness-sharing.maude"),
            &[
                e("P", "< b, b >", 1),       // FREE subject dup: two g(a) -> one node, reduced once
                e("P", "< c, c >", 2),       // deep shared chain g(g(a))->g(b)->c, once
                e("P", "< b, b >", 2),       // rhs dup: f(a) [1] + shared g(a) in rhs [2]
                e("P", "< b, b >", 2),       // triple subject dup: g(a) once [1] + h [2]
                e("P", "< mkA, mkA >", 1),   // mb on a shared constant: fires once
                e("L", "b b", 1),            // AU: two equal elements share, reduced once
                e("L", "b b b", 1),          // AU: three equal elements
                e("E", "b & b", 1),          // CUI: two equal elements share
                e("E", "b + b", 1),          // ACU: already merges to multiplicity 2 (unchanged by C7)
            ],
        );
    }

    #[test]
    fn overload_conforms() {
        // Command 8 is a kind-level (error-sort) result. C4: the kernel now names a kind after its MAXIMAL
        // sort (Maude's `printKind`), so this single-top component prints `[Nat]` byte-identically to the
        // reference (was `[Zero]` — the first-declared member). (overload.maude is the non-preregular module;
        // Maude also warns on preregularity, which we don't surface yet — B2.1's deferred diagnostics sink —
        // but the reduced results/sorts match.)
        conform(
            conformance_file!("overload.maude"),
            &[
                e("Zero", "0", 0),
                e("NzNat", "s 0", 0),
                e("NzNat", "s 0 + s 0", 0),
                e("Nat", "0 + s 0", 0),
                e("Nat", "0 + 0", 0),
                e("NzNat", "s s 0", 2),
                e("Zero", "0", 1),
                e("[Nat]", "0 + 0", 0),
                e("NzNat", "s 0 + s 0", 0),
                e("A", "f(c)", 0),
            ],
        );
    }

    // ---- B4.5b: built-in literals (string / qid / float) ----

    /// Like [`conform`], but checks the result's *printed* form (Maude-faithful, uncolored) against the
    /// binary's text — for modules whose results are literals best compared textually (no ACU residues,
    /// so no order/spacing caveats).
    fn conform_render(src: &str, expected: &[Expect]) {
        let mut loaded = load_source(src).expect("load source");
        let cmds: Vec<(usize, Vec<Token>)> = loaded
            .commands
            .iter()
            .map(|(m, c)| match c {
                Command::Reduce { term, .. } => (*m, term.clone()),
                _ => panic!("conform_render handles only reduce"),
            })
            .collect();
        assert_eq!(cmds.len(), expected.len(), "command count");
        for (idx, ((m, term), exp)) in cmds.iter().zip(expected).enumerate() {
            let Expect::Reduce { sort: esort, term: eterm, rewrites } = exp else {
                panic!("conform_render handles only reduce expectations");
            };
            let (got, rw) = reduce_command(&mut loaded.modules[*m], &loaded.interner, term)
                .unwrap_or_else(|err| panic!("command {idx}: {err}"));
            let built = &loaded.modules[*m].built;
            let sort = built.engine.sorts().name(built.engine.sort_of(got)).to_string();
            assert_eq!(sort, *esort, "command {idx} sort");
            assert_eq!(rw, *rewrites, "command {idx} rewrites");
            let printed = crate::pretty::print_pretty(built, &loaded.interner, got, false);
            assert_eq!(printed, *eterm, "command {idx} printed value");
        }
    }

    #[test]
    fn float_conforms() {
        conform_render(
            conformance_file!("float.maude"),
            &[
                e("Flt", "4.0", 1),
                e("Flt", "3.5", 1),
                e("Flt", "6.0", 1),
                e("Flt", "3.5", 1),
                e("Flt", "-1.5", 1),
                e("Flt", "3.0", 2),
                e("Flt", "2.0", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
            ],
        );
    }

    /// C9: floats print via Maude's `doubleToString` — the normalized scientific form (`1.0e+4`,
    /// `2.5e-1`), the 17-significant-digit rounding of 0.1, and a long non-scientific mantissa. `float.maude`
    /// only used format-coincident values, so this fixture is what pins the printer against the binary.
    #[test]
    fn float_print_conforms() {
        conform_render(
            conformance_file!("correctness-float-print.maude"),
            &[
                e("Flt", "3.3333333333333331e-1", 1),
                e("Flt", "1.0e+4", 1),
                e("Flt", "2.5e-1", 0),
                e("Flt", "1.0000000000000001e-1", 0),
                e("Flt", "1.0e+3", 0),
                e("Flt", "1.0e-3", 0),
                e("Flt", "1.0e+1", 0),
                e("Flt", "5.0e-1", 0),
                e("Flt", "1.0e+16", 0),
                e("Flt", "1.23456789e+5", 0),
                e("Flt", "1.0", 0),
                e("Flt", "1.4142135623730951", 1),
            ],
        );
    }

    /// C10: a `-` glued to digits (`-7`) lexes as one `SMALL_NEG` token and parses via the `-_` minus op
    /// (`MAKE_INTEGER`), exactly as a spaced `- 7` — so `-7 quo 2`, `3 + -7`, `5 - -7` all parse and reduce.
    /// (The lexer-level `5 -7` rejection — matching the binary — is pinned in `lex::tests`.)
    #[test]
    fn glued_minus_conforms() {
        conform_render(
            conformance_file!("correctness-glued-minus.maude"),
            &[
                e("NzInt", "-3", 0),
                e("NzInt", "-7", 0),
                e("NzInt", "-3", 1),
                e("NzInt", "-4", 1),
                e("NzInt", "-1", 1),
                e("NzNat", "12", 1),
                e("NzNat", "6", 1),
                e("Truth", "tt", 1),
            ],
        );
    }

    /// C3: order-dependent equation + membership application matches the reference binary. The
    /// first-*declared* matching equation fires (declaration order, not specificity — `f(a)` → `b` when
    /// `eq f(a)=b` is first, `c` when `eq f(X)=c` is first); a non-confluent `eq a=b . eq a=c` → `b`;
    /// comparable membership targets apply smallest-sort-first (1 rewrite, no double count); a conditional
    /// fallback takes the first whose condition holds. (The incomparable-membership tiebreak and
    /// repeated-subterm sharing are separate documented residuals — doc 09 C3 / C7.)
    #[test]
    fn eq_mb_order_conforms() {
        conform_render(
            conformance_file!("correctness-eq-mb-order.maude"),
            &[
                e("S", "b", 1),
                e("S", "c", 1),
                e("S", "c", 1),
                e("S", "b", 1),
                e("A", "x", 1),
                e("S", "b", 1),
                e("S", "c", 1),
            ],
        );
    }

    #[test]
    fn string_conforms() {
        conform_render(
            conformance_file!("string.maude"),
            &[
                e("Str", "\"abcd\"", 1),
                e("NzNat", "5", 1),
                e("Zero", "0", 1),
                e("Str", "\"ell\"", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
            ],
        );
    }

    /// C11: a rational special constant prints compactly as `num/den` (Maude's `handleDivision`), so this
    /// now checks the printed text (was value-only `conform` while we printed the generic `3 / 4`). A
    /// `0/N` is *not* a rational — `0` is the `Zero` constant, not a numeral — so it stays spaced (`0 / 5`).
    #[test]
    fn rat_conforms() {
        conform_render(
            conformance_file!("rat.maude"),
            &[
                e("NzNat", "2", 1),
                e("NzRat", "3/4", 1),
                e("NzRat", "3/2", 1),
                e("NzRat", "-3/2", 1),
                e("NzNat", "5", 1),
                e("NzRat", "3/4", 0),
                e("Rat", "0 / 5", 0),
            ],
        );
    }

    // ---- B4.5c: conditional statements (ceq / cmb / owise-with-condition / := / sort-test) ----

    #[test]
    fn conditional_conforms() {
        conform(
            conformance_file!("conditional.maude"),
            &[
                e("Nat", "s s z", 3),
                e("Nat", "s s z", 5),
                e("Nat", "z", 2),
                e("NzNat", "s z", 1),
                e("Nat", "nz?(z)", 0),
            ],
        );
    }

    #[test]
    fn owise_conforms() {
        conform(
            conformance_file!("owise.maude"),
            &[
                e("Truth", "tt", 1),
                e("Truth", "ff", 1),
                e("Truth", "ff", 1),
                e("Nat", "z", 2),
                e("Nat", "z", 3),
                e("Nat", "s z", 3),
            ],
        );
    }

    #[test]
    fn match_cond_conforms() {
        conform(
            conformance_file!("match-cond.maude"),
            &[
                e("Nat", "s z", 1),
                e("Nat", "z", 1),
                e("Nat", "pred(z)", 0),
                e("Nat", "s z", 2),
                e("Nat", "s s z", 2),
            ],
        );
    }

    #[test]
    fn cmb_conforms() {
        conform(
            conformance_file!("cmb.maude"),
            &[
                e("GoodPair", "< z, s z >", 2),
                e("Pair", "< s z, z >", 1),
                e("GoodPair", "< z, z >", 2),
                e("GoodPair", "< s z, s z >", 3),
            ],
        );
    }

    /// B4.5d: the `match`/`xmatch` command end-to-end through the public kernel solution stream. ACU
    /// matching with and without identity, and an extension `xmatch` reporting the matched portion — the
    /// strongest from-text exercise of the B1 matcher. Solution sets vs the reference binary (order is
    /// Maude's deferred Diophantine order; see [`Expect::Match`]).
    #[test]
    fn acu_match_conforms() {
        conform(
            conformance_file!("acu-match.maude"),
            &[
                // match X + Y <=? a + b + c  — six splits into two non-empty parts.
                mat(&[
                    "X --> a\nY --> b + c",
                    "X --> b\nY --> a + c",
                    "X --> c\nY --> a + b",
                    "X --> a + b\nY --> c",
                    "X --> a + c\nY --> b",
                    "X --> b + c\nY --> a",
                ]),
                // match X # Y <=? a # b  — four, including a variable binding the identity `e`.
                mat(&[
                    "X --> e\nY --> a # b",
                    "X --> a\nY --> b",
                    "X --> b\nY --> a",
                    "X --> a # b\nY --> e",
                ]),
                // xmatch a + b <=? a + b + c  — one extension match, residue c, empty substitution.
                mat(&["Matched portion = a + b\nempty substitution"]),
            ],
        );
    }

    /// The Maude `match` display layout: `No match.` when empty, else `Matcher N` headers with a blank
    /// line between blocks (the B5 REPL renderer over [`match_command`]'s blocks).
    #[test]
    fn format_matchers_layout() {
        assert_eq!(format_matchers(&[]), "No match.");
        assert_eq!(
            format_matchers(&["X --> a\nY --> b".to_string(), "X --> b\nY --> a".to_string()]),
            "Matcher 1\nX --> a\nY --> b\n\nMatcher 2\nX --> b\nY --> a"
        );
    }

    /// B4.5d: CUI `match` (the two commutative pairings) alongside the CUI reduce locks (matching modulo
    /// commutativity, and the idem/identity collapses at construction).
    #[test]
    fn cui_conforms() {
        conform(
            conformance_file!("cui.maude"),
            &[
                // match f(X, Y) <=? f(a, b)  — the two pairings.
                mat(&["X --> a\nY --> b", "X --> b\nY --> a"]),
                e("E", "c", 1), // red f(b, a)  — matching modulo comm
                e("E", "a", 0), // red g(a, a)  — idempotence collapses at construction
                e("E", "a", 0), // red h(a, e)  — identity collapses at construction
            ],
        );
    }

    /// B4.5e: `__` juxtaposition (`op __ : E E -> E [assoc]`, the empty-syntax production `E ::= E E`).
    /// The `[assoc]` right-associating gather `(e E)` disambiguates the otherwise-ambiguous adjacent
    /// nonterminals; the kernel then flattens the parse modulo associativity. AU `match` (ordered
    /// prefix/suffix splits incl. the identity `nil`) + the two AU reduce locks (extension on both ends;
    /// the lone variable absorbing the ordered tail).
    #[test]
    fn au_conforms() {
        conform(
            conformance_file!("au.maude"),
            &[
                // match X Y <=? a b c  — four ordered splits, including nil via the identity.
                mat(&[
                    "X --> nil\nY --> a b c",
                    "X --> a\nY --> b c",
                    "X --> a b\nY --> c",
                    "X --> a b c\nY --> nil",
                ]),
                e("E", "d a d", 1), // red d b c d  — `b c` rewrites to `a` in place (extension both ends)
                e("E", "b", 1),     // red a c c    — lone var absorbs the tail (`a X = b`)
            ],
        );
    }

    /// The whole-conformance-suite differential gate (B4.5e, the last B4 deliverable). EVERY conformance
    /// module loads, EVERY command runs, and every reduced result **round-trips** (`parse∘print_raw =
    /// id`). The per-module `*_conforms` tests pin exact sorts / counts / values against the reference
    /// binary; this sweep is the breadth guarantee — parser and pretty-printer stay mutually consistent
    /// across the *entire* suite — and the explicit list is the coverage guard: a new `conformance/*.maude`
    /// must be added here, so nothing silently drops out of coverage.
    #[test]
    fn whole_conformance_suite() {
        use crate::pretty::print_raw;
        // (name, source, round_trip). `fib` is the throughput fixture — its result is a 17711-deep
        // successor chain, so we run+count it but skip the (correct, but O(n)-token) round-trip reparse;
        // `peano` round-trips the same Peano-Fibonacci theory at a small numeral.
        let modules: &[(&str, &str, bool)] = &[
            ("acu-match", conformance_file!("acu-match.maude"), true),
            ("acu-overload", conformance_file!("acu-overload.maude"), true),
            ("acu-reduce", conformance_file!("acu-reduce.maude"), true),
            ("au", conformance_file!("au.maude"), true),
            ("bool", conformance_file!("bool.maude"), true),
            ("cmb", conformance_file!("cmb.maude"), true),
            ("conditional", conformance_file!("conditional.maude"), true),
            ("cui", conformance_file!("cui.maude"), true),
            ("fib", conformance_file!("fib.maude"), false),
            ("float", conformance_file!("float.maude"), true),
            ("int", conformance_file!("int.maude"), true),
            ("iter", conformance_file!("iter.maude"), true),
            ("match-cond", conformance_file!("match-cond.maude"), true),
            ("membership", conformance_file!("membership.maude"), true),
            ("nat", conformance_file!("nat.maude"), true),
            ("overload", conformance_file!("overload.maude"), true),
            ("owise", conformance_file!("owise.maude"), true),
            ("peano", conformance_file!("peano.maude"), true),
            ("rat", conformance_file!("rat.maude"), true),
            ("strat", conformance_file!("strat.maude"), true),
            ("string", conformance_file!("string.maude"), true),
        ];
        for &(name, src, round_trip) in modules {
            let mut loaded = load_source(src).unwrap_or_else(|e| panic!("{name}: load: {e}"));
            let cmds: Vec<(usize, Cmd)> = loaded
                .commands
                .iter()
                .map(|(m, c)| {
                    let cmd = match c {
                        Command::Reduce { term, .. } => Cmd::Reduce(term.clone()),
                        Command::Match { pattern, subject, xmatch, .. } => Cmd::Match {
                            pattern: pattern.clone(),
                            subject: subject.clone(),
                            xmatch: *xmatch,
                        },
                        _ => panic!("this conformance harness covers only reduce/match"),
                    };
                    (*m, cmd)
                })
                .collect();
            assert!(!cmds.is_empty(), "{name}: no commands parsed");
            for (idx, (m, cmd)) in cmds.iter().enumerate() {
                match cmd {
                    Cmd::Reduce(term) => {
                        let (result, _) = reduce_command(&mut loaded.modules[*m], &loaded.interner, term)
                            .unwrap_or_else(|e| panic!("{name} cmd {idx}: reduce: {e}"));
                        if round_trip {
                            let printed = print_raw(&loaded.modules[*m].built, &loaded.interner, result);
                            let toks = tokenize(&printed, &mut loaded.interner);
                            let (reparsed, _) =
                                reduce_command(&mut loaded.modules[*m], &loaded.interner, &toks)
                                    .unwrap_or_else(|e| panic!("{name} cmd {idx} reparse `{printed}`: {e}"));
                            let eng = &loaded.modules[*m].built.engine;
                            assert!(
                                eng.deep_equal(result, reparsed),
                                "{name} cmd {idx}: `{printed}` did not round-trip"
                            );
                        }
                    }
                    Cmd::Match { pattern, subject, xmatch } => {
                        match_command(&mut loaded.modules[*m], &loaded.interner, pattern, subject, *xmatch)
                            .unwrap_or_else(|e| panic!("{name} cmd {idx}: match: {e}"));
                    }
                }
            }
        }
    }
}
