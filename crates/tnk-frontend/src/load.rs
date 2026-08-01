//! Loading: drive a whole `.maude` source end-to-end. Surface-parse it, then for each module build the
//! signature ([`build_module`]), the mixfix grammar ([`build_grammar`]), and add its parsed statements;
//! commands are run against the module they follow (Maude's current module). The B4.4c entry point and
//! the basis for the B5 REPL.
//!
//! Scope: unconditional and conditional `eq`/`mb` (`ceq`/`cmb`/condition fragments/`owise`, B4.5c) and
//! the `reduce` (B4.4c) and `match`/`xmatch` (B4.5d, via [`match_command`]) commands. The `match`
//! command drives the kernel's public multi-solution stream (`Engine::match_solutions`). Still open in
//! B4.5: `__` juxtaposition (B4.5e, blocks `au`) and the whole-prelude differential test.

use crate::build_term::{VarIndex, build_dag, build_logic_dag, build_term};
use crate::cfparser::compile::CompiledGrammar;
use crate::cfparser::forest::PTree;
use crate::cfparser::{ParseEffort, earley, forest};
use crate::grammar::build::build_grammar;
use crate::grammar::{Action, GSym, Nt, NtType, Terminal};
use crate::lex::{Frag, Interner, TokKind, Token, tokenize};
use crate::oo_complete;
use crate::pretty::{print_pretty, print_pretty_with_variables, print_term};
use crate::sig::build_sig::build_module;
use crate::sig::syntax::{BuiltModule, EqTrace, MbTrace, RlTrace};
use crate::surface::ast::{Command, Diagnostic, PreModule, SearchArrow, Source, Statement};
use crate::surface::parser::Parser;
use std::borrow::Cow;
use std::collections::{BTreeSet, HashMap};
use tnk_core::dag::DagId;
use tnk_core::engine::MatchedPortion;
use tnk_core::rewrite::Rewriting;
use tnk_core::search::{Arrow, Search};
use tnk_core::smt_search::SmtSearch;
use tnk_core::sort::{KindId, SortId};
use tnk_core::symbol::SymbolId;
use tnk_core::term::{ConditionFragment, Equation, Membership, Term};
use tnk_core::variant::{
    VariantEquation, VariantMode, VariantSearch, compile_variant_equation, term_from_dag_slots,
};

/// A fully loaded module: its kernel state (signature + statements) and its mixfix grammar (for parsing
/// command/REPL terms).
pub struct LoadedModule {
    pub built: BuiltModule,
    pub grammar: CompiledGrammar,
    /// Nonfatal parse/build diagnostics, rendered only by the owning Session.
    pub diagnostics: Vec<Diagnostic>,
    /// Imported strategy-definition home grammars, with semantic actions remapped to `built`. A strategy
    /// definition carrying a distinct `home` is executable only when this map contains that home.
    pub strategy_grammars: HashMap<String, CompiledGrammar>,
    /// Maude's module-wide `validForSMT_Rewriting` result.
    pub smt_rewrite_valid: bool,
}

/// Dense engine-trace slot produced by one source statement. The surrounding `Option` used by the
/// homed loader is `None` for a non-executable or rejected statement, preserving source alignment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatementTraceRef {
    Membership(usize),
    Equation(usize),
    Rule(usize),
}

impl LoadedModule {
    /// Recompute Maude's module-wide SMT-rewrite eligibility after callers install statements
    /// directly into the built engine (the reflected-module path does this post-build).
    pub fn refresh_smt_rewrite_valid(&mut self, pm: &PreModule) {
        self.smt_rewrite_valid =
            self.built.engine.valid_for_smt_rewriting() && !has_regular_collapse_axiom(pm);
    }
}

fn has_regular_collapse_axiom(pm: &PreModule) -> bool {
    pm.ops
        .iter()
        .any(|op| op.attrs.poly.is_none() && (op.attrs.idem || op.attrs.id.is_some()))
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
pub fn build_loaded_module(
    pm: &PreModule,
    interner: &mut Interner,
) -> Result<LoadedModule, String> {
    let mut built = build_module(pm, interner)?;
    let grammar = CompiledGrammar::compile(&build_grammar(&built, interner));
    install_identities(&mut built, &grammar, interner)?;
    let diagnostics = load_statements(pm, &mut built, &grammar, interner)?;
    let smt_rewrite_valid =
        built.engine.valid_for_smt_rewriting() && !has_regular_collapse_axiom(pm);
    Ok(LoadedModule {
        built,
        grammar,
        diagnostics,
        strategy_grammars: HashMap::new(),
        smt_rewrite_valid,
    })
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
    build_loaded_module_homed_traced(pm, homes, home_mod, interner).map(|(loaded, _)| loaded)
}

/// The homed build plus a source-aligned map to the dense executable trace vectors. Reflection needs
/// this map because Maude drops an individually rejected statement while keeping the surrounding module;
/// indexing the dense vectors by source position would then shift every following axiom.
pub fn build_loaded_module_homed_traced<'m>(
    pm: &PreModule,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    interner: &mut Interner,
) -> Result<(LoadedModule, Vec<Option<StatementTraceRef>>), String> {
    let mut built = build_module(pm, interner)?;
    let grammar = CompiledGrammar::compile(&build_grammar(&built, interner));
    install_identities(&mut built, &grammar, interner)?;
    let (trace_refs, diagnostics) =
        load_statements_homed(pm, &mut built, &grammar, homes, home_mod, interner)?;
    let strategy_grammars = pm
        .strat_defs
        .iter()
        .filter_map(|def| def.home.as_deref())
        .filter(|home| *home != pm.name)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .filter_map(|home| {
            home_mod(home)
                .and_then(|module| remap_home_grammar(module, &built))
                .map(|grammar| (home.to_string(), grammar))
        })
        .collect();
    let smt_rewrite_valid =
        built.engine.valid_for_smt_rewriting() && !has_regular_collapse_axiom(pm);
    Ok((
        LoadedModule {
            built,
            grammar,
            diagnostics,
            strategy_grammars,
            smt_rewrite_valid,
        },
        trace_refs,
    ))
}

fn install_identities(
    built: &mut BuiltModule,
    grammar: &CompiledGrammar,
    interner: &Interner,
) -> Result<(), String> {
    let specs = std::mem::take(&mut built.identity_specs);
    for spec in specs {
        let mut vars = VarIndex::new();
        let kind = built.engine.sorts().kind_of(spec.sort);
        let tree = parse_forest_at(
            &spec.tokens,
            grammar,
            interner,
            Nt::Comp(kind, NtType::Term),
        )
        .map_err(|e| format!("bad identity term: {e}"))?;
        let term = build_term(&tree, grammar, built, &spec.tokens, interner, &mut vars)
            .map_err(|e| format!("bad identity term: {e}"))?;
        if vars.count() != 0 {
            return Err("identity term must be ground".to_string());
        }
        match spec.side {
            crate::surface::ast::IdSide::Both => built.engine.set_identity_term(spec.symbol, term),
            crate::surface::ast::IdSide::Left | crate::surface::ast::IdSide::Right => {
                built.engine.set_one_sided_identity_term(spec.symbol, term);
            }
        }
    }
    built.engine.prepare_identities();
    Ok(())
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
            kind_map
                .entry(hsorts.kind_of(hsort))
                .or_insert_with(|| fsorts.kind_of(fsort));
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
        let dom: Vec<KindId> = syn
            .domain
            .iter()
            .map(|&s| kind_map.get(&hsorts.kind_of(s)).copied())
            .collect::<Option<_>>()?;
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
            Action::MakeRational { division, minus } => Action::MakeRational {
                division: map_sym(division)?,
                minus: map_sym(minus)?,
            },
            Action::MakeSmtNumber { symbol, kind } => Action::MakeSmtNumber {
                symbol: map_sym(symbol)?,
                kind,
            },
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
    let Source {
        modules: pre,
        commands,
        ..
    } = Parser::new(&toks, &interner).parse_source()?;

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
    Ok(Loaded {
        interner,
        modules,
        commands,
    })
}

fn statement_kind(statement: &Statement) -> &'static str {
    match statement {
        Statement::Eq { .. } => "equation",
        Statement::Mb { .. } => "membership",
        Statement::Rule { .. } => "rule",
    }
}

fn statement_line(statement: &Statement) -> Option<u32> {
    match statement {
        Statement::Eq { lhs, rhs, cond, .. } | Statement::Rule { lhs, rhs, cond, .. } => lhs
            .first()
            .or_else(|| rhs.first())
            .or_else(|| cond.as_ref().and_then(|tokens| tokens.first())),
        Statement::Mb {
            lhs, sort, cond, ..
        } => lhs
            .first()
            .or_else(|| sort.first())
            .or_else(|| cond.as_ref().and_then(|tokens| tokens.first())),
    }
    .map(|token| token.line)
}

/// Parse + build + add each of the module's statement bubbles to the engine, all against the flattened
/// module's own grammar `g`. The import-free / meta / REPL-legacy entry (no home information); the module
/// system's [`build_loaded_module_homed`] adds the D1a per-statement home grammars on top.
fn load_statements(
    pm: &PreModule,
    m: &mut BuiltModule,
    g: &CompiledGrammar,
    i: &Interner,
) -> Result<Vec<Diagnostic>, String> {
    load_statements_homed(pm, m, g, &[], &|_| None, i).map(|(_, diagnostics)| diagnostics)
}

/// Parse + build + add each statement in its defining module's grammar. Imported statements are parsed
/// against their **home** grammar first, remapped onto the flattened module's symbol table by
/// [`remap_home_grammar`]. This preserves the sorts of home variables when an importer declares
/// same-named variables (a flattened parse can succeed while silently selecting the importer's
/// declaration). The flattened grammar remains the fallback when the home is unavailable or its remapped
/// grammar cannot parse the statement. `homes[k]` is the home-module name of `pm.statements[k]` (from
/// `flatten_with_homes`); `None` or the flattened module's own name selects the flattened grammar directly.
pub fn load_statements_homed<'m>(
    pm: &PreModule,
    m: &mut BuiltModule,
    g: &CompiledGrammar,
    homes: &[Option<String>],
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    i: &Interner,
) -> Result<(Vec<Option<StatementTraceRef>>, Vec<Diagnostic>), String> {
    // Object-pattern completion context (Pillar 2.5-E): resolved once for an `omod`'s flattened module
    // (the CONFIGURATION object constructor / AttributeSet symbol / class sorts). `None` for a non-object
    // module, or one with no object constructor in scope — completion then never runs.
    let oo = pm.is_object.then(|| m.engine.oo_info()).flatten();
    // Cache home-module grammars remapped onto this flattened module's symbols. Imported statements use
    // these first; `None` means the home is unavailable or cannot be remapped, so the flat grammar is used.
    let mut home_grammars: HashMap<String, Option<CompiledGrammar>> = HashMap::new();
    let mut trace_refs = Vec::with_capacity(pm.statements.len());
    let mut diagnostics = pm.diagnostics.clone();

    for (idx, stmt) in pm.statements.iter().enumerate() {
        // Ordinary nonexec equations/memberships are proof obligations. Rules still pass through:
        // `[nonexec narrowing]` feeds symbolic narrowing, and an SMT-capable module retains every rule
        // in its dedicated root-rewrite table without making it ordinarily executable.
        if stmt_is_nonexec(stmt) && !matches!(stmt, Statement::Rule { .. }) {
            trace_refs.push(None);
            continue;
        }
        let trace_ref = match stmt {
            Statement::Mb { .. } => StatementTraceRef::Membership(m.mb_traces.len()),
            Statement::Eq { .. } => StatementTraceRef::Equation(m.eq_traces.len()),
            Statement::Rule { .. } => StatementTraceRef::Rule(m.rl_traces.len()),
        };
        // Imported statements belong to their defining grammar. Trying the flattened grammar first is
        // unsafe even when it parses: importer declarations can shadow a home variable name and change
        // its sort without producing an error.
        if let Some(home) = homes.get(idx).and_then(|h| h.as_deref())
            && home != m.name
        {
            if !home_grammars.contains_key(home) {
                let remapped = home_mod(home).and_then(|lm| remap_home_grammar(lm, m));
                home_grammars.insert(home.to_string(), remapped);
            }
            if let Some(hg) = home_grammars.get(home).and_then(Option::as_ref)
                && let Ok(registered) = load_one_stmt(stmt, m, hg, true, false, &oo, i)
            {
                trace_refs.push(registered.then_some(trace_ref));
                continue;
            }
        }
        let own_statement = homes
            .get(idx)
            .and_then(|home| home.as_deref())
            .is_some_and(|home| home == m.name);
        // Home parsing was not applicable or failed. A statement whose flattened parse/build fails is
        // dropped with an owned diagnostic; nothing is registered before the last fallible check.
        match load_one_stmt(stmt, m, g, false, own_statement, &oo, i) {
            Ok(registered) => {
                trace_refs.push(registered.then_some(trace_ref));
            }
            Err(error) => {
                trace_refs.push(None);
                let home = homes
                    .get(idx)
                    .and_then(|home| home.as_deref())
                    .unwrap_or(&pm.name);
                let kind = statement_kind(stmt);
                diagnostics.push(Diagnostic::warning(
                    home,
                    statement_line(stmt),
                    kind,
                    format!("dropped {kind}: {error}"),
                ));
            }
        }
    }

    // Root statements precede imported statements in the flattened stream. Within each source module,
    // line order interleaves parser-time and build-time diagnostics deterministically.
    let mut source_order: HashMap<Option<String>, usize> = HashMap::new();
    for diagnostic in &diagnostics {
        let next = source_order.len();
        source_order
            .entry(diagnostic.module.clone())
            .or_insert(next);
    }
    diagnostics.sort_by_key(|diagnostic| {
        (
            source_order
                .get(&diagnostic.module)
                .copied()
                .unwrap_or(usize::MAX),
            diagnostic.line.unwrap_or(u32::MAX),
        )
    });
    Ok((trace_refs, diagnostics))
}

/// Normalize a symbolic statement term through the kernel's theory canonicalizer, then recover the
/// original variable slots for source-form rendering. Maude prints `[narrowing]` rules from normalized
/// `Term`s in `show path`, so AC/ACU arguments there follow canonical order rather than parser order.
fn normalize_trace_term(m: &mut BuiltModule, i: &Interner, vars: &VarIndex, term: &Term) -> Term {
    let bindings: Vec<_> = (0..vars.count())
        .map(|slot| {
            let source = vars.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            let name = i
                .get(base)
                .expect("statement variable name was interned by the lexer")
                .index();
            m.engine.make_var(vars.sort(slot), name, slot as u32)
        })
        .collect();
    let dag = m.engine.instantiate_bindings(term, &bindings);
    let dag = m.engine.normalize_for_unify(dag);
    term_from_dag_slots(&m.engine, dag)
}
/// Static AC normalization preserves the source positions of direct variables relative to nonvariables
/// until a genuine adjacent inversion forces a sort. The runtime DAG canonicalizer always sorts the
/// whole soup. Restore that observable partition while retaining the kernel's canonical order within
/// the variable and nonvariable groups (notably `M:Marking a c` versus `N' + M + K`).
fn restore_echo_variable_positions(m: &BuiltModule, source: &Term, normalized: Term) -> Term {
    fn source_soup<'a>(symbol: SymbolId, term: &'a Term, out: &mut Vec<&'a Term>) {
        if let Term::Op {
            symbol: child_symbol,
            args,
        } = term
            && *child_symbol == symbol
        {
            for arg in args {
                source_soup(symbol, arg, out);
            }
        } else {
            out.push(term);
        }
    }

    fn normalized_soup(symbol: SymbolId, term: Term, out: &mut Vec<Term>) {
        match term {
            Term::Op {
                symbol: child_symbol,
                args,
            } if child_symbol == symbol => {
                for arg in args {
                    normalized_soup(symbol, arg, out);
                }
            }
            term => out.push(term),
        }
    }
    fn source_shape(
        symbol: SymbolId,
        source: &Term,
        leaves: &mut std::vec::IntoIter<Term>,
    ) -> Term {
        if let Term::Op {
            symbol: child_symbol,
            args,
        } = source
            && *child_symbol == symbol
        {
            Term::op(
                symbol,
                args.iter()
                    .map(|arg| source_shape(symbol, arg, leaves))
                    .collect(),
            )
        } else {
            leaves.next().expect("associative source shape changed")
        }
    }

    match (source, normalized) {
        (
            Term::Op {
                symbol: source_symbol,
                args: direct_source_args,
            },
            Term::Op {
                symbol,
                args: direct_args,
            },
        ) if *source_symbol == symbol => {
            let mut flattened_source = Vec::new();
            let mut flattened = Vec::new();
            let blank_juxtaposition = m
                .syntax
                .get(&symbol)
                .is_some_and(|syntax| matches!(syntax.frags.as_slice(), [Frag::Hole, Frag::Hole]));
            let (source_args, args, restore_shape, left_fold_candidate) =
                if direct_source_args.len() == direct_args.len() {
                    (
                        direct_source_args.iter().collect::<Vec<_>>(),
                        direct_args,
                        false,
                        direct_source_args.len() > 2 && blank_juxtaposition,
                    )
                } else {
                    for arg in direct_source_args {
                        source_soup(symbol, arg, &mut flattened_source);
                    }
                    for arg in direct_args {
                        normalized_soup(symbol, arg, &mut flattened);
                    }
                    (flattened_source, flattened, true, blank_juxtaposition)
                };
            if source_args.len() != args.len() {
                return Term::op(symbol, args);
            }
            let left_fold = left_fold_candidate
                && source_args.len() > 2
                && source_args.iter().any(|arg| {
                    arg.top_symbol()
                        .and_then(|symbol| m.syntax.get(&symbol))
                        .is_some_and(|syntax| {
                            matches!(syntax.frags.first(), Some(Frag::Hole))
                                || matches!(syntax.frags.last(), Some(Frag::Hole))
                        })
                });
            let restore_shape = restore_shape && !left_fold;

            let mask: Vec<_> = source_args
                .iter()
                .map(|arg| matches!(arg, Term::Var(_)))
                .collect();
            let has_variables = mask.iter().any(|&is_variable| is_variable);
            let has_nonvariables = mask.iter().any(|&is_variable| !is_variable);
            let ordered = if has_variables && has_nonvariables {
                let (variables, nonvariables): (Vec<_>, Vec<_>) = args
                    .into_iter()
                    .partition(|arg| matches!(arg, Term::Var(_)));
                let mut variables = variables.into_iter();
                let mut nonvariables = nonvariables.into_iter();
                mask.into_iter()
                    .map(|is_variable| {
                        if is_variable {
                            variables.next().expect("variable partition length changed")
                        } else {
                            nonvariables
                                .next()
                                .expect("nonvariable partition length changed")
                        }
                    })
                    .collect()
            } else {
                args
            };
            let restored: Vec<_> = source_args
                .into_iter()
                .zip(ordered)
                .map(|(source, normalized)| restore_echo_variable_positions(m, source, normalized))
                .collect();
            if restore_shape {
                source_shape(symbol, source, &mut restored.into_iter())
            } else if left_fold {
                let mut restored = restored.into_iter();
                let mut term = restored.next().expect("associative term has no arguments");
                for arg in restored {
                    term = Term::op(symbol, vec![term, arg]);
                }
                term
            } else {
                Term::op(symbol, restored)
            }
        }
        (
            Term::Iter {
                symbol: source_symbol,
                count: source_count,
                arg: source_arg,
            },
            Term::Iter { symbol, count, arg },
        ) if *source_symbol == symbol && *source_count == count => Term::iter(
            symbol,
            count,
            restore_echo_variable_positions(m, source_arg, *arg),
        ),
        (_, normalized) => normalized,
    }
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
    record_oo_diagnostic: bool,
    oo: &Option<tnk_core::engine::OoInfo>,
    i: &Interner,
) -> Result<bool, String> {
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
        Statement::Eq {
            lhs,
            rhs,
            cond,
            owise,
            variant,
            label,
            ..
        } => {
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
            let oo_source = (record_oo_diagnostic && oo.is_some()).then(|| {
                let source_count = vars.count();
                let names = oo_variable_names(m, &vars, source_count);
                (
                    render_oo_equation(m, i, &lhs_t, &rhs_t, &condition, &names, *owise, label),
                    source_count,
                )
            });
            let oo_completed = oo.as_ref().is_some_and(|info| {
                oo_complete::complete_statement(
                    info,
                    m,
                    &mut vars,
                    &mut lhs_t,
                    Some(&mut rhs_t),
                    &mut condition,
                )
            });
            if oo_completed && let Some((source, source_count)) = oo_source {
                let names = oo_variable_names(m, &vars, source_count);
                let transformed =
                    render_oo_equation(m, i, &lhs_t, &rhs_t, &condition, &names, *owise, label);
                push_oo_diagnostic(m, "equation", source, transformed);
            }
            let nr = vars.count();
            // Capture the source-form trace metadata before the Terms are moved into the kernel; the
            // kernel returns the dense equation id, which must index `eq_traces` (asserted).
            reject_rewrite_fragment(&condition, "equation")?;
            if !statement_vars_bound(&lhs_t, &condition, Some(&rhs_t)) {
                return Err("unbound variable in equation right-hand side or condition".to_string());
            }
            let trace = EqTrace {
                lhs: lhs_t.clone(),
                rhs: rhs_t.clone(),
                condition: condition.clone(),
                var_names: (0..nr).map(|k| vars.name(k).to_string()).collect(),
                owise: *owise,
                variant: *variant,
                label: label.clone(),
                nonexec: false, // engine-registered ⇒ executable
            };
            let id = if *variant {
                m.engine
                    .add_variant_equation(lhs_t, rhs_t, nr, condition, *owise)
            } else if *owise {
                m.engine.add_owise_equation(lhs_t, rhs_t, nr, condition)
            } else if condition.is_empty() {
                m.engine.add_equation(Equation {
                    lhs: lhs_t,
                    rhs: rhs_t,
                    nr_vars: nr,
                })
            } else {
                m.engine
                    .add_conditional_equation(lhs_t, rhs_t, nr, condition)
            };
            assert_eq!(
                id as usize,
                m.eq_traces.len(),
                "equation id is the dense eq_traces index"
            );
            m.eq_traces.push(trace);
            return Ok(true);
        }
        Statement::Mb {
            lhs,
            sort,
            cond,
            label,
            ..
        } => {
            let mut vars = VarIndex::new();
            let mut lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
            let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
            let sort_id = resolve_sort(sort, m, i)?;
            let mut condition = match cond {
                Some(c) => parse_condition(c, g, m, i, &mut vars, &mut bound)?,
                None => Vec::new(),
            };
            let oo_source = (record_oo_diagnostic && oo.is_some()).then(|| {
                let source_count = vars.count();
                let names = oo_variable_names(m, &vars, source_count);
                (
                    render_oo_membership(m, i, &lhs_t, sort_id, &condition, &names, label),
                    source_count,
                )
            });
            let oo_completed = oo.as_ref().is_some_and(|info| {
                oo_complete::complete_statement(
                    info,
                    m,
                    &mut vars,
                    &mut lhs_t,
                    None,
                    &mut condition,
                )
            });
            if oo_completed && let Some((source, source_count)) = oo_source {
                let names = oo_variable_names(m, &vars, source_count);
                let transformed =
                    render_oo_membership(m, i, &lhs_t, sort_id, &condition, &names, label);
                push_oo_diagnostic(m, "membership axiom", source, transformed);
            }
            let nr = vars.count();
            reject_rewrite_fragment(&condition, "membership")?;
            if !statement_vars_bound(&lhs_t, &condition, None) {
                return Err("unbound variable in membership condition".to_string());
            }
            if lhs_t.top_symbol().is_none() {
                return Err("membership left-hand side is a variable".to_string());
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
                m.engine.add_membership(Membership {
                    lhs: lhs_t,
                    sort: sort_id,
                    nr_vars: nr,
                })
            } else {
                m.engine
                    .add_conditional_membership(lhs_t, sort_id, nr, condition)
            };
            assert_eq!(
                id as usize,
                m.mb_traces.len(),
                "membership id is the dense mb_traces index"
            );
            m.mb_traces.push(trace);
            return Ok(true);
        }
        Statement::Rule {
            label,
            lhs,
            rhs,
            cond,
            nonexec,
            narrowing,
        } => {
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
            let oo_source = (record_oo_diagnostic && oo.is_some()).then(|| {
                let source_count = vars.count();
                let names = oo_variable_names(m, &vars, source_count);
                (
                    render_oo_rule(m, i, &lhs_t, &rhs_t, &condition, &names, label, *narrowing),
                    source_count,
                )
            });
            let oo_completed = oo.as_ref().is_some_and(|info| {
                oo_complete::complete_statement(
                    info,
                    m,
                    &mut vars,
                    &mut lhs_t,
                    Some(&mut rhs_t),
                    &mut condition,
                )
            });
            if oo_completed && let Some((source, source_count)) = oo_source {
                let names = oo_variable_names(m, &vars, source_count);
                let transformed =
                    render_oo_rule(m, i, &lhs_t, &rhs_t, &condition, &names, label, *narrowing);
                push_oo_diagnostic(m, "rule", source, transformed);
            }
            let nr = vars.count();
            let variable_names: Vec<String> =
                (0..nr).map(|slot| vars.name(slot).to_string()).collect();
            let variable_specs = if *narrowing {
                (0..nr)
                    .map(|slot| {
                        let source = vars.name(slot);
                        let base = source.split_once(':').map_or(source, |(base, _)| base);
                        let code = i.get(base).map_or(slot, |symbol| symbol.index());
                        tnk_core::unify::problem::VarSpec {
                            sort: vars.sort(slot),
                            name: maude_variable_name_rank(base, code),
                        }
                    })
                    .collect()
            } else {
                Vec::new()
            };
            // Maude rejects conditions on `[narrowing]` rules.
            if *narrowing && !condition.is_empty() {
                return Err("a narrowing rule cannot have a condition".to_string());
            }
            if !statement_vars_bound(&lhs_t, &condition, Some(&rhs_t)) && !*nonexec {
                return Err("unbound variable in rule right-hand side or condition".to_string());
            }
            if lhs_t.top_symbol().is_none() && !(*nonexec || *narrowing) {
                return Err("rule left-hand side is a variable".to_string());
            }
            m.engine.add_smt_rule(
                lhs_t.clone(),
                rhs_t.clone(),
                (0..nr).map(|slot| vars.sort(slot)).collect(),
                variable_names.clone(),
                condition.clone(),
            );
            if *narrowing {
                m.engine.add_narrowing_rule(
                    lhs_t.clone(),
                    rhs_t.clone(),
                    variable_specs,
                    variable_names.clone(),
                    condition.clone(),
                    label.clone(),
                    *nonexec,
                );
            }
            // A nonexec or bare-lhs narrowing rule exists only in the symbolic descriptor table.
            if *nonexec || lhs_t.top_symbol().is_none() {
                return Ok(false);
            }
            let (trace_lhs, trace_rhs) = if *narrowing {
                (
                    normalize_trace_term(m, i, &vars, &lhs_t),
                    normalize_trace_term(m, i, &vars, &rhs_t),
                )
            } else {
                (lhs_t.clone(), rhs_t.clone())
            };
            let shared_label = label.as_deref().map(std::rc::Rc::<str>::from);
            let trace = RlTrace {
                lhs: trace_lhs,
                rhs: trace_rhs,
                condition: condition.clone(),
                var_names: variable_names,
                label: shared_label.clone(),
                nonexec: false, // engine-registered ⇒ executable
                narrowing: *narrowing,
            };
            let id = if condition.is_empty() {
                m.engine.add_labelled_rule(lhs_t, rhs_t, nr, shared_label)
            } else {
                m.engine
                    .add_labelled_conditional_rule(lhs_t, rhs_t, nr, condition, shared_label)
            };
            assert_eq!(
                id as usize,
                m.rl_traces.len(),
                "rule id is the dense rl_traces index"
            );
            m.rl_traces.push(trace);
            return Ok(true);
        }
    }
}

fn push_oo_diagnostic(m: &mut BuiltModule, kind: &str, source: String, transformed: String) {
    m.oo_completion_diagnostics.push(format!(
        "Considering object completion on:\n  {source}\n\
         Transformed {kind}:\n  {transformed}"
    ));
}

fn oo_keyword(keyword: &str, label: &Option<String>) -> String {
    label.as_deref().map_or_else(
        || keyword.to_string(),
        |label| format!("{keyword} [{label}] :"),
    )
}

fn oo_variable_names(m: &BuiltModule, vars: &VarIndex, source_count: u32) -> Vec<String> {
    (0..vars.count())
        .map(|slot| {
            let raw = vars.name(slot);
            let base = raw.split_once(':').map_or(raw, |(base, _)| base);
            let sort = vars.sort(slot);
            let declared = m
                .vars
                .iter()
                .any(|(name, declared_sort)| name == base && *declared_sort == sort);
            if declared {
                base.to_string()
            } else if slot >= source_count {
                format!("{base}:{}", m.engine.sorts().name(sort))
            } else {
                raw.to_string()
            }
        })
        .collect()
}

fn print_oo_term(m: &BuiltModule, i: &Interner, term: &Term, names: &[String]) -> String {
    print_term(m, i, term, names, false)
}

#[allow(clippy::too_many_arguments)]
fn render_oo_equation(
    m: &BuiltModule,
    i: &Interner,
    lhs: &Term,
    rhs: &Term,
    condition: &[ConditionFragment],
    names: &[String],
    owise: bool,
    label: &Option<String>,
) -> String {
    let keyword = oo_keyword(if condition.is_empty() { "eq" } else { "ceq" }, label);
    let mut body = format!(
        "{keyword} {} = {}",
        print_oo_term(m, i, lhs, names),
        print_oo_term(m, i, rhs, names)
    );
    append_oo_condition(m, i, &mut body, condition, names);
    if owise {
        body.push_str(" [owise]");
    }
    body.push_str(" .");
    body
}

fn render_oo_membership(
    m: &BuiltModule,
    i: &Interner,
    lhs: &Term,
    sort: SortId,
    condition: &[ConditionFragment],
    names: &[String],
    label: &Option<String>,
) -> String {
    let keyword = oo_keyword(if condition.is_empty() { "mb" } else { "cmb" }, label);
    let mut body = format!(
        "{keyword} {} : {}",
        print_oo_term(m, i, lhs, names),
        m.engine.sorts().name(sort)
    );
    append_oo_condition(m, i, &mut body, condition, names);
    body.push_str(" .");
    body
}

#[allow(clippy::too_many_arguments)]
fn render_oo_rule(
    m: &BuiltModule,
    i: &Interner,
    lhs: &Term,
    rhs: &Term,
    condition: &[ConditionFragment],
    names: &[String],
    label: &Option<String>,
    narrowing: bool,
) -> String {
    let keyword = oo_keyword(if condition.is_empty() { "rl" } else { "crl" }, label);
    let mut body = format!(
        "{keyword} {} => {}",
        print_oo_term(m, i, lhs, names),
        print_oo_term(m, i, rhs, names)
    );
    append_oo_condition(m, i, &mut body, condition, names);
    if narrowing {
        body.push_str(" [narrowing]");
    }
    body.push_str(" .");
    body
}

fn append_oo_condition(
    m: &BuiltModule,
    i: &Interner,
    body: &mut String,
    condition: &[ConditionFragment],
    names: &[String],
) {
    if condition.is_empty() {
        return;
    }
    body.push_str(" if ");
    for (position, fragment) in condition.iter().enumerate() {
        if position != 0 {
            body.push_str(" /\\ ");
        }
        match fragment {
            ConditionFragment::Equality { lhs, rhs } => {
                body.push_str(&print_oo_term(m, i, lhs, names));
                body.push_str(" = ");
                body.push_str(&print_oo_term(m, i, rhs, names));
            }
            ConditionFragment::SortTest { term, sort } => {
                body.push_str(&print_oo_term(m, i, term, names));
                body.push_str(" : ");
                body.push_str(m.engine.sorts().name(*sort));
            }
            ConditionFragment::Matching {
                pattern, subject, ..
            } => {
                body.push_str(&print_oo_term(m, i, pattern, names));
                body.push_str(" := ");
                body.push_str(&print_oo_term(m, i, subject, names));
            }
            ConditionFragment::Rewrite { lhs, pattern, .. } => {
                body.push_str(&print_oo_term(m, i, lhs, names));
                body.push_str(" => ");
                body.push_str(&print_oo_term(m, i, pattern, names));
            }
        }
    }
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
        Statement::Eq {
            lhs,
            rhs,
            cond,
            owise,
            variant,
            nonexec,
            label,
        } => {
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
                variant: *variant,
                label: label.clone(),
                nonexec: *nonexec,
            }))
        }
        Statement::Mb {
            lhs,
            sort,
            cond,
            nonexec,
            label,
        } => {
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
        Statement::Rule {
            label,
            lhs,
            rhs,
            cond,
            nonexec,
            narrowing,
        } => {
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
                label: label.as_deref().map(std::rc::Rc::<str>::from),
                nonexec: *nonexec,
                narrowing: *narrowing,
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
            frags.push(ConditionFragment::Equality {
                lhs,
                rhs: Term::constant(true_sym),
            });
            continue;
        };
        let frag = match conn {
            Connective::Match => {
                let pattern = parse_build(left, g, m, i, vars)?;
                let subject = parse_build(right, g, m, i, vars)?;
                let mut pat_vars = Vec::new();
                term_var_indices(&pattern, &mut pat_vars);
                let fresh: Vec<u32> = pat_vars
                    .iter()
                    .copied()
                    .filter(|v| !bound.contains(v))
                    .collect();
                bound.extend(pat_vars);
                ConditionFragment::Matching {
                    pattern,
                    subject,
                    fresh_vars: fresh,
                }
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
                let fresh: Vec<u32> = pat_vars
                    .iter()
                    .copied()
                    .filter(|v| !bound.contains(v))
                    .collect();
                bound.extend(pat_vars);
                ConditionFragment::Rewrite {
                    lhs,
                    pattern,
                    fresh_vars: fresh,
                }
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
    if condition
        .iter()
        .any(|f| matches!(f, ConditionFragment::Rewrite { .. }))
    {
        return Err(format!(
            "a rewrite condition (`=>`) is only allowed in a rule (`crl`), not an {owner}"
        ));
    }
    Ok(())
}

/// Collect a term's distinct variable indices, in first-seen order.
/// Whether every variable a statement *instantiates* is bound by the time it is needed: rhs and each
/// condition fragment's evaluated side may use only lhs variables plus the fresh binders of *earlier*
/// `:=`/`=>` fragments (Maude's "used before it is bound" check). A violating statement is degraded to
/// non-executable — parsed but never registered — instead of panicking at `instantiate` (A1c);
/// the caller retains the rejection cause as an owned dropped-statement diagnostic.
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
            ConditionFragment::Matching {
                subject,
                fresh_vars,
                ..
            } => {
                let r = ok(subject, &bound);
                bound.extend_from_slice(fresh_vars);
                r
            }
            ConditionFragment::Rewrite {
                lhs, fresh_vars, ..
            } => {
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
        Term::Iter { arg, .. } => term_var_indices(arg, out),
    }
}

/// Parse a term token bubble to its (unambiguous) parse tree; rejects empty input, no-parse, and ambiguity.
fn parse_forest(tokens: &[Token], g: &CompiledGrammar, i: &Interner) -> Result<PTree, String> {
    let parsed = parse_forest_any(tokens, g, i)?;
    if parsed.ambiguous {
        let rendered = tokens
            .iter()
            .map(|t| i.resolve(t.sym))
            .collect::<Vec<_>>()
            .join(" ");
        return Err(format!("ambiguous parse: `{rendered}`"));
    }
    Ok(parsed.tree)
}

/// Parse a **command** term bubble, warn-and-pick on ambiguity: Maude warns and takes
/// its first parse — our extraction is the same `extractFirstSubparse` walk (first split in
/// chart/completion order, pass2.cc), so the picked tree is used; the warning text is deferred
/// diagnostics (phase E). Statement bubbles keep the strict [`parse_forest`]: their ambiguity today
/// is dominated by the import-reparse artifact (D1a), where a noisy error is the safer behavior
/// until the home-grammar fix lands.
fn parse_forest_pick(tokens: &[Token], g: &CompiledGrammar, i: &Interner) -> Result<PTree, String> {
    Ok(parse_forest_any(tokens, g, i)?.tree)
}

fn parse_effort_error(at: usize, tokens: &[Token], i: &Interner) -> String {
    let token = tokens.get(at).map(|token| token.text(i)).unwrap_or("<end>");
    format!("parse effort limit exceeded at token {at} (`{token}`)")
}

fn parse_forest_any(
    tokens: &[Token],
    g: &CompiledGrammar,
    i: &Interner,
) -> Result<forest::Parse, String> {
    let mut effort = ParseEffort::default();
    parse_forest_any_with_effort(tokens, g, i, &mut effort)
}

fn parse_forest_any_with_effort(
    tokens: &[Token],
    g: &CompiledGrammar,
    i: &Interner,
    effort: &mut ParseEffort,
) -> Result<forest::Parse, String> {
    if tokens.is_empty() {
        return Err("empty term".into());
    }
    let rendered = || {
        tokens
            .iter()
            .map(|t| i.resolve(t.sym))
            .collect::<Vec<_>>()
            .join(" ")
    };
    let chart = earley::parse(g, tokens, Nt::Term, i, effort)
        .map_err(|e| format!("{}: `{}`", parse_effort_error(e.at, tokens, i), rendered()))?;
    if !chart.recognized(g, Nt::Term) {
        let at = chart.furthest();
        let token = tokens.get(at).map(|token| token.text(i)).unwrap_or("<end>");
        return Err(format!(
            "no parse at token {at} (`{token}`): `{}`",
            rendered()
        ));
    }
    forest::extract(g, &chart, tokens.len(), Nt::Term, effort).map_err(|e| match e {
        forest::ExtractError::Effort(exceeded) => format!(
            "{}: `{}`",
            parse_effort_error(exceeded.at, tokens, i),
            rendered()
        ),
        forest::ExtractError::NoParse => format!("no parse: `{}`", rendered()),
    })
}

/// Maude accepts an omitted third argument in object syntax (`< O : C | >`) as the empty
/// `AttributeSet`. The mixfix grammar still sees `<_:_|_>` as an ordinary three-hole operator, so
/// materialize its identity token before parsing. The borrowed common path keeps non-object terms free
/// of token copies.
fn fill_empty_object_attributes<'a>(
    tokens: &'a [Token],
    m: &BuiltModule,
    i: &Interner,
) -> Cow<'a, [Token]> {
    let Some(none) = m
        .engine
        .oo_info()
        .and_then(|info| info.none_sym)
        .and_then(|symbol| i.get(m.engine.symbol(symbol).name()))
    else {
        return Cow::Borrowed(tokens);
    };
    if !tokens
        .windows(2)
        .any(|pair| pair[0].text(i) == "|" && pair[1].text(i) == ">")
    {
        return Cow::Borrowed(tokens);
    }

    let mut filled = Vec::with_capacity(tokens.len() + 1);
    for (index, token) in tokens.iter().copied().enumerate() {
        filled.push(token);
        if token.text(i) == "|"
            && tokens
                .get(index + 1)
                .is_some_and(|next| next.text(i) == ">")
        {
            filled.push(Token {
                sym: none,
                line: token.line,
                kind: TokKind::Ident,
            });
        }
    }
    Cow::Owned(filled)
}

/// One command term parsed once against its module grammar. The token bubble is borrowed on the common
/// path and owned only when omitted object attributes need their identity token materialized.
pub struct ParsedCommandTerm<'a> {
    tokens: Cow<'a, [Token]>,
    parsed: forest::Parse,
}

impl ParsedCommandTerm<'_> {
    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }
    pub(crate) fn tree(&self) -> &PTree {
        &self.parsed.tree
    }
    pub(crate) fn unambiguous_tree(&self, i: &Interner) -> Result<&PTree, String> {
        if self.parsed.ambiguous {
            let rendered = self
                .tokens
                .iter()
                .map(|token| token.text(i))
                .collect::<Vec<_>>()
                .join(" ");
            return Err(format!("ambiguous parse: `{rendered}`"));
        }
        Ok(&self.parsed.tree)
    }
}

pub fn parse_command_term<'a>(
    lm: &LoadedModule,
    i: &Interner,
    tokens: &'a [Token],
) -> Result<ParsedCommandTerm<'a>, String> {
    let tokens = fill_empty_object_attributes(tokens, &lm.built, i);
    let parsed = parse_forest_any(&tokens, &lm.grammar, i)?;
    Ok(ParsedCommandTerm { tokens, parsed })
}

/// Parse a term token bubble and build its kernel [`Term`] (the statement/pattern path).
pub(crate) fn parse_build(
    tokens: &[Token],
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    let tokens = fill_empty_object_attributes(tokens, m, i);
    build_term(&parse_forest(&tokens, g, i)?, g, m, &tokens, i, vars)
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
    let rhs = fill_empty_object_attributes(rhs, m, i);
    if let Some(k) = term_kind(lhs, m) {
        let start = Nt::Comp(k, NtType::Term);
        if let Ok(tree) = parse_forest_at(&rhs, g, i, start) {
            return build_term(&tree, g, m, &rhs, i, vars);
        }
    }
    parse_build(&rhs, g, m, i, vars)
}

/// Like [`parse_forest`] but starting at an arbitrary nonterminal (a per-kind term nonterminal), to parse
/// a bubble constrained to one kind.
fn parse_forest_at(
    tokens: &[Token],
    g: &CompiledGrammar,
    i: &Interner,
    start: Nt,
) -> Result<PTree, String> {
    if tokens.is_empty() {
        return Err("empty term".into());
    }
    let mut effort = ParseEffort::default();
    let chart = earley::parse(g, tokens, start, i, &mut effort)
        .map_err(|e| parse_effort_error(e.at, tokens, i))?;
    if !chart.recognized(g, start) {
        let at = chart.furthest();
        let token = tokens.get(at).map(|token| token.text(i)).unwrap_or("<end>");
        return Err(format!("no parse at token {at} (`{token}`)"));
    }
    let parsed =
        forest::extract(g, &chart, tokens.len(), start, &mut effort).map_err(|e| match e {
            forest::ExtractError::Effort(exceeded) => parse_effort_error(exceeded.at, tokens, i),
            forest::ExtractError::NoParse => "no parse".to_string(),
        })?;
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
    m.sorts
        .get(&name)
        .copied()
        .ok_or_else(|| format!("unknown sort `{name}`"))
}

/// The Maude-faithful command echo for `reduce in M : <term> .`: the parsed term, theory-normalized and
/// pretty-printed exactly as the reference binary prints it. Float, rational, and negative special
/// constants collapse to canonical surface forms (`1.0e+2`, `2/4`, `-3`), redundant parentheses drop, and
/// AC arguments appear in kernel canonical order. Reuses the command's parsed tree, builds the
/// pre-reduction DAG, and renders it.
pub fn command_echo(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
    color: bool,
) -> Result<String, String> {
    let dag = build_subject_dag(lm, term.tree(), term.tokens(), i)?;
    let mut echo = print_pretty(&lm.built, i, dag, color);
    // Nullary overloads share one runtime symbol and therefore cannot carry the parent's expected
    // declaration into pretty-printing. The variant metalevel APIs uniquely require their `empty`
    // argument at `GroundTermList`; restore that statically known domain in the command echo.
    let head = term
        .tokens()
        .first()
        .map(|token| token.text(i))
        .unwrap_or("");
    if matches!(
        head,
        "metaGetVariant"
            | "metaGetIrredundantVariant"
            | "metaVariantUnify"
            | "metaVariantDisjointUnify"
            | "metaVariantMatch"
    ) {
        echo = echo.replace("(empty).EmptyCommaList", "(empty).GroundTermList");
    }
    Ok(echo)
}

pub fn reduce_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
) -> Result<(DagId, u64), String> {
    // Reset BEFORE building so this command's count starts clean. Construction itself does no rewrites
    // (C1: membership axioms now apply lazily at the reduce normal-form point, not at construction); the
    // `reduce` below is where every equation and membership application is counted (Maude's accounting).
    lm.built.engine.reset_rewrites();
    // C7: build the subject inside a structural-dedup window so a repeated subterm (`< g(a), g(a) >`)
    // becomes one shared node — `reduce` then normalizes it once, matching Maude's hash-consed subject
    // DAG. The window must close before `reduce` (it spans only construction); end it even on a build
    // error, then propagate, so a failed parse never leaks an open window into the next command.
    lm.built.engine.begin_dedup();
    let dag = build_subject_dag(lm, term.tree(), term.tokens(), i);
    lm.built.engine.end_dedup();
    let dag = dag?;
    let result = lm.built.engine.reduce(dag);
    Ok((result, lm.built.engine.rewrites()))
}

/// Build a parsed command subject DAG, resetting the rewrite counter and building inside a dedup window
/// exactly like [`reduce_command`]. Shared by the `rewrite`/`frewrite` session builders and the REPL's
/// `reduce` (which then drives [`Engine::reduce_with`](tnk_core::engine::Engine::reduce_with) for
/// META-LEVEL descent).
pub fn build_command_dag(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
) -> Result<DagId, String> {
    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let dag = build_subject_dag(lm, term.tree(), term.tokens(), i);
    lm.built.engine.end_dedup();
    dag
}

/// Parse a command-shaped term into the first one or two concrete parses needed by META-LEVEL's
/// `metaParse`. Each tuple contains the source-order [`Term`] used for up-translation, its variable names,
/// and the canonical symbolic DAG used to compute the least sort.
pub fn build_logic_command_parses(
    lm: &mut LoadedModule,
    i: &Interner,
    tokens: &[Token],
) -> Result<Vec<(Term, VarIndex, DagId)>, String> {
    let parsed = parse_forest_any(tokens, &lm.grammar, i)?;
    let mut trees = vec![parsed.tree];
    if let Some(alternative) = parsed.alternative {
        trees.push(alternative);
    }
    let mut sources = Vec::with_capacity(trees.len());
    for tree in trees {
        let mut vars = VarIndex::new();
        let term = build_term(&tree, &lm.grammar, &lm.built, tokens, i, &mut vars)?;
        sources.push((tree, term, vars));
    }

    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let result = sources
        .into_iter()
        .map(|(tree, term, mut vars)| {
            let dag = build_logic_dag(
                &tree,
                &lm.grammar,
                &mut lm.built.engine,
                lm.built.nat_zero,
                lm.built.nat_succ,
                tokens,
                i,
                &mut vars,
            )?;
            Ok((term, vars, dag))
        })
        .collect();
    lm.built.engine.end_dedup();
    result
}

/// Parse a command-shaped term into a genuine symbolic DAG. Unlike [`build_command_dag`], variables stay
/// [`NodeRepr::Var`](tnk_core::dag::NodeRepr::Var) leaves rather than being lowered to inert constants.
/// META-LEVEL's `metaParse` needs this distinction because its result reifies variables as `Qid` terms.
pub fn build_logic_command_dag(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
) -> Result<DagId, String> {
    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let mut vars = VarIndex::new();
    let dag = build_logic_dag(
        term.tree(),
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        term.tokens(),
        i,
        &mut vars,
    );
    lm.built.engine.end_dedup();
    dag
}

/// Build a command's subject DAG from its parse tree, handling BOTH ground terms (the [`build_dag`] fast
/// path — compact literals/numerals) and **open** terms with variables. Maude reduces open terms (a
/// variable is inert under reduction — `red X:A .`, `red g(X, a) .`, `red N + 1 .`);
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
            tree,
            &lm.grammar,
            &mut lm.built.engine,
            lm.built.nat_zero,
            lm.built.nat_succ,
            term,
            i,
        );
    }
    let mut vars = VarIndex::new();
    let t = build_term(tree, &lm.grammar, &lm.built, term, i, &mut vars)?;
    let bindings: Vec<DagId> = (0..vars.count())
        .map(|idx| {
            let sym = lm
                .built
                .engine
                .add_op(vars.name(idx).to_string(), vec![], vars.sort(idx));
            // Class the atom as a variable: `.=.`'s stability/groundness analysis must see Maude's
            // VariableSymbol (never stable, never ground), and comm/AC canonical ordering must
            // compare same-sort variables by name-token code (the variable's source token is
            // guaranteed interned — it was lexed), not by symbol creation order.
            let rank = i.get(vars.name(idx)).map(|s| s.index()).unwrap_or(u32::MAX);
            lm.built
                .engine
                .set_symbol_class(sym, tnk_core::symbol::SymbolClass::Variable { rank });
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

/// The token index where a failed command/term parse got stuck — the furthest token a valid partial
/// parse consumed (Maude's `badTokenIndex`). `metaParse` reports this as `noParse(n)` (B4);
/// parsed at the universal `Term` start, matching [`build_command_dag`].
pub fn command_parse_furthest(lm: &LoadedModule, i: &Interner, term: &[Token]) -> usize {
    let mut effort = ParseEffort::default();
    match earley::parse(&lm.grammar, term, Nt::Term, i, &mut effort) {
        Ok(chart) => chart.furthest(),
        Err(exceeded) => exceeded.at,
    }
}

/// Begin a `rewrite` (rule-fair) session over `term` (Pillar A). The caller drives the returned
/// [`Rewriting`] with [`Rewriting::run`] and stores it for `continue`.
pub fn rewrite_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
) -> Result<Rewriting, String> {
    let dag = build_command_dag(lm, i, term)?;
    Ok(lm.built.engine.rewrite(dag))
}

/// Begin a `frewrite` (position-fair) session over `term` (Pillar A-ii); `gas` rule applications per
/// position per pass.
pub fn frewrite_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
    gas: u64,
) -> Result<Rewriting, String> {
    let dag = build_command_dag(lm, i, term)?;
    Ok(lm.built.engine.frewrite(dag, gas))
}

/// Begin an `erewrite` (object-message-fair) session over `term` (Pillar 2.5-B); `gas` is the
/// per-position gas for the non-config fallback (default 1).
pub fn erewrite_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &ParsedCommandTerm<'_>,
    gas: u64,
) -> Result<Rewriting, String> {
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
    subject: &ParsedCommandTerm<'_>,
    arrow: SearchArrow,
    pattern: &ParsedCommandTerm<'_>,
    such_that: Option<&[Token]>,
    max_depth: Option<u64>,
) -> Result<(Search, VarIndex), String> {
    // Goal pattern + such-that condition share one variable index.
    let mut vars = VarIndex::new();
    let pat = build_term(
        pattern.unambiguous_tree(i)?,
        &lm.grammar,
        &lm.built,
        pattern.tokens(),
        i,
        &mut vars,
    )?;
    let mut bound: BTreeSet<u32> = (0..vars.count()).collect();
    let cond = match such_that {
        Some(c) => parse_condition(c, &lm.grammar, &lm.built, i, &mut vars, &mut bound)?,
        None => Vec::new(),
    };
    let nr = vars.count();
    // Subject as a ground DAG (reset the counter so the search's rewrites start clean).
    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let subj = build_dag(
        subject.tree(),
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        subject.tokens(),
        i,
    );
    lm.built.engine.end_dedup();
    let subj = subj?;
    let arrow = match arrow {
        SearchArrow::One => Arrow::One,
        SearchArrow::Plus => Arrow::Plus,
        SearchArrow::Star => Arrow::Star,
        SearchArrow::Bang => Arrow::Bang,
    };
    let search = lm
        .built
        .engine
        .search(subj, pat, nr, cond, arrow, max_depth.map(|d| d as u32));
    Ok((search, vars))
}

pub struct SmtSearchCommand {
    pub search: SmtSearch,
    pub goal_variables: VarIndex,
    pub target_variable_count: u32,
}

/// Build an object-level symbolic rewrite search modulo SMT. The initial state and accumulated
/// constraint use genuine variable DAGs; the goal remains a static matcher pattern.
#[allow(clippy::too_many_arguments)]
pub fn smt_search_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    subject: &ParsedCommandTerm<'_>,
    arrow: SearchArrow,
    pattern: &ParsedCommandTerm<'_>,
    such_that: Option<&[Token]>,
    max_depth: Option<u64>,
) -> Result<SmtSearchCommand, String> {
    if matches!(arrow, SearchArrow::Bang) {
        return Err("=>! mode is not supported for searching modulo SMT".to_string());
    }

    let subject_tree = subject.tree();
    let pattern_tree = pattern.tree();

    let mut subject_variables = VarIndex::new();
    let mut goal_variables = VarIndex::new();
    let goal = build_term(
        &pattern_tree,
        &lm.grammar,
        &lm.built,
        pattern.tokens(),
        i,
        &mut goal_variables,
    )?;
    let target_variable_count = goal_variables.count();
    let mut bound: BTreeSet<u32> = (0..target_variable_count).collect();
    let condition = match such_that {
        Some(tokens) => parse_condition(
            tokens,
            &lm.grammar,
            &lm.built,
            i,
            &mut goal_variables,
            &mut bound,
        )?,
        None => Vec::new(),
    };

    if !lm.smt_rewrite_valid || !lm.built.engine.valid_smt_goal(&goal) {
        return Err("module or goal does not satisfy SMT rewriting restrictions".to_string());
    }

    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let subject_dag = build_logic_dag(
        subject_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        subject.tokens(),
        i,
        &mut subject_variables,
    );
    lm.built.engine.end_dedup();
    let subject_dag = subject_dag?;

    let mut variable_names: Vec<String> = (0..subject_variables.count())
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                subject_variables.name(slot),
                subject_variables.sort(slot),
            )
        })
        .collect();
    let subject_variable_count = subject_variables.count();
    let mut goal_variable_dags = Vec::with_capacity(goal_variables.count() as usize);
    for slot in 0..goal_variables.count() {
        let source = goal_variables.name(slot);
        let base = source.split_once(':').map_or(source, |(base, _)| base);
        let code = i.intern(base).index();
        let global_slot = subject_variable_count + slot;
        goal_variable_dags.push(lm.built.engine.make_var(
            goal_variables.sort(slot),
            code,
            global_slot,
        ));
        variable_names.push(command_variable_display_name(
            &lm.grammar,
            i,
            source,
            goal_variables.sort(slot),
        ));
    }

    let initial_constraint = lm
        .built
        .engine
        .make_smt_constraint(&condition, &goal_variable_dags)?;
    let goal_smt_variables = (0..target_variable_count)
        .filter(|&slot| {
            lm.built
                .engine
                .smt_type(goal_variables.sort(slot))
                .is_some()
        })
        .map(|slot| (slot, goal_variable_dags[slot as usize]))
        .collect();
    let arrow = match arrow {
        SearchArrow::One => Arrow::One,
        SearchArrow::Plus => Arrow::Plus,
        SearchArrow::Star => Arrow::Star,
        SearchArrow::Bang => unreachable!("rejected above"),
    };
    let search = lm.built.engine.smt_search(
        subject_dag,
        initial_constraint,
        goal,
        target_variable_count,
        goal_smt_variables,
        arrow,
        max_depth.map(|depth| depth as u32),
        variable_names,
    );
    Ok(SmtSearchCommand {
        search,
        goal_variables,
        target_variable_count,
    })
}

pub struct NarrowCommand {
    pub search: tnk_core::narrow::NarrowSearch,
    pub variables: VarIndex,
    pub initial_variable_count: usize,
    /// Per-root source variables for a disjunction; `None` for the ordinary shared subject/goal scope.
    pub initial_variables: Option<Vec<VarIndex>>,
    pub initial_echoes: Vec<String>,
    pub subject_echo: String,
    pub goal_echo: String,
}

#[allow(clippy::too_many_arguments)]
pub fn narrow_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    subject: &[Token],
    arrow: SearchArrow,
    goal: &[Token],
    max_depth: Option<u64>,
    fold: bool,
    vfold: bool,
    path: bool,
    filter: bool,
    delay: bool,
) -> Result<NarrowCommand, String> {
    use tnk_core::fresh::VariableFamily;
    use tnk_core::narrow::{NarrowFold, NarrowGoal, NarrowOptions, NarrowSearchType};
    use tnk_core::unify::problem::VarSpec;

    let initial_parts = split_on_text(subject, "\\/", i);
    if initial_parts.len() > 1 {
        return narrow_disjunction_command(
            lm,
            i,
            &initial_parts,
            arrow,
            goal,
            max_depth,
            fold,
            vfold,
            path,
            filter,
            delay,
        );
    }

    let subject_tree = parse_forest_pick(subject, &lm.grammar, i)?;
    let goal_tree = parse_forest_pick(goal, &lm.grammar, i)?;
    let mut variables = VarIndex::new();
    let _ = build_term(
        &subject_tree,
        &lm.grammar,
        &lm.built,
        subject,
        i,
        &mut variables,
    )?;
    let initial_variable_count = variables.count() as usize;
    let goal_term = build_term(&goal_tree, &lm.grammar, &lm.built, goal, i, &mut variables)?;
    let goal_variable_names: Vec<_> = (0..variables.count())
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                variables.name(slot),
                variables.sort(slot),
            )
        })
        .collect();
    for slot in 0..variables.count() {
        let base = variables
            .name(slot)
            .split_once(':')
            .map_or(variables.name(slot), |(base, _)| base);
        i.intern(base);
    }
    let mut specs: Vec<_> = (0..variables.count())
        .map(|slot| {
            let source = variables.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            let code = i.intern(base).index();
            VarSpec {
                sort: variables.sort(slot),
                name: maude_variable_name_rank(base, code),
            }
        })
        .collect();

    lm.built.engine.reset_rewrites();
    lm.built.engine.begin_dedup();
    let subject_dag = build_logic_dag(
        &subject_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        subject,
        i,
        &mut variables,
    );
    let goal_dag = build_logic_dag(
        &goal_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        goal,
        i,
        &mut variables,
    );
    lm.built.engine.end_dedup();
    let mut subject_dag = subject_dag?;
    let mut goal_dag = goal_dag?;
    // Maude indexes command variables by walking each canonical DAG, not by source-token order.
    // This is visible in substitutions whenever an AC(U) operator reorders the input.
    let mut variable_order = tnk_core::variant::variables_in_dag(&lm.built.engine, subject_dag);
    for slot in tnk_core::variant::variables_in_dag(&lm.built.engine, goal_dag) {
        if !variable_order.contains(&slot) {
            variable_order.push(slot);
        }
    }
    if variable_order.len() != specs.len() {
        return Err("narrowing variable table does not match the command terms".into());
    }
    let mut new_slot = vec![0u32; specs.len()];
    for (new, &old) in variable_order.iter().enumerate() {
        new_slot[old] = new as u32;
    }
    let remapping: Vec<_> = specs
        .iter()
        .enumerate()
        .map(|(old, spec)| {
            Some(
                lm.built
                    .engine
                    .make_var(spec.sort, spec.name, new_slot[old]),
            )
        })
        .collect();
    subject_dag = tnk_core::unify::instantiate(&mut lm.built.engine, &remapping, subject_dag)
        .unwrap_or(subject_dag);
    goal_dag = tnk_core::unify::instantiate(&mut lm.built.engine, &remapping, goal_dag)
        .unwrap_or(goal_dag);
    specs = variable_order
        .iter()
        .map(|&old| specs[old].clone())
        .collect();
    variables.reorder(&variable_order);
    let echo_variables: Vec<_> = (0..variables.count())
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                variables.name(slot),
                variables.sort(slot),
            )
        })
        .collect();
    let subject_echo =
        print_pretty_with_variables(&lm.built, i, subject_dag, &echo_variables, false);
    let goal_echo = print_term(&lm.built, i, &goal_term, &goal_variable_names, false);

    let equations = executable_variant_equations(&mut lm.built, i);
    let rules = lm.built.engine.narrowing_rules().to_vec();
    let search_type = match arrow {
        SearchArrow::One => NarrowSearchType::One,
        SearchArrow::Plus => NarrowSearchType::AtLeastOne,
        SearchArrow::Star => NarrowSearchType::Any,
        SearchArrow::Bang => NarrowSearchType::NormalForm,
    };
    let options = NarrowOptions {
        search_type,
        max_depth: max_depth.map(|depth| depth as usize),
        filter,
        delay,
        fold: if vfold {
            NarrowFold::Variant
        } else if fold {
            NarrowFold::Match
        } else {
            NarrowFold::None
        },
        keep_history: false,
        keep_paths: path,
        respect_frozen: true,
    };
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let mut search = tnk_core::narrow::NarrowSearch::new(
        &mut env,
        subject_dag,
        specs[..initial_variable_count].to_vec(),
        &rules,
        equations,
        "0",
        options,
    )?;
    let goal = NarrowGoal::new(env.e, goal_dag, specs, initial_variable_count);
    search.set_goal(goal);
    let _ = VariableFamily::Unify;
    Ok(NarrowCommand {
        search,
        variables,
        initial_variable_count,
        initial_variables: None,
        initial_echoes: vec![subject_echo.clone()],
        subject_echo,
        goal_echo,
    })
}

#[allow(clippy::too_many_arguments)]
fn narrow_disjunction_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    initial_parts: &[&[Token]],
    arrow: SearchArrow,
    goal: &[Token],
    max_depth: Option<u64>,
    fold: bool,
    vfold: bool,
    path: bool,
    filter: bool,
    delay: bool,
) -> Result<NarrowCommand, String> {
    use tnk_core::narrow::{NarrowFold, NarrowGoal, NarrowOptions, NarrowSearchType};
    use tnk_core::unify::problem::VarSpec;

    let mut initials = Vec::with_capacity(initial_parts.len());
    let mut initial_variables = Vec::with_capacity(initial_parts.len());
    let mut initial_echoes = Vec::with_capacity(initial_parts.len());
    let mut seen_initial_variables: Vec<(String, tnk_core::sort::SortId, usize)> = Vec::new();

    lm.built.engine.reset_rewrites();
    for (root, &tokens) in initial_parts.iter().enumerate() {
        if tokens.is_empty() {
            return Err("empty initial state in narrowing disjunction".into());
        }
        let tree = parse_forest_pick(tokens, &lm.grammar, i)?;
        let mut variables = VarIndex::new();
        let source_term = build_term(&tree, &lm.grammar, &lm.built, tokens, i, &mut variables)?;
        for slot in 0..variables.count() {
            let source = variables.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            if let Some((_, _, prior)) = seen_initial_variables
                .iter()
                .find(|(name, sort, _)| name == base && *sort == variables.sort(slot))
            {
                return Err(format!(
                    "variable {source} appears in both initial state {} and initial state {root}",
                    prior
                ));
            }
            seen_initial_variables.push((base.to_string(), variables.sort(slot), root));
            i.intern(base);
        }
        let specs: Vec<VarSpec> = (0..variables.count())
            .map(|slot| {
                let source = variables.name(slot);
                let base = source.split_once(':').map_or(source, |(base, _)| base);
                VarSpec {
                    sort: variables.sort(slot),
                    name: maude_variable_name_rank(base, i.intern(base).index()),
                }
            })
            .collect();
        let echo_variables: Vec<_> = (0..variables.count())
            .map(|slot| {
                command_variable_display_name(
                    &lm.grammar,
                    i,
                    variables.name(slot),
                    variables.sort(slot),
                )
            })
            .collect();
        let echo_term = normalize_trace_term(&mut lm.built, i, &variables, &source_term);
        let echo_term = restore_echo_variable_positions(&lm.built, &source_term, echo_term);
        let initial_echo = print_term(&lm.built, i, &echo_term, &echo_variables, false);
        lm.built.engine.begin_dedup();
        let dag = build_logic_dag(
            &tree,
            &lm.grammar,
            &mut lm.built.engine,
            lm.built.nat_zero,
            lm.built.nat_succ,
            tokens,
            i,
            &mut variables,
        );
        lm.built.engine.end_dedup();
        let (dag, specs) =
            canonicalize_narrow_command_dag(&mut lm.built.engine, dag?, specs, &mut variables)?;
        initial_echoes.push(initial_echo);
        initial_variables.push(variables);
        initials.push((dag, specs));
    }

    let goal_tree = parse_forest_pick(goal, &lm.grammar, i)?;
    let mut variables = VarIndex::new();
    let goal_term = build_term(&goal_tree, &lm.grammar, &lm.built, goal, i, &mut variables)?;
    let goal_variable_names: Vec<_> = (0..variables.count())
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                variables.name(slot),
                variables.sort(slot),
            )
        })
        .collect();
    for slot in 0..variables.count() {
        let source = variables.name(slot);
        let base = source.split_once(':').map_or(source, |(base, _)| base);
        if let Some((_, _, root)) = seen_initial_variables
            .iter()
            .find(|(name, sort, _)| name == base && *sort == variables.sort(slot))
        {
            return Err(format!(
                "sharing variable {source} between initial state {root} and the goal is not allowed"
            ));
        }
        i.intern(base);
    }
    let goal_specs: Vec<VarSpec> = (0..variables.count())
        .map(|slot| {
            let source = variables.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            VarSpec {
                sort: variables.sort(slot),
                name: maude_variable_name_rank(base, i.intern(base).index()),
            }
        })
        .collect();
    lm.built.engine.begin_dedup();
    let goal_dag = build_logic_dag(
        &goal_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        goal,
        i,
        &mut variables,
    );
    lm.built.engine.end_dedup();
    let (goal_dag, goal_specs) = canonicalize_narrow_command_dag(
        &mut lm.built.engine,
        goal_dag?,
        goal_specs,
        &mut variables,
    )?;
    let goal_echo = print_term(&lm.built, i, &goal_term, &goal_variable_names, false);

    let equations = executable_variant_equations(&mut lm.built, i);
    let rules = lm.built.engine.narrowing_rules().to_vec();
    let search_type = match arrow {
        SearchArrow::One => NarrowSearchType::One,
        SearchArrow::Plus => NarrowSearchType::AtLeastOne,
        SearchArrow::Star => NarrowSearchType::Any,
        SearchArrow::Bang => NarrowSearchType::NormalForm,
    };
    let options = NarrowOptions {
        search_type,
        max_depth: max_depth.map(|depth| depth as usize),
        filter,
        delay,
        fold: if vfold {
            NarrowFold::Variant
        } else if fold {
            NarrowFold::Match
        } else {
            NarrowFold::None
        },
        keep_history: false,
        keep_paths: path,
        respect_frozen: true,
    };
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let mut search = tnk_core::narrow::NarrowSearch::new_many(
        &mut env, initials, &rules, equations, "0", options,
    )?;
    search.set_goal(NarrowGoal::new(env.e, goal_dag, goal_specs, 0));
    let subject_echo = initial_echoes.join(" \\/ ");
    Ok(NarrowCommand {
        search,
        variables,
        initial_variable_count: 0,
        initial_variables: Some(initial_variables),
        initial_echoes,
        subject_echo,
        goal_echo,
    })
}

fn canonicalize_narrow_command_dag(
    engine: &mut tnk_core::engine::Engine,
    dag: DagId,
    specs: Vec<tnk_core::unify::problem::VarSpec>,
    variables: &mut VarIndex,
) -> Result<(DagId, Vec<tnk_core::unify::problem::VarSpec>), String> {
    let ranked_names: Vec<_> = specs
        .iter()
        .enumerate()
        .map(|(slot, spec)| Some(engine.make_var(spec.sort, spec.name, slot as u32)))
        .collect();
    let dag = tnk_core::unify::instantiate(engine, &ranked_names, dag).unwrap_or(dag);
    let dag = engine.normalize_for_unify(dag);
    let variable_order = tnk_core::variant::variables_in_dag(engine, dag);
    if variable_order.len() != specs.len() {
        return Err("narrowing variable table does not match the command term".into());
    }
    let mut new_slot = vec![0u32; specs.len()];
    for (new, &old) in variable_order.iter().enumerate() {
        new_slot[old] = new as u32;
    }
    let remapping: Vec<_> = specs
        .iter()
        .enumerate()
        .map(|(old, spec)| Some(engine.make_var(spec.sort, spec.name, new_slot[old])))
        .collect();
    let dag = tnk_core::unify::instantiate(engine, &remapping, dag).unwrap_or(dag);
    let specs = variable_order
        .iter()
        .map(|&old| specs[old].clone())
        .collect();
    variables.reorder(&variable_order);
    Ok((dag, specs))
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
/// follow-up; every solution and its bindings are reproduced, only the order may differ.
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
    let subj = build_dag(
        &subj_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        subject,
        i,
    );
    lm.built.engine.end_dedup();
    let subj = subj?;
    let subj = lm.built.engine.reduce(subj);

    // Enumerate while the stream borrows the engine, capturing only `DagId`s; render afterwards.
    let mut raws: Vec<RawSolution> = Vec::new();
    {
        let mut sols = lm.built.engine.match_solutions(pat, nr, subj, xmatch);
        while sols.advance() {
            let bindings = (0..nr)
                .map(|k| {
                    sols.binding(k)
                        .expect("the matcher binds every pattern variable")
                })
                .collect();
            let portion = if xmatch {
                sols.matched_portion_display()
            } else {
                None
            };
            raws.push(RawSolution { bindings, portion });
        }
    }

    Ok(raws
        .iter()
        .map(|r| render_solution(&lm.built, i, r, &vars))
        .collect())
}

/// Render one solution's body: the `Matched portion = …` line (for `xmatch`) followed by the
/// substitution — either `Var --> value` lines (variable order = first occurrence in the pattern,
/// Maude's index order) or `empty substitution` when the pattern is ground.
fn render_solution(m: &BuiltModule, i: &Interner, sol: &RawSolution, vars: &VarIndex) -> String {
    let mut lines: Vec<String> = Vec::new();
    match sol.portion {
        Some(MatchedPortion::Whole) => lines.push("Matched portion = (whole)".to_string()),
        Some(MatchedPortion::Portion(p)) => {
            lines.push(format!(
                "Matched portion = {}",
                print_pretty(m, i, p, false)
            ));
        }
        None => {}
    }
    if sol.bindings.is_empty() {
        lines.push("empty substitution".to_string());
    } else {
        for (k, &b) in sol.bindings.iter().enumerate() {
            lines.push(format!(
                "{} --> {}",
                vars.name(k as u32),
                print_pretty(m, i, b, false)
            ));
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

/// Relative token-name ranks established by Maude 3.5.1's standing prelude before a user module is
/// parsed. VariableTerm comparison uses these global token codes, so a self-contained module still
/// normalizes conventional one-letter variables in this order (direct oracle: an AC sum of A..Z).
/// Names outside the standing set retain this session's interner order after the reserved prefix.
pub fn maude_variable_name_rank(name: &str, fallback: u32) -> u32 {
    const STANDING: &[&str] = &[
        "E", "A", "B", "C", "I", "J", "N", "M", "K", "Z", "Q", "R", "X", "Y", "L", "S", "P", "D",
        "V", "U", "H", "T", "O", "F", "G", "W",
    ];
    STANDING
        .iter()
        .position(|&candidate| candidate == name)
        .map_or(0x100u32.saturating_add(fallback), |rank| rank as u32)
}
/// Maude resolves `X:Sort` to the existing declared variable `X` when both name and sort agree, and
/// consequently drops the on-the-fly sort suffix in command echoes and substitution keys.
pub fn command_variable_display_name(
    grammar: &CompiledGrammar,
    i: &Interner,
    source: &str,
    sort: SortId,
) -> String {
    let Some((base, _)) = source.split_once(':') else {
        return source.to_string();
    };
    let declared = grammar.prods.iter().any(|prod| {
        matches!(prod.action, Action::MakeVariable(s) if s == sort)
            && matches!(
                prod.rhs.as_slice(),
                [GSym::T(Terminal::Tok(sym))] if i.resolve(*sym) == base
            )
    });
    if declared {
        base.to_string()
    } else {
        source.to_string()
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
    pub(crate) source_var_names: Vec<String>,
    pub(crate) equations: Vec<(DagId, DagId)>,
    pub(crate) specs: Vec<tnk_core::unify::problem::VarSpec>,
    pub(crate) vars: VarIndex,
}

fn build_unify_echo_term(
    tree: &PTree,
    lm: &LoadedModule,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    build_term(tree, &lm.grammar, &lm.built, tokens, i, vars)
}

/// Build a `unify` command: parse each pair with temporary source-order slots, theory-normalize every
/// side, then use Maude's post-normalization variable order for the resumable order-sorted problem and
/// displayed substitution keys.
pub fn unify_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    body: &[Token],
) -> Result<UnifyCommand, String> {
    use tnk_core::fresh::VariableFamily;
    use tnk_core::unify::problem::{UnifyProblem, VarSpec};

    let conjs = split_on_text(body, "/\\", i);
    let sides: Vec<_> = conjs.iter().map(|c| split_on_text(c, "=?", i)).collect();
    if sides.iter().any(|s| s.len() != 2) {
        return Err("unify: each conjunct must be `T1 =? T2`".to_string());
    }

    let mut vars = VarIndex::new();
    let mut equations = Vec::with_capacity(sides.len());
    let mut echo_pairs = Vec::with_capacity(sides.len());
    for side in &sides {
        let lhs_tree = parse_forest_pick(side[0], &lm.grammar, i)?;
        // Establish source-order variable slots before the DAG constructor canonicalizes commutative args.
        let lhs_echo = build_unify_echo_term(&lhs_tree, lm, side[0], i, &mut vars)?;
        // `Token::split` interns the base when Maude turns an on-the-fly `X:Sort` token into a
        // VariableTerm. Do that before the DAG builder records the variable's name id.
        for idx in 0..vars.count() {
            let name = vars.name(idx);
            let base = name.split_once(':').map_or(name, |(base, _)| base);
            i.intern(base);
        }
        let lhs = build_logic_dag(
            &lhs_tree,
            &lm.grammar,
            &mut lm.built.engine,
            lm.built.nat_zero,
            lm.built.nat_succ,
            side[0],
            i,
            &mut vars,
        )?;
        let rhs_tree = parse_forest_pick(side[1], &lm.grammar, i)?;
        let rhs_echo = build_unify_echo_term(&rhs_tree, lm, side[1], i, &mut vars)?;
        for idx in 0..vars.count() {
            let name = vars.name(idx);
            let base = name.split_once(':').map_or(name, |(base, _)| base);
            i.intern(base);
        }
        let rhs = build_logic_dag(
            &rhs_tree,
            &lm.grammar,
            &mut lm.built.engine,
            lm.built.nat_zero,
            lm.built.nat_succ,
            side[1],
            i,
            &mut vars,
        )?;
        echo_pairs.push((lhs_echo, rhs_echo));
        equations.push((lhs, rhs));
    }

    let source_var_names: Vec<String> = (0..vars.count())
        .map(|idx| command_variable_display_name(&lm.grammar, i, vars.name(idx), vars.sort(idx)))
        .collect();
    let echo = echo_pairs
        .iter()
        .map(|(lhs, rhs)| {
            format!(
                "{} =? {}",
                print_term(&lm.built, i, lhs, &source_var_names, false),
                print_term(&lm.built, i, rhs, &source_var_names, false)
            )
        })
        .collect::<Vec<_>>()
        .join(" /\\ ");
    let specs: Vec<VarSpec> = (0..vars.count())
        .map(|idx| {
            let source_name = vars.name(idx);
            let base = source_name
                .split_once(':')
                .map_or(source_name, |(base, _)| base);
            let code = i.intern(base).index();
            VarSpec {
                sort: vars.sort(idx),
                name: maude_variable_name_rank(base, code),
            }
        })
        .collect();

    let namegen = tnk_core::fresh::FreshVariableGenerator::new();
    let names_ok = source_var_names.iter().all(|name| {
        let bare = name.split(':').next().unwrap_or(name);
        !namegen.variable_name_conflict(bare, None)
    });
    let source_equations = equations.clone();
    let source_specs = specs.clone();
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let problem = UnifyProblem::new(&mut env, equations, specs, VariableFamily::Unify, "0");
    let var_names = problem
        .original_variable_order()
        .iter()
        .map(|&old| source_var_names[old].clone())
        .collect();
    Ok(UnifyCommand {
        echo,
        var_names,
        names_ok,
        problem,
        source_var_names,
        equations: source_equations,
        specs: source_specs,
        vars,
    })
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

/// Parsed state for a resumable `get variants` command.
pub struct VariantCommand {
    pub echo: String,
    pub var_names: Vec<String>,
    pub names_ok: bool,
    pub search: VariantSearch,
}

/// Parsed state for a plain or filtered variant-unification command.
pub struct VariantUnifyCommand {
    pub echo: String,
    pub var_names: Vec<String>,
    pub names_ok: bool,
    pub pair_count: usize,
    pub search: VariantSearch,
}

/// Parsed state for variant matching: an irredundant pattern-variant search plus the grounded
/// subject matched against each surviving variant.
pub struct VariantMatchCommand {
    pub echo: String,
    pub var_names: Vec<String>,
    pub names_ok: bool,
    pub search: VariantSearch,
    pub subject: DagId,
    pub restorations: Vec<(DagId, DagId)>,
    pub fresh_base: String,
}

fn collect_term_variable_sorts(term: &Term, sorts: &mut Vec<Option<SortId>>) {
    match term {
        Term::Var(v) => {
            let slot = v.index as usize;
            if sorts.len() <= slot {
                sorts.resize(slot + 1, None);
            }
            sorts[slot] = Some(v.sort);
        }
        Term::Op { args, .. } => {
            for arg in args {
                collect_term_variable_sorts(arg, sorts);
            }
        }
        Term::Iter { arg, .. } => collect_term_variable_sorts(arg, sorts),
        Term::Na { .. } => {}
    }
}

pub fn executable_variant_equations(m: &mut BuiltModule, i: &mut Interner) -> Vec<VariantEquation> {
    use tnk_core::unify::problem::VarSpec;

    let traces = &m.eq_traces;
    let engine = &mut m.engine;
    traces
        .iter()
        .enumerate()
        .filter(|(_, trace)| trace.variant && !trace.nonexec)
        .map(|(id, trace)| {
            let mut sorts = Vec::new();
            collect_term_variable_sorts(&trace.lhs, &mut sorts);
            collect_term_variable_sorts(&trace.rhs, &mut sorts);
            let variables: Vec<_> = sorts
                .into_iter()
                .enumerate()
                .map(|(slot, sort)| {
                    let source = trace.var_names.get(slot).map(String::as_str).unwrap_or("X");
                    let base = source.split_once(':').map_or(source, |(base, _)| base);
                    let code = i.intern(base).index();
                    VarSpec {
                        sort: sort.expect("each statement variable occurs in its lhs or rhs"),
                        name: maude_variable_name_rank(base, code),
                    }
                })
                .collect();
            compile_variant_equation(engine, id as u32, &trace.lhs, &trace.rhs, variables)
        })
        .collect()
}

/// Build the target, irreducibility blockers, and executable `[variant]` equation set for `get
/// variants`. The target's source slots are reordered only after theory canonicalization, matching
/// Maude's `VariantSearch` constructor.
pub fn variant_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    term: &[Token],
    irreducible: Option<&[Token]>,
    irredundant: bool,
) -> Result<VariantCommand, String> {
    use tnk_core::fresh::{FreshVariableGenerator, VariableFamily};
    use tnk_core::unify::problem::VarSpec;

    let mut vars = VarIndex::new();
    let tree = parse_forest_pick(term, &lm.grammar, i)?;
    let _source_term = build_term(&tree, &lm.grammar, &lm.built, term, i, &mut vars)?;
    for slot in 0..vars.count() {
        let source = vars.name(slot);
        let base = source.split_once(':').map_or(source, |(base, _)| base);
        i.intern(base);
    }
    let target = build_logic_dag(
        &tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        term,
        i,
        &mut vars,
    )?;
    let echo_term = tnk_core::variant::term_from_dag_slots(&lm.built.engine, target);
    let target_variables = vars.count();

    let mut blocker_terms = Vec::new();
    let mut blockers = Vec::new();
    if let Some(body) = irreducible {
        for part in split_on_text(body, ",", i) {
            let tree = parse_forest_pick(part, &lm.grammar, i)?;
            let source_term = build_term(&tree, &lm.grammar, &lm.built, part, i, &mut vars)?;
            for slot in 0..vars.count() {
                let source = vars.name(slot);
                let base = source.split_once(':').map_or(source, |(base, _)| base);
                i.intern(base);
            }
            let blocker = build_logic_dag(
                &tree,
                &lm.grammar,
                &mut lm.built.engine,
                lm.built.nat_zero,
                lm.built.nat_succ,
                part,
                i,
                &mut vars,
            )?;
            blocker_terms.push(source_term);
            blockers.push(blocker);
        }
    }

    let source_var_names: Vec<String> = (0..vars.count())
        .map(|slot| command_variable_display_name(&lm.grammar, i, vars.name(slot), vars.sort(slot)))
        .collect();
    let mut echo = print_term(&lm.built, i, &echo_term, &source_var_names, false);
    if !blocker_terms.is_empty() {
        let blockers = blocker_terms
            .iter()
            .map(|term| print_term(&lm.built, i, term, &source_var_names, false))
            .collect::<Vec<_>>()
            .join(", ");
        echo.push_str(" such that ");
        echo.push_str(&blockers);
        echo.push_str(" irreducible");
    }
    let specs: Vec<VarSpec> = (0..target_variables)
        .map(|slot| {
            let source = vars.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            let code = i.intern(base).index();
            VarSpec {
                sort: vars.sort(slot),
                name: maude_variable_name_rank(base, code),
            }
        })
        .collect();
    let namegen = FreshVariableGenerator::new();
    let names_ok = source_var_names.iter().all(|name| {
        let bare = name.split(':').next().unwrap_or(name);
        !namegen.variable_name_conflict(bare, None)
    });
    let equations = executable_variant_equations(&mut lm.built, i);
    lm.built.engine.reset_rewrites();
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let mode = if irredundant {
        VariantMode::Irredundant
    } else {
        VariantMode::Incremental
    };
    let search = VariantSearch::new(
        &mut env,
        target,
        specs,
        blockers,
        equations,
        mode,
        None::<VariableFamily>,
        "0",
    )?;
    let var_names = search
        .original_variable_order()
        .iter()
        .map(|&old| source_var_names[old].clone())
        .collect();
    Ok(VariantCommand {
        echo,
        var_names,
        names_ok,
        search,
    })
}

pub fn variant_unify_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    body: &[Token],
    irreducible: Option<&[Token]>,
    _filtered: bool,
) -> Result<VariantUnifyCommand, String> {
    use tnk_core::fresh::VariableFamily;

    let UnifyCommand {
        mut echo,
        names_ok,
        problem,
        source_var_names,
        equations,
        specs,
        mut vars,
        ..
    } = unify_command(lm, i, body)?;
    drop(problem);
    let pair_count = equations.len();
    if pair_count == 0 {
        return Err("variant unify: expected at least one unification pair".to_string());
    }

    let mut blockers = Vec::new();
    let mut blocker_echoes = Vec::new();
    if let Some(tokens) = irreducible {
        for part in split_on_text(tokens, ",", i) {
            let tree = parse_forest_pick(part, &lm.grammar, i)?;
            let echo_term = build_term(&tree, &lm.grammar, &lm.built, part, i, &mut vars)?;
            for slot in 0..vars.count() {
                let source = vars.name(slot);
                let base = source.split_once(':').map_or(source, |(base, _)| base);
                i.intern(base);
            }
            let dag = build_logic_dag(
                &tree,
                &lm.grammar,
                &mut lm.built.engine,
                lm.built.nat_zero,
                lm.built.nat_succ,
                part,
                i,
                &mut vars,
            )?;
            blocker_echoes.push(print_term(
                &lm.built,
                i,
                &echo_term,
                &source_var_names,
                false,
            ));
            blockers.push(dag);
        }
    }
    if !blocker_echoes.is_empty() {
        echo.push_str(" such that ");
        echo.push_str(&blocker_echoes.join(", "));
        echo.push_str(" irreducible");
    }

    let target = if pair_count == 1 {
        let (lhs, rhs) = equations[0];
        let domains = [lhs, rhs]
            .map(|dag| {
                let sort = lm.built.engine.sort_of(dag);
                let kind = lm.built.engine.sorts().kind_of(sort);
                lm.built.engine.sorts().error_sort(kind)
            })
            .to_vec();
        let result_sort = domains[0];
        let pair_symbol = lm
            .built
            .engine
            .add_op("$variant-unification-pair", domains, result_sort);
        lm.built.engine.make_free(pair_symbol, vec![lhs, rhs])
    } else {
        let lhs: Vec<_> = equations.iter().map(|&(lhs, _)| lhs).collect();
        let rhs: Vec<_> = equations.iter().map(|&(_, rhs)| rhs).collect();
        let tuple_sort = {
            let kind = lm
                .built
                .engine
                .sorts()
                .kind_of(lm.built.engine.sort_of(lhs[0]));
            lm.built.engine.sorts().error_sort(kind)
        };
        let lhs_domains = lhs
            .iter()
            .map(|&dag| {
                let kind = lm
                    .built
                    .engine
                    .sorts()
                    .kind_of(lm.built.engine.sort_of(dag));
                lm.built.engine.sorts().error_sort(kind)
            })
            .collect();
        let rhs_domains = rhs
            .iter()
            .map(|&dag| {
                let kind = lm
                    .built
                    .engine
                    .sorts()
                    .kind_of(lm.built.engine.sort_of(dag));
                lm.built.engine.sorts().error_sort(kind)
            })
            .collect();
        let lhs_symbol =
            lm.built
                .engine
                .add_op("$variant-unification-lhs", lhs_domains, tuple_sort);
        let rhs_symbol =
            lm.built
                .engine
                .add_op("$variant-unification-rhs", rhs_domains, tuple_sort);
        let lhs = lm.built.engine.make_free(lhs_symbol, lhs);
        let rhs = lm.built.engine.make_free(rhs_symbol, rhs);
        let pair_symbol = lm.built.engine.add_op(
            "$variant-unification-pair",
            vec![tuple_sort, tuple_sort],
            tuple_sort,
        );
        lm.built.engine.make_free(pair_symbol, vec![lhs, rhs])
    };
    let target = lm.built.engine.normalize_for_unify(target);
    let equations = executable_variant_equations(&mut lm.built, i);
    lm.built.engine.reset_rewrites();
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let mode = VariantMode::Incremental;
    let mut search = VariantSearch::new(
        &mut env,
        target,
        specs,
        blockers,
        equations,
        mode,
        None::<VariableFamily>,
        "0",
    )?;
    search.enable_unification(env.e, pair_count);
    let var_names = search
        .original_variable_order()
        .iter()
        .map(|&old| source_var_names[old].clone())
        .collect();
    Ok(VariantUnifyCommand {
        echo,
        var_names,
        names_ok,
        pair_count,
        search,
    })
}

pub fn variant_match_command(
    lm: &mut LoadedModule,
    i: &mut Interner,
    pattern: &[Token],
    subject: &[Token],
    irreducible: Option<&[Token]>,
) -> Result<VariantMatchCommand, String> {
    use tnk_core::fresh::{FreshVariableGenerator, VariableFamily};
    use tnk_core::unify::problem::VarSpec;

    let mut pattern_vars = VarIndex::new();
    let pattern_tree = parse_forest_pick(pattern, &lm.grammar, i)?;
    let pattern_term = build_term(
        &pattern_tree,
        &lm.grammar,
        &lm.built,
        pattern,
        i,
        &mut pattern_vars,
    )?;
    for slot in 0..pattern_vars.count() {
        let source = pattern_vars.name(slot);
        i.intern(source.split_once(':').map_or(source, |(base, _)| base));
    }
    let pattern_dag = build_logic_dag(
        &pattern_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        pattern,
        i,
        &mut pattern_vars,
    )?;
    let target_variables = pattern_vars.count();
    let source_var_names: Vec<_> = (0..target_variables)
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                pattern_vars.name(slot),
                pattern_vars.sort(slot),
            )
        })
        .collect();

    let mut subject_vars = VarIndex::new();
    let subject_tree = parse_forest_pick(subject, &lm.grammar, i)?;
    let subject_term = build_term(
        &subject_tree,
        &lm.grammar,
        &lm.built,
        subject,
        i,
        &mut subject_vars,
    )?;
    for slot in 0..subject_vars.count() {
        let source = subject_vars.name(slot);
        i.intern(source.split_once(':').map_or(source, |(base, _)| base));
    }
    let subject_dag = build_logic_dag(
        &subject_tree,
        &lm.grammar,
        &mut lm.built.engine,
        lm.built.nat_zero,
        lm.built.nat_succ,
        subject,
        i,
        &mut subject_vars,
    )?;
    let subject_var_names: Vec<_> = (0..subject_vars.count())
        .map(|slot| {
            command_variable_display_name(
                &lm.grammar,
                i,
                subject_vars.name(slot),
                subject_vars.sort(slot),
            )
        })
        .collect();
    let fresh_base = subject_var_names
        .iter()
        .filter_map(|name| {
            name.split(':')
                .next()
                .and_then(|bare| bare.strip_prefix('#'))
                .and_then(|digits| digits.parse::<u64>().ok())
        })
        .max()
        .unwrap_or(0)
        .to_string();
    let (subject_dag, mut restorations) =
        tnk_core::variant::ground_subject_variables(&mut lm.built.engine, subject_dag);
    for (index, (_, variable)) in restorations.iter_mut().enumerate() {
        let sort = lm.built.engine.sort_of(*variable);
        let display = subject_var_names
            .get(index)
            .map(String::as_str)
            .unwrap_or("X");
        *variable = lm
            .built
            .engine
            .make_var(sort, i.intern(display).index(), index as u32);
    }

    let mut blockers = Vec::new();
    let mut blocker_echoes = Vec::new();
    if let Some(tokens) = irreducible {
        for part in split_on_text(tokens, ",", i) {
            let tree = parse_forest_pick(part, &lm.grammar, i)?;
            let term = build_term(&tree, &lm.grammar, &lm.built, part, i, &mut pattern_vars)?;
            let dag = build_logic_dag(
                &tree,
                &lm.grammar,
                &mut lm.built.engine,
                lm.built.nat_zero,
                lm.built.nat_succ,
                part,
                i,
                &mut pattern_vars,
            )?;
            blocker_echoes.push(print_term(&lm.built, i, &term, &source_var_names, false));
            blockers.push(dag);
        }
    }

    let mut echo = format!(
        "{} <=? {}",
        print_term(&lm.built, i, &pattern_term, &source_var_names, false),
        print_term(&lm.built, i, &subject_term, &subject_var_names, false)
    );
    if !blocker_echoes.is_empty() {
        echo.push_str(" such that ");
        echo.push_str(&blocker_echoes.join(", "));
        echo.push_str(" irreducible");
    }
    let specs: Vec<VarSpec> = (0..target_variables)
        .map(|slot| {
            let source = pattern_vars.name(slot);
            let base = source.split_once(':').map_or(source, |(base, _)| base);
            VarSpec {
                sort: pattern_vars.sort(slot),
                name: maude_variable_name_rank(base, i.intern(base).index()),
            }
        })
        .collect();
    let namegen = FreshVariableGenerator::new();
    let names_ok = source_var_names.iter().all(|name| {
        let bare = name.split(':').next().unwrap_or(name);
        !namegen.variable_name_conflict(bare, None)
    });
    let equations = executable_variant_equations(&mut lm.built, i);
    lm.built.engine.reset_rewrites();
    let mut names = InternerNames(i);
    let mut env = tnk_core::unify::UnifyEnv {
        e: &mut lm.built.engine,
        names: &mut names,
    };
    let search = VariantSearch::new(
        &mut env,
        pattern_dag,
        specs,
        blockers,
        equations,
        VariantMode::Irredundant,
        None::<VariableFamily>,
        &fresh_base,
    )?;
    let var_names = search
        .original_variable_order()
        .iter()
        .map(|&old| source_var_names[old].clone())
        .collect();
    Ok(VariantMatchCommand {
        echo,
        var_names,
        names_ok,
        search,
        subject: subject_dag,
        restorations,
        fresh_base,
    })
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
        Reduce {
            sort: &'static str,
            term: &'static str,
            rewrites: u64,
        },
        /// A `match`/`xmatch`: the expected solution blocks (each the `Var --> value` lines, or for
        /// `xmatch` the `Matched portion = …` line + substitution), rendered by [`render_solution`].
        /// Compared **as a set** (both sides sorted): the binary's exact ACU/AU solution *order* is
        /// Maude's Diophantine order, a deferred B1 follow-up — we reproduce every solution and its
        /// bindings, only the order may differ (CUI's two pairings happen to match order too).
        Match(&'static [&'static str]),
    }

    const fn e(sort: &'static str, term: &'static str, rewrites: u64) -> Expect {
        Expect::Reduce {
            sort,
            term,
            rewrites,
        }
    }

    const fn mat(blocks: &'static [&'static str]) -> Expect {
        Expect::Match(blocks)
    }

    /// A command's tokens, owned so the loop can `&mut`-borrow `loaded.modules` while iterating.
    enum Cmd {
        Reduce(Vec<Token>),
        Match {
            pattern: Vec<Token>,
            subject: Vec<Token>,
            xmatch: bool,
        },
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
                    Command::Match {
                        pattern,
                        subject,
                        xmatch,
                        ..
                    } => Cmd::Match {
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
                (
                    Cmd::Reduce(term),
                    Expect::Reduce {
                        sort,
                        term: eterm,
                        rewrites,
                    },
                ) => {
                    let parsed = parse_command_term(&loaded.modules[*m], &loaded.interner, term)
                        .unwrap_or_else(|err| panic!("command {idx}: {err}"));
                    let (got, rw) =
                        reduce_command(&mut loaded.modules[*m], &loaded.interner, &parsed)
                            .unwrap_or_else(|err| panic!("command {idx}: {err}"));
                    {
                        let eng = &loaded.modules[*m].built.engine;
                        assert_eq!(
                            eng.sorts().name(eng.sort_of(got)),
                            *sort,
                            "command {idx} sort"
                        );
                    }
                    assert_eq!(rw, *rewrites, "command {idx} rewrite count");

                    let exp_toks = tokenize(eterm, &mut loaded.interner);
                    let expected_parsed =
                        parse_command_term(&loaded.modules[*m], &loaded.interner, &exp_toks)
                            .unwrap_or_else(|err| {
                                panic!("command {idx} expected `{eterm}`: {err}")
                            });
                    let (want, _) =
                        reduce_command(&mut loaded.modules[*m], &loaded.interner, &expected_parsed)
                            .unwrap_or_else(|err| {
                                panic!("command {idx} expected `{eterm}`: {err}")
                            });
                    let eng = &loaded.modules[*m].built.engine;
                    assert!(
                        eng.deep_equal(got, want),
                        "command {idx} value: expected `{eterm}`"
                    );
                }
                (
                    Cmd::Match {
                        pattern,
                        subject,
                        xmatch,
                    },
                    Expect::Match(blocks),
                ) => {
                    let mut got = match_command(
                        &mut loaded.modules[*m],
                        &loaded.interner,
                        pattern,
                        subject,
                        *xmatch,
                    )
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
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../conformance/",
                $name
            ))
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
    fn compact_prefix_iteration_command_stays_one_iter_node() {
        let mut loaded = load_source(
            "fmod PREFIX-ITER is
               sort Nat .
               op 0 : -> Nat [ctor] .
               op s : Nat -> Nat [ctor iter] .
             endfm",
        )
        .expect("load prefix iter module");
        let term = tokenize("s^1000000(0)", &mut loaded.interner);
        let lm = &mut loaded.modules[0];

        let parsed = parse_command_term(lm, &loaded.interner, &term).expect("parse command");
        assert_eq!(
            command_echo(lm, &loaded.interner, &parsed, false).expect("command echo"),
            "s^1000000(0)"
        );
        let (result, rewrites) =
            reduce_command(lm, &loaded.interner, &parsed).expect("reduce compact prefix iteration");
        assert_eq!(rewrites, 0);
        assert_eq!(
            lm.built
                .engine
                .sorts()
                .name(lm.built.engine.sort_of(result)),
            "Nat"
        );
        assert_eq!(
            crate::pretty::print_raw(&lm.built, &loaded.interner, result),
            "s^1000000(0)",
            "round-trip printer must not expand the million-count iter node"
        );
        match lm.built.engine.node(result).repr() {
            tnk_core::dag::NodeRepr::Iter { count, arg } => {
                assert_eq!(count, "1000000");
                assert!(matches!(
                    lm.built.engine.node(arg).repr(),
                    tnk_core::dag::NodeRepr::App
                ));
            }
            other => panic!("expected one compact iter node, got {other:?}"),
        }
    }

    #[test]
    fn prefix_and_mixfix_iter_notation_follow_overloaded_ditto_syntax() {
        let mut loaded = load_source(
            "fmod ITER-SYNTAX is
               sorts Small Big .
               subsort Small < Big .
               op a : -> Small [ctor] .
               op g : Big -> Big [ctor iter] .
               op g : Small -> Small [ditto] .
               op s_ : Big -> Big [ctor iter] .
               op s_ : Small -> Small [ditto] .
             endfm",
        )
        .expect("load overloaded iter module");

        for (input, echo) in [
            ("g^1(a)", "g(a)"),
            ("g^2(a)", "g^2(a)"),
            ("s_^1(a)", "s a"),
            ("s_^3(a)", "s_^3(a)"),
        ] {
            let term = tokenize(input, &mut loaded.interner);
            let lm = &mut loaded.modules[0];
            let parsed = parse_command_term(lm, &loaded.interner, &term).expect("parse command");
            assert_eq!(
                command_echo(lm, &loaded.interner, &parsed, false).expect("iter command echo"),
                echo,
                "oracle print for `{input}`"
            );
            let (result, rewrites) =
                reduce_command(lm, &loaded.interner, &parsed).expect("reduce overloaded iter");
            assert_eq!(rewrites, 0);
            assert_eq!(
                lm.built
                    .engine
                    .sorts()
                    .name(lm.built.engine.sort_of(result)),
                "Small",
                "ditto declaration selects the Small sort for `{input}`"
            );
        }
    }

    #[test]
    fn u03_million_iter_identities_load_and_commands_five_six_match() {
        let mut loaded =
            load_source(conformance_file!("subsystems/U03-unification3.maude")).expect("load U03");
        let targets: Vec<_> = loaded
            .commands
            .iter()
            .skip(4)
            .take(2)
            .map(|(module, command)| {
                let Command::Unify { body, .. } = command else {
                    panic!("U03 commands 5/6 must be unify commands")
                };
                (*module, body.clone())
            })
            .collect();
        assert_eq!(targets.len(), 2);

        let expected = [
            vec!["X:Small --> #1:Small\nZ:Small --> #1:Small\nY:Big --> g^999999(a)"],
            vec![
                "X:Small --> #1:Small\nZ:Small --> #1:Small\nY:Big --> g^999999(a)",
                "X:Small --> f(#1:Small, g(#2:Small))\nZ:Small --> #1:Small\nY:Big --> #2:Small",
            ],
        ];

        for ((module, body), want) in targets.into_iter().zip(expected) {
            let mut command =
                unify_command(&mut loaded.modules[module], &mut loaded.interner, &body)
                    .expect("build U03 unify");
            assert_eq!(command.echo, "X:Small =? f(g(Y:Big), Z:Small)");
            assert!(command.names_ok && command.problem.problem_okay());

            let mut solutions = Vec::new();
            {
                let mut names = InternerNames(&mut loaded.interner);
                let mut env = tnk_core::unify::UnifyEnv {
                    e: &mut loaded.modules[module].built.engine,
                    names: &mut names,
                };
                while let Some(binding) = command.problem.find_next(&mut env) {
                    solutions.push(binding);
                }
            }
            let got: Vec<_> = solutions
                .iter()
                .map(|binding| {
                    render_unifier(
                        &loaded.modules[module].built,
                        &loaded.interner,
                        &command.var_names,
                        binding,
                    )
                })
                .collect();
            assert_eq!(got, want);
        }
    }

    #[test]
    fn iter_comm_normalization_uses_standing_maude_name_order() {
        let mut loaded = load_source(conformance_file!("subsystems/U-ch13-07-iter-comm.maude"))
            .expect("load iter-comm fixture");
        let commands: Vec<_> = loaded
            .commands
            .iter()
            .map(|(module, command)| {
                let Command::Unify { body, .. } = command else {
                    panic!("iter-comm fixture contains only unify commands")
                };
                (*module, body.clone())
            })
            .collect();
        let expected = [
            vec!["X:OddNat", "Y:Int"],
            vec!["X:OddNat", "W:Int", "Z:Int", "Y:Int"],
            vec!["X:OddNat", "W:Int", "Z:Int", "Y:Int"],
        ];

        for ((module, body), expected_names) in commands.into_iter().zip(expected) {
            let command = unify_command(&mut loaded.modules[module], &mut loaded.interner, &body)
                .expect("build iter-comm unify");
            assert_eq!(command.var_names, expected_names);
        }
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
            &[
                e("Nat", "s s s s 0", 3),
                e("Nat", "s s s s s s s s s s s s 0", 21),
            ],
        );
    }

    #[test]
    fn strat_conforms() {
        conform(
            conformance_file!("strat.maude"),
            &[
                e("Nat", "s s z", 1),
                e("Nat", "z", 1),
                e("Nat", "z", 1),
                e("Nat", "s s z", 2),
                e("S", "b", 1),                    // (0 1 0): first top succeeds
                e("S", "b", 2),                    // first top misses; argument then final top
                e("S", "b", 1),                    // first top skips a reducible argument
                e("S", "b", 2),                    // intermediate top excludes owise
                e("S", "b", 2),                    // (1 0 2 0): intermediate top skips arg 2
                e("S", "b", 3),                    // both staged arguments, then final top
                e("S", "b", 2),                    // missing final zero is appended
                e("S", "b", 2),                    // a strategy with no zero gets a final one
                e("S", "b", 2),                    // duplicate arguments/adjacent zeroes normalize
                e("S", "pair(a, a)", 2), // shared post-top redexes are copied per occurrence
                e("S", "pair(box(a), box(a))", 2), // eager descendants are copied too
                e("S", "a m a m b", 2),  // semi-eager AC reduces every physical argument
                e("S", "a ; b ; a", 3),  // semi-eager AU preserves per-occurrence accounting
            ],
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
                e("Nat", "s s s s s s z", 8),        // 2 * 3
                e("Nat", "s s s s s s s s s z", 13), // 3 * 3
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
                e("E", "a b c", 2),     // (s s a) b c — peel two successors off the head
                e("E", "a b c", 1),     // a (s b) c   — interior successor untouched
                e("E", "a b c", 2),     // (s a)(s b) c
                e("E", "a", 1),         // a a         — non-linear collapse
                e("E", "a", 2),         // a a a
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
                e("E", "b c", 1),      // f(a b c) — AU alien under free f
                e("E", "f(b c)", 0),   // f(b c)   — no match (head is not a)
                e("E", "b ; c", 1),    // g(a ; b ; c) — AC alien under free g
                e("E", "g(b ; c)", 0), // g(b ; c)
                e("E", "c a", 1),      // h(a c, b a) — two aliens, one per argument
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
                e("Pair", "s a + b", 1), // alien membership lhs `s M + N` matches modulo AC
                e("Pair", "s a + s a", 1), // both apply; the tie-break picks Pair
                // AU-MB
                e("Lst", "a b c", 1),
                e("E", "b c", 0),
                e("Spec", "s a b c", 1), // alien head `(s M) L` matches modulo AU
                // S-MB
                e("Zero", "0", 0),
                e("NzNat", "s s 0", 0), // too few successors
                e("Big", "s s s 0", 1), // iter/S membership lhs `s s s X`
                e("Big", "s s s s 0", 1),
            ],
        );
    }

    /// TNK-011: top-collapsing ACU/two-sided-AU/CUI memberships are offered outside their syntactic
    /// root. Covers recursive survivors, conditional matching, direct+collapse ordering, identity
    /// re-entry, a false-positive control, and the downstream sorted-equation value impact.
    #[test]
    fn tnk_011_collapsing_memberships_conform() {
        let source = conformance_file!("audit/B3c-membership-collapse.maude")
            .lines()
            .filter(|line| !line.starts_with("set trace"))
            .collect::<Vec<_>>()
            .join("\n");
        conform(
            &source,
            &[
                e("Special", "a", 1),             // ACU identity collapse
                e("Special", "a", 1),             // AU two-sided identity collapse
                e("Special", "a", 1),             // CUI identity collapse
                e("Special", "a * b", 2),         // child collapse + rooted membership
                e("Special", "a", 1),             // CUI idempotent collapse
                e("Special", "s a", 1),           // collapse to iter survivor
                e("Special", "s a", 1),           // conditional collapse to iter
                e("Special", "a", 1),             // recursive CUI-over-AU survivor
                e("Special", "a", 1),             // recursive CUI-over-CUI survivor
                e("Special", "a", 1),             // all-variable ordinary subject
                e("Special", "z", 1),             // all-variable identity subject
                e("E", "a", 0),                   // conservative noncollapse control
                e("Special", "a * b", 1),         // rooted ground membership still applies
                e("Low", "a", 1),                 // direct+collapse streams: smallest first
                e("E", "b", 2),                   // true sort enables sorted equation
                e("Special", "s a", 1),           // iter contains CUI collapse
                e("Special", "b * s (a + a)", 1), // CUI contains iter + nonlinear AC
                e("Special", "a", 1),             // trace module's reduction
            ],
        );
    }

    /// Phase 1.5 / C1 seam 3 — strat × membership. A custom `strat` leaves args unreduced, but Maude
    /// (and now we) still refine their TRUE SORT at the top step: the overloaded `wrap`'s result sort
    /// reflects the refined `mk(e):Sml` (→ WrS, not Wr), and `pick`'s discarded branch still has its
    /// membership counted (4 rewrites). Distinct subterms only — a repeated reducible-membership subterm
    /// was, at C1 time, the separate subject-DAG-sharing divergence (C7, since resolved).
    #[test]
    fn correctness_strat_mb_conforms() {
        conform(
            conformance_file!("correctness-strat-mb.maude"),
            &[
                e("WrS", "wrap(mk(e))", 1), // skipped arg refined → overloaded range WrS
                e("Sml", "mkA", 4), // both branches refined before selection; discarded one counts
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
                e("Big", "big", 1), // MB-REDUCIBLE: eq g(a)=big fires; mb g(X):Small never reached
                e("S", "g(b)", 2),  // MB-REWRITE-CHAIN: g(a)→g(b) [1] then g(b)'s mb [2]
                e("Big", "big", 1), // CMB-DIVERGENT: halts at big; the looping cmb condition is unreached
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
                e("P", "< b, b >", 1), // FREE subject dup: two g(a) -> one node, reduced once
                e("P", "< c, c >", 2), // deep shared chain g(g(a))->g(b)->c, once
                e("P", "< b, b >", 2), // rhs dup: f(a) [1] + shared g(a) in rhs [2]
                e("P", "< b, b >", 2), // triple subject dup: g(a) once [1] + h [2]
                e("P", "< mkA, mkA >", 1), // mb on a shared constant: fires once
                e("L", "b b", 1),      // AU: two equal elements share, reduced once
                e("L", "b b b", 1),    // AU: three equal elements
                e("E", "b & b", 1),    // CUI: two equal elements share
                e("E", "b + b", 1),    // ACU: already merges to multiplicity 2 (unchanged by C7)
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
            let Expect::Reduce {
                sort: esort,
                term: eterm,
                rewrites,
            } = exp
            else {
                panic!("conform_render handles only reduce expectations");
            };
            let parsed = parse_command_term(&loaded.modules[*m], &loaded.interner, term)
                .unwrap_or_else(|err| panic!("command {idx}: {err}"));
            let (got, rw) = reduce_command(&mut loaded.modules[*m], &loaded.interner, &parsed)
                .unwrap_or_else(|err| panic!("command {idx}: {err}"));
            let built = &loaded.modules[*m].built;
            let sort = built
                .engine
                .sorts()
                .name(built.engine.sort_of(got))
                .to_string();
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
    /// repeated-subterm sharing are separate documented residuals — C7.)
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
            format_matchers(&[
                "X --> a\nY --> b".to_string(),
                "X --> b\nY --> a".to_string()
            ]),
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

    /// General ground identities normalize identically in ACU, AU, CUI, and one-sided AU theories.
    #[test]
    fn compound_identities_conform_across_theories() {
        conform(
            "fmod ID-THEORIES is
               sort S .
               ops a b : -> S [ctor] .
               op g : S -> S [ctor] .
               op _*_ : S S -> S [assoc comm id: g(a)] .
               op cat : S S -> S [assoc id: g(a)] .
               op pair : S S -> S [comm id: g(a)] .
               op lefty : S S -> S [assoc left id: g(a)] .
               op righty : S S -> S [assoc right id: g(a)] .
             endfm
             red g(a) * b .
             red cat(g(a), b) .
             red pair(g(a), b) .
             red lefty(g(a), b) .
             red lefty(b, g(a)) .
             red righty(b, g(a)) .
             red righty(g(a), b) .",
            &[
                e("S", "b", 0),
                e("S", "b", 0),
                e("S", "b", 0),
                e("S", "b", 0),
                e("S", "lefty(b, g(a))", 0),
                e("S", "b", 0),
                e("S", "righty(g(a), b)", 0),
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

    /// Declared command variables keep their base names while the solver reorders their slots by
    /// canonical DAG traversal. The colon-token ids occur in source order here, deliberately opposite
    /// the declared base-name order.
    #[test]
    fn unify_normalization_uses_declared_variable_base_names() {
        let src = r#"
fmod BASE-NAME-ORDER is
  sort S .
  op f : S S -> S [assoc comm] .
  vars Z X Y : S .
endfm
unify f(X:S, X:S, Y:S, Y:S, Z:S) =? f(X:S, Y:S, Z:S) .
"#;
        let mut loaded = load_source(src).expect("load source");
        let (module, command) = loaded.commands.pop().expect("unify command");
        let body = match command {
            Command::Unify { body, .. } => body,
            _ => panic!("expected unify command"),
        };
        let command = unify_command(&mut loaded.modules[module], &mut loaded.interner, &body)
            .expect("build unify");
        assert_eq!(command.var_names, ["Z", "X", "Y"]);
    }

    #[test]
    fn retains_nonexec_and_bare_lhs_narrowing_rules() {
        let loaded = load_source(
            r#"
mod NARROW-METADATA is
  sort S .
  op s : S -> S .
  vars X Y : S .
  rl [step] : s(X) => X [narrowing] .
  rl [extra] : X => Y [nonexec narrowing] .
  crl [bad] : s(X) => X if X = X [narrowing] .
endm
"#,
        )
        .expect("load narrowing metadata");
        let module = &loaded.modules[0].built;
        let rules = module.engine.narrowing_rules();
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0].label.as_deref(), Some("step"));
        assert!(!rules[0].nonexec);
        assert_eq!(rules[1].label.as_deref(), Some("extra"));
        assert!(rules[1].nonexec);
        assert!(matches!(rules[1].lhs, Term::Var(_)));
        assert_eq!(rules[1].variable_names, ["X", "Y"]);
        assert_eq!(module.rl_traces.len(), 1);
        assert!(module.rl_traces[0].narrowing);
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
            (
                "acu-overload",
                conformance_file!("acu-overload.maude"),
                true,
            ),
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
                        Command::Match {
                            pattern,
                            subject,
                            xmatch,
                            ..
                        } => Cmd::Match {
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
                        let parsed =
                            parse_command_term(&loaded.modules[*m], &loaded.interner, term)
                                .unwrap_or_else(|e| panic!("{name} cmd {idx}: parse: {e}"));
                        let (result, _) =
                            reduce_command(&mut loaded.modules[*m], &loaded.interner, &parsed)
                                .unwrap_or_else(|e| panic!("{name} cmd {idx}: reduce: {e}"));
                        if round_trip {
                            let printed =
                                print_raw(&loaded.modules[*m].built, &loaded.interner, result);
                            let toks = tokenize(&printed, &mut loaded.interner);
                            let reparsed_term =
                                parse_command_term(&loaded.modules[*m], &loaded.interner, &toks)
                                    .unwrap_or_else(|e| {
                                        panic!("{name} cmd {idx} reparse `{printed}`: {e}")
                                    });
                            let (reparsed, _) = reduce_command(
                                &mut loaded.modules[*m],
                                &loaded.interner,
                                &reparsed_term,
                            )
                            .unwrap_or_else(|e| {
                                panic!("{name} cmd {idx} reparse `{printed}`: {e}")
                            });
                            let eng = &loaded.modules[*m].built.engine;
                            assert!(
                                eng.deep_equal(result, reparsed),
                                "{name} cmd {idx}: `{printed}` did not round-trip"
                            );
                        }
                    }
                    Cmd::Match {
                        pattern,
                        subject,
                        xmatch,
                    } => {
                        match_command(
                            &mut loaded.modules[*m],
                            &loaded.interner,
                            pattern,
                            subject,
                            *xmatch,
                        )
                        .unwrap_or_else(|e| panic!("{name} cmd {idx}: match: {e}"));
                    }
                }
            }
        }
    }

    #[test]
    fn parse_effort_limit_is_deterministic() {
        let mut loaded = load_source(
            "fmod EFFORT-LIMIT is
               sort S .
               op a : -> S [ctor] .
               op _+_ : S S -> S [assoc comm] .
             endfm",
        )
        .expect("load effort grammar");
        let text = std::iter::repeat_n("a", 200)
            .collect::<Vec<_>>()
            .join(" + ");
        let tokens = tokenize(&text, &mut loaded.interner);
        let mut first_error = None;
        for _ in 0..2 {
            let mut effort = ParseEffort::new(1_000);
            let error = parse_forest_any_with_effort(
                &tokens,
                &loaded.modules[0].grammar,
                &loaded.interner,
                &mut effort,
            )
            .expect_err("small explicit budget must reject");
            assert_eq!(effort.used(), 1_000);
            assert!(
                error.starts_with("parse effort limit exceeded at token "),
                "{error}"
            );
            if let Some(first) = &first_error {
                assert_eq!(&error, first);
            } else {
                first_error = Some(error);
            }
        }
    }

    #[test]
    fn forest_extraction_shares_recognizer_budget() {
        let mut loaded = load_source(
            "fmod FOREST-EFFORT is
               sort S .
               op a : -> S [ctor] .
               op _+_ : S S -> S [assoc comm] .
             endfm",
        )
        .expect("load forest effort grammar");
        let text = std::iter::repeat_n("a", 20).collect::<Vec<_>>().join(" + ");
        let tokens = tokenize(&text, &mut loaded.interner);
        let grammar = &loaded.modules[0].grammar;

        let mut recognition = ParseEffort::new(u64::MAX);
        earley::parse(
            grammar,
            &tokens,
            Nt::Term,
            &loaded.interner,
            &mut recognition,
        )
        .expect("recognize term");
        let recognition_cost = recognition.used();

        let mut shared = ParseEffort::new(recognition_cost);
        let error = parse_forest_any_with_effort(&tokens, grammar, &loaded.interner, &mut shared)
            .expect_err("forest must not receive a fresh budget");
        assert_eq!(shared.used(), recognition_cost);
        assert!(
            error.starts_with(&format!(
                "parse effort limit exceeded at token {} (`<end>`)",
                tokens.len()
            )),
            "{error}"
        );
    }

    /// Opt-in TNK-016 scaling benchmark. Both inputs deliberately exceed the interactive safety budget so
    /// parser algorithm changes can still be compared without weakening that availability boundary.
    #[test]
    #[ignore = "opt-in large-grammar parser benchmark"]
    fn large_grammar_valid_and_invalid_parse_benchmark() {
        let mut source = String::from("fmod EFFORT is\n sort S .\n op a : -> S [ctor] .\n");
        for index in 0..1000 {
            source.push_str(&format!(" op _o{index}_ : S S -> S [assoc] .\n"));
        }
        source.push_str("endfm\n");
        let mut loaded = load_source(&source).expect("load generated grammar");
        let mut text = String::from("a");
        for _ in 1..1280 {
            text.push_str(" o0 a");
        }

        let valid = tokenize(&text, &mut loaded.interner);
        let mut valid_effort = ParseEffort::new(u64::MAX);
        parse_forest_any_with_effort(
            &valid,
            &loaded.modules[0].grammar,
            &loaded.interner,
            &mut valid_effort,
        )
        .expect("valid benchmark term");
        assert!(valid_effort.used() > crate::cfparser::DEFAULT_PARSE_EFFORT_LIMIT);

        let invalid = tokenize(&format!("{text} o0 bogus"), &mut loaded.interner);
        let mut invalid_effort = ParseEffort::new(u64::MAX);
        let error = parse_forest_any_with_effort(
            &invalid,
            &loaded.modules[0].grammar,
            &loaded.interner,
            &mut invalid_effort,
        )
        .expect_err("invalid benchmark term");
        assert!(
            error.starts_with("no parse at token 2560 (`bogus`)"),
            "{error}"
        );
        assert!(invalid_effort.used() > crate::cfparser::DEFAULT_PARSE_EFFORT_LIMIT);
    }

    #[test]
    fn two_thousand_atom_flat_command_fits_parse_budget() {
        let mut loaded = load_source(
            "fmod D3 is
               sort S .
               op 1 : -> S [ctor] .
               op _+_ : S S -> S [assoc comm] .
             endfm",
        )
        .expect("load D3 grammar");
        let text = std::iter::repeat_n("1", 2000)
            .collect::<Vec<_>>()
            .join(" + ");
        let tokens = tokenize(&text, &mut loaded.interner);
        parse_command_term(&loaded.modules[0], &loaded.interner, &tokens)
            .expect("retained 2,000-atom command must remain below the parser budget");
    }
}
