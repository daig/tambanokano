//! Loading: drive a whole `.maude` source end-to-end. Surface-parse it, then for each module build the
//! signature ([`build_module`]), the mixfix grammar ([`build_grammar`]), and add its parsed statements;
//! commands are run against the module they follow (Maude's current module). The B4.4c entry point and
//! the basis for the B5 REPL.
//!
//! Scope (B4.4c milestone): unconditional `eq`/`mb` and the `reduce` command. Conditional statements
//! (`ceq`/`cmb`/condition fragments), `owise` conditions, and the `match` command are deferred to B4.5
//! (their kernel facades and the build_term machinery already exist; only the condition-bubble parse is
//! missing).

use crate::build_term::{build_term, VarIndex};
use crate::cfparser::compile::CompiledGrammar;
use crate::cfparser::{earley, forest};
use crate::grammar::build::build_grammar;
use crate::grammar::Nt;
use crate::lex::{tokenize, Interner, Token};
use crate::sig::build_sig::build_module;
use crate::sig::syntax::BuiltModule;
use crate::surface::ast::{Command, PreModule, Source, Statement};
use crate::surface::parser::Parser;
use tnk_core::dag::DagId;
use tnk_core::sort::SortId;
use tnk_core::term::{Equation, Membership, Subst, Term};

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

/// Surface-parse `src`, then build every module (signature + grammar + statements).
pub fn load_source(src: &str) -> Result<Loaded, String> {
    let mut interner = Interner::new();
    let toks = tokenize(src, &mut interner);
    let Source { modules: pre, commands } = Parser::new(&toks, &interner).parse_source()?;

    let mut modules = Vec::with_capacity(pre.len());
    for pm in &pre {
        let mut built = build_module(pm, &mut interner)?;
        let grammar = CompiledGrammar::compile(&build_grammar(&built, &mut interner));
        load_statements(pm, &mut built, &grammar, &interner)?;
        modules.push(LoadedModule { built, grammar });
    }
    Ok(Loaded { interner, modules, commands })
}

/// Parse + build + add each of the module's statement bubbles to the engine.
fn load_statements(
    pm: &PreModule,
    m: &mut BuiltModule,
    g: &CompiledGrammar,
    i: &Interner,
) -> Result<(), String> {
    for stmt in &pm.statements {
        match stmt {
            Statement::Eq { lhs, rhs, cond, owise } => {
                if cond.is_some() {
                    return Err("conditional equations (ceq) are deferred to B4.5".into());
                }
                let mut vars = VarIndex::new();
                let lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
                let rhs_t = parse_build(rhs, g, m, i, &mut vars)?;
                let nr = vars.count();
                if *owise {
                    m.engine.add_owise_equation(lhs_t, rhs_t, nr, Vec::new());
                } else {
                    m.engine.add_equation(Equation { lhs: lhs_t, rhs: rhs_t, nr_vars: nr });
                }
            }
            Statement::Mb { lhs, sort, cond } => {
                if cond.is_some() {
                    return Err("conditional memberships (cmb) are deferred to B4.5".into());
                }
                let mut vars = VarIndex::new();
                let lhs_t = parse_build(lhs, g, m, i, &mut vars)?;
                let sort_id = resolve_sort(sort, m, i)?;
                m.engine.add_membership(Membership { lhs: lhs_t, sort: sort_id, nr_vars: vars.count() });
            }
        }
    }
    Ok(())
}

/// Parse a term token bubble and build its kernel [`Term`]; rejects no-parse and (for now) ambiguity.
fn parse_build(
    tokens: &[Token],
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    if tokens.is_empty() {
        return Err("empty term".into());
    }
    let chart = earley::parse(g, tokens, Nt::Term, i);
    let parsed = forest::extract(g, &chart, tokens.len(), Nt::Term)?;
    if parsed.ambiguous {
        return Err("ambiguous parse".into());
    }
    build_term(&parsed.tree, g, m, tokens, i, vars)
}

/// Resolve a sort token bubble to a [`SortId`] (single token only; structured sorts are B4.5).
fn resolve_sort(tokens: &[Token], m: &BuiltModule, i: &Interner) -> Result<SortId, String> {
    match tokens {
        [t] => m
            .sorts
            .get(t.text(i))
            .copied()
            .ok_or_else(|| format!("unknown sort `{}`", t.text(i))),
        _ => Err("structured sort in membership: B4.5".into()),
    }
}

/// Parse, build, and reduce a ground command term; returns `(result, rewrite count)`.
pub fn reduce_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &[Token],
) -> Result<(DagId, u64), String> {
    let mut vars = VarIndex::new();
    let t = parse_build(term, &lm.grammar, &lm.built, i, &mut vars)?;
    if vars.count() != 0 {
        return Err("a reduce-command term must be ground".into());
    }
    let mut subst = Subst::new();
    subst.reset(0);
    let dag = lm.built.engine.instantiate(&t, &subst);
    lm.built.engine.reset_rewrites();
    let result = lm.built.engine.reduce(dag);
    Ok((result, lm.built.engine.rewrites()))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One expected command result, transcribed from the reference binary:
    /// `~/Downloads/Maude-3/maude -no-banner conformance/<file>.maude < /dev/null`.
    /// `(result-sort, an expected-term in surface syntax, rewrite-count)`. The expected term is reduced
    /// through the same pipeline and compared by `deep_equal`, so its surface form just has to denote the
    /// same value (e.g. `- 3` for the binary's `-3`, `s s 0` for `s_^2(0)`).
    struct Expect {
        sort: &'static str,
        term: &'static str,
        rewrites: u64,
    }

    const fn e(sort: &'static str, term: &'static str, rewrites: u64) -> Expect {
        Expect { sort, term, rewrites }
    }

    /// Load `src`, run each `reduce` command, and assert its result sort, rewrite count, and value match
    /// the reference binary (the value via reducing `expected[k].term` through the same pipeline).
    fn conform(src: &str, expected: &[Expect]) {
        let mut loaded = load_source(src).expect("load source");
        let cmds: Vec<(usize, Vec<Token>)> = loaded
            .commands
            .iter()
            .map(|(m, c)| match c {
                Command::Reduce { term } => (*m, term.clone()),
                Command::Match { .. } => panic!("milestone modules use only `reduce`"),
            })
            .collect();
        assert_eq!(cmds.len(), expected.len(), "command count");

        for (idx, ((m, term), exp)) in cmds.iter().zip(expected).enumerate() {
            let (got, rw) = reduce_command(&mut loaded.modules[*m], &loaded.interner, term)
                .unwrap_or_else(|err| panic!("command {idx}: {err}"));
            {
                let eng = &loaded.modules[*m].built.engine;
                assert_eq!(eng.sorts().name(eng.sort_of(got)), exp.sort, "command {idx} sort");
            }
            assert_eq!(rw, exp.rewrites, "command {idx} rewrite count");

            let exp_toks = tokenize(exp.term, &mut loaded.interner);
            let (want, _) = reduce_command(&mut loaded.modules[*m], &loaded.interner, &exp_toks)
                .unwrap_or_else(|err| panic!("command {idx} expected `{}`: {err}", exp.term));
            let eng = &loaded.modules[*m].built.engine;
            assert!(eng.deep_equal(got, want), "command {idx} value: expected `{}`", exp.term);
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
}
