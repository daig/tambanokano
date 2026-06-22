//! Loading: drive a whole `.maude` source end-to-end. Surface-parse it, then for each module build the
//! signature ([`build_module`]), the mixfix grammar ([`build_grammar`]), and add its parsed statements;
//! commands are run against the module they follow (Maude's current module). The B4.4c entry point and
//! the basis for the B5 REPL.
//!
//! Scope (B4.4c milestone): unconditional `eq`/`mb` and the `reduce` command. Conditional statements
//! (`ceq`/`cmb`/condition fragments), `owise` conditions, and the `match` command are deferred to B4.5
//! (their kernel facades and the build_term machinery already exist; only the condition-bubble parse is
//! missing).

use crate::build_term::{build_dag, build_term, VarIndex};
use crate::cfparser::compile::CompiledGrammar;
use crate::cfparser::forest::PTree;
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
use tnk_core::term::{Equation, Membership, Term};

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

/// Parse a term token bubble to its (unambiguous) parse tree; rejects empty input, no-parse, and ambiguity.
fn parse_forest(tokens: &[Token], g: &CompiledGrammar, i: &Interner) -> Result<PTree, String> {
    if tokens.is_empty() {
        return Err("empty term".into());
    }
    let chart = earley::parse(g, tokens, Nt::Term, i);
    let parsed = forest::extract(g, &chart, tokens.len(), Nt::Term)?;
    if parsed.ambiguous {
        return Err("ambiguous parse".into());
    }
    Ok(parsed.tree)
}

/// Parse a term token bubble and build its kernel [`Term`] (the statement/pattern path).
fn parse_build(
    tokens: &[Token],
    g: &CompiledGrammar,
    m: &BuiltModule,
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    build_term(&parse_forest(tokens, g, i)?, g, m, tokens, i, vars)
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

/// Parse, build, and reduce a ground command term; returns `(result, rewrite count)`. Builds the term
/// directly as a DAG ([`build_dag`]) so built-in literals (string/qid/float) and compact numerals work.
pub fn reduce_command(
    lm: &mut LoadedModule,
    i: &Interner,
    term: &[Token],
) -> Result<(DagId, u64), String> {
    let tree = parse_forest(term, &lm.grammar, i)?;
    // Reset BEFORE building: construction applies membership axioms (`constrain_to_smaller_sort` counts as
    // a rewrite — Maude's accounting), so those rewrites belong to this command's count.
    lm.built.engine.reset_rewrites();
    let dag = build_dag(&tree, &lm.grammar, &mut lm.built.engine, lm.built.nat_zero, term, i)?;
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

    #[test]
    fn overload_conforms() {
        // Command 8 is a kind-level (error-sort) result. COSMETIC NAMING DIVERGENCE (task #8, like the ACU
        // order #7): the kernel names a kind's error sort `[<first-declared member>]` = `[Zero]`, whereas
        // Maude names it after a maximal sort = `[Nat]`. Same kind, semantically irrelevant; we assert our
        // `[Zero]`. (overload.maude is the non-preregular module; Maude also warns on preregularity, which we
        // don't surface yet — B2.1's deferred diagnostics sink — but the reduced results/sorts still match.)
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
                e("[Zero]", "0 + 0", 0),
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
                Command::Reduce { term } => (*m, term.clone()),
                Command::Match { .. } => panic!("milestone uses only reduce"),
            })
            .collect();
        assert_eq!(cmds.len(), expected.len(), "command count");
        for (idx, ((m, term), exp)) in cmds.iter().zip(expected).enumerate() {
            let (got, rw) = reduce_command(&mut loaded.modules[*m], &loaded.interner, term)
                .unwrap_or_else(|err| panic!("command {idx}: {err}"));
            let built = &loaded.modules[*m].built;
            let sort = built.engine.sorts().name(built.engine.sort_of(got)).to_string();
            assert_eq!(sort, exp.sort, "command {idx} sort");
            assert_eq!(rw, exp.rewrites, "command {idx} rewrites");
            let printed = crate::pretty::print_pretty(built, &loaded.interner, got, false);
            assert_eq!(printed, exp.term, "command {idx} printed value");
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

    #[test]
    fn rat_conforms() {
        // Rationals have no ACU-order issue, but `_/_` prints with spaces here (`3 / 4`) vs the binary's
        // `3/4`, so compare by value (deep_equal), not text.
        conform(
            conformance_file!("rat.maude"),
            &[
                e("NzNat", "2", 1),
                e("NzRat", "3 / 4", 1),
                e("NzRat", "3 / 2", 1),
                e("NzRat", "- 3 / 2", 1),
                e("NzNat", "5", 1),
                e("NzRat", "3 / 4", 0),
                e("Rat", "0 / 5", 0),
            ],
        );
    }
}
