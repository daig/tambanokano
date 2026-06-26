//! `load_program`: drive a whole `.maude` source through the module system — parse, build the module
//! database, flatten each module's import closure, and build each into a runnable [`LoadedModule`].
//!
//! This is the import-aware counterpart of the frontend's `load_source` (which rejects imports). It is
//! the entry the B5 REPL consumes next round: load a file, hold the [`Program`] (modules + the command
//! list + a name→index map), and run commands against the current module.

use std::collections::HashMap;
use tnk_frontend::lex::{tokenize, Interner};
use tnk_frontend::load::{build_loaded_module, LoadedModule};
use tnk_frontend::surface::ast::{Command, Source};
use tnk_frontend::surface::parser::Parser;

use crate::db::ModuleDb;
use crate::flatten::flatten;
use crate::view::{validate_view, ViewDb};

/// A loaded program: the shared interner, every module **flattened** (one [`LoadedModule`] per top-level
/// `fmod`, in file order), a name→index map (for the REPL's `select`), the validated views (B-ii), and the
/// commands tagged with the index of the module they run against (the most recently entered one).
pub struct Program {
    pub interner: Interner,
    pub modules: Vec<LoadedModule>,
    pub module_index: HashMap<String, usize>,
    pub views: ViewDb,
    pub commands: Vec<(usize, Command)>,
}

/// Parse `src`, flatten every module's import closure, and build each. A module with no imports flattens
/// to itself, so this loader handles import-free files too.
pub fn load_program(src: &str) -> Result<Program, String> {
    let mut interner = Interner::new();
    let toks = tokenize(src, &mut interner);
    let Source { modules: pre, views: pre_views, commands } =
        Parser::new(&toks, &interner).parse_source()?;

    // Names in file order (the command-index basis), and the database for import resolution.
    let names: Vec<String> = pre.iter().map(|m| m.name.clone()).collect();
    let db = ModuleDb::from_modules(pre);

    // Views first (B-ii): validate each against the module DB, then store — so a parameterized
    // instantiation `M{V}` reached while flattening a module can resolve its view (B-iv). A bad view aborts
    // the load with the reference binary's diagnostic.
    let mut views = ViewDb::new();
    for v in pre_views {
        validate_view(&v, &db, &mut interner)?;
        views.insert(v);
    }

    // Then flatten + build each module (instantiations resolve against `views`).
    let mut modules = Vec::with_capacity(names.len());
    let mut module_index = HashMap::new();
    for (idx, name) in names.iter().enumerate() {
        let flat = flatten(name, &db, &views, &mut interner)?;
        modules.push(build_loaded_module(&flat, &mut interner)?);
        module_index.insert(name.clone(), idx);
    }
    Ok(Program { interner, modules, module_index, views, commands })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tnk_frontend::lex::{tokenize, Token};
    use tnk_frontend::load::reduce_command;
    use tnk_frontend::pretty::print_raw;

    /// One expected `reduce` result, transcribed from the reference binary:
    /// `~/Downloads/Maude-3/maude -no-banner conformance/import-<name>.maude < /dev/null`.
    /// `(result-sort, an expected-term in surface syntax, rewrite-count)`; the expected term is reduced
    /// through the same flattened module and compared by `deep_equal`.
    struct Expect {
        sort: &'static str,
        term: &'static str,
        rewrites: u64,
    }
    const fn e(sort: &'static str, term: &'static str, rewrites: u64) -> Expect {
        Expect { sort, term, rewrites }
    }

    /// Load a multi-module `.maude` program through the module system and assert each `reduce` command's
    /// result sort, rewrite count, and value match the reference binary — and that the printed result
    /// round-trips (`parse∘print_raw = id`) against the flattened module's grammar.
    fn conform(src: &str, expected: &[Expect]) {
        let mut prog = load_program(src).expect("load program");
        let cmds: Vec<(usize, Vec<Token>)> = prog
            .commands
            .iter()
            .map(|(m, c)| match c {
                Command::Reduce { term } => (*m, term.clone()),
                _ => panic!("import conformance uses only `reduce`"),
            })
            .collect();
        assert_eq!(cmds.len(), expected.len(), "command count");

        for (idx, ((m, term), exp)) in cmds.iter().zip(expected).enumerate() {
            let (got, rw) = reduce_command(&mut prog.modules[*m], &prog.interner, term)
                .unwrap_or_else(|err| panic!("command {idx}: {err}"));
            {
                let eng = &prog.modules[*m].built.engine;
                assert_eq!(eng.sorts().name(eng.sort_of(got)), exp.sort, "command {idx} sort");
            }
            assert_eq!(rw, exp.rewrites, "command {idx} rewrite count");

            // Value: reduce the expected surface term through the same module and compare.
            let exp_toks = tokenize(exp.term, &mut prog.interner);
            let (want, _) = reduce_command(&mut prog.modules[*m], &prog.interner, &exp_toks)
                .unwrap_or_else(|err| panic!("command {idx} expected `{}`: {err}", exp.term));
            {
                let eng = &prog.modules[*m].built.engine;
                assert!(eng.deep_equal(got, want), "command {idx} value: expected `{}`", exp.term);
            }

            // Round-trip: the printed result re-parses to the same term.
            let printed = print_raw(&prog.modules[*m].built, &prog.interner, got);
            let toks = tokenize(&printed, &mut prog.interner);
            let (reparsed, _) = reduce_command(&mut prog.modules[*m], &prog.interner, &toks)
                .unwrap_or_else(|err| panic!("command {idx} reparse `{printed}`: {err}"));
            let eng = &prog.modules[*m].built.engine;
            assert!(eng.deep_equal(got, reparsed), "command {idx}: `{printed}` did not round-trip");
        }
    }

    macro_rules! conformance_file {
        ($name:expr) => {
            include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../conformance/", $name))
        };
    }

    /// `protecting` a base module; commands use both the imported and the new signatures.
    #[test]
    fn import_protecting_conforms() {
        conform(
            conformance_file!("import-protecting.maude"),
            &[
                e("N", "s(s(s(s(0))))", 4),                   // double(2) = 4
                e("N", "s(s(s(s(s(s(s(0)))))))", 7),          // 1 + double(3) = 7
            ],
        );
    }

    /// protecting / extending / including all flatten identically — the same `d(2) = 4` in three modules.
    #[test]
    fn import_modes_conforms() {
        conform(
            conformance_file!("import-modes.maude"),
            &[e("N", "s(s(s(s(0))))", 4), e("N", "s(s(s(s(0))))", 4), e("N", "s(s(s(s(0))))", 4)],
        );
    }

    /// Diamond import: `TOP` imports `LEFT` and `RIGHT`, both protecting `BASE` — `BASE` included once,
    /// so `combine(1) = 2·1 + 3·1 = 5` with the binary's exact rewrite count.
    #[test]
    fn import_diamond_conforms() {
        conform(conformance_file!("import-diamond.maude"), &[e("N", "s(s(s(s(s(0)))))", 12)]);
    }

    /// Module summation `A + B`: the importer sees both signatures.
    #[test]
    fn import_summation_conforms() {
        conform(
            conformance_file!("import-summation.maude"),
            &[e("SA", "a2", 1), e("SB", "b2", 1)],
        );
    }

    /// Renaming `* (sort Elt to Item, op wrap to box)` — the renamed sort is the result sort and the
    /// renamed op fires inside the equation (`wrap(X)=X` became `box(X)=X`): `top(e) = box(e) = e`.
    #[test]
    fn import_renaming_conforms() {
        conform(
            conformance_file!("import-renaming.maude"),
            &[e("Item", "e", 2), e("Item", "e", 1)],
        );
    }

    /// B-i: a theory (`fth`) builds its signature like a module, but a `[nonexec]` axiom is a proof
    /// obligation that is never applied (`e < e` stays, 0 rewrites) while an ordinary theory equation does
    /// fire (`id(e) = e`, 1 rewrite). Differentially verified against the reference binary.
    #[test]
    fn theory_nonexec_conforms() {
        conform(
            conformance_file!("theory-nonexec.maude"),
            &[e("Bool", "e < e", 0), e("Elt", "e", 1)],
        );
    }

    /// B-i: a theory flattens its `protecting`/`including` imports exactly as a module does — `TINY`'s
    /// equation `neg(t) = f` fires inside the theory `ORD` that protects it.
    #[test]
    fn theory_import_conforms() {
        conform(
            conformance_file!("theory-import.maude"),
            &[e("B", "f", 1), e("B", "t", 2)],
        );
    }

    /// B-ii: a file carrying a *valid* view loads end-to-end — the view is validated and stored, and the
    /// target module's reduces are unaffected (`p(s(z)) = z`). The view itself is exercised in B-iv.
    #[test]
    fn view_good_conforms() {
        conform(conformance_file!("view-good.maude"), &[e("N", "z", 1), e("N", "s(z)", 1)]);
    }

    /// B-iii: a parameterized module `fmod CTR{X :: TRIV}` builds and reduces ground terms. The parameter
    /// copy turns the theory sort `Elt` into the parameter sort `X$Elt`; structured sorts `Ctr{X}` /
    /// `NzCtr{X}` (and the subsort between them) drive the least-sort results. Byte-identical to the binary.
    #[test]
    fn param_module_conforms() {
        conform(
            conformance_file!("param-module.maude"),
            &[
                e("Ctr{X}", "zero", 1),
                e("NzCtr{X}", "inc(inc(zero))", 3),
                e("NzCtr{X}", "inc(zero)", 1),
            ],
        );
    }

    /// B-iv: parameterized-module instantiation `M{V}`. The single-parameter `BOX{ToColor}` substitutes
    /// the parameter sort (`X$Elt ↦ Hue`) and names structured sorts (`Box{X} ↦ Box{ToColor}`), importing
    /// the view's target; the multi-parameter `PR{VA, VB}` binds each parameter independently. All four
    /// results/sorts/counts are byte-identical to the reference binary.
    #[test]
    fn instantiation_conforms() {
        conform(
            conformance_file!("instantiation.maude"),
            &[
                e("Hue", "red", 1),
                e("Box{ToColor}", "wrap(green)", 1),
                e("Hue", "green", 2),
                e("SA", "a", 1),
            ],
        );
    }

    /// Axis-A3: a parameterized module `protecting`s the same module its instantiating view targets — the
    /// shared module is merged exactly once (the flatten visited-set), so a membership it carries is not
    /// double-counted (3 rewrites, not inflated). Byte-identical to the binary; no new engine code (the
    /// pre-existing dedup already handles it — this pins it as a regression guard).
    #[test]
    fn param_shared_import_conforms() {
        conform(
            conformance_file!("param-shared-import.maude"),
            &[e("NzN", "s(s(z))", 3), e("NzN", "s(s(s(z)))", 3)],
        );
    }

    /// B-ii: a view whose sort map targets a non-existent sort fails to load, with the reference binary's
    /// `failed to find sort … in … to represent …` diagnostic.
    #[test]
    fn bad_view_rejected_by_load() {
        let src = "fth TRIV is sort Elt . endfth\n\
                   fmod NUM is sort N . endfm\n\
                   view Bad from TRIV to NUM is sort Elt to NoSuch . endv\n";
        let err = match load_program(src) {
            Err(e) => e,
            Ok(_) => panic!("expected the bad view to be rejected"),
        };
        assert!(err.contains("failed to find sort NoSuch in NUM"), "got: {err}");
    }
}
