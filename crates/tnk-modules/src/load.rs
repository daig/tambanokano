//! `load_program`: drive a whole `.maude` source through the module system — parse, build the module
//! database, flatten each module's import closure, and build each into a runnable [`LoadedModule`].
//!
//! This is the import-aware counterpart of the frontend's `load_source` (which rejects imports). It is
//! the entry the B5 REPL consumes next round: load a file, hold the [`Program`] (modules + the command
//! list + a name→index map), and run commands against the current module.

use std::collections::{HashMap, HashSet};
use tnk_frontend::lex::{Interner, tokenize};
use tnk_frontend::load::{LoadedModule, build_loaded_module_homed};
use tnk_frontend::surface::ast::{Command, ModuleExpr, PreModule, Source, ViewDecl};
use tnk_frontend::surface::parser::Parser;

use crate::db::ModuleDb;
use crate::flatten::flatten_with_homes;
use crate::view::{ViewDb, validate_view};

/// Flatten `name`'s import closure and build it into a runnable [`LoadedModule`], applying the **D1a
/// import-reparse point-fix**: a statement the flattened grammar parses ambiguously is re-parsed against
/// its home module's own grammar. `home_mod` resolves an imported statement's home name to its
/// already-built module (the caller's module cache — `load_program`'s in-progress map, or the REPL's
/// `modules`); a home not found there simply keeps the flattened-grammar behavior. This is the single
/// entry both `load_program` and the REPL use to build an import-aware module.
pub fn flatten_and_build<'m>(
    name: &str,
    db: &ModuleDb,
    views: &ViewDb,
    home_mod: &dyn Fn(&str) -> Option<&'m LoadedModule>,
    interner: &mut Interner,
) -> Result<LoadedModule, String> {
    let (flat, homes) = flatten_with_homes(name, db, views, interner)?;
    build_loaded_module_homed(&flat, &homes, home_mod, interner)
}

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

/// Collect every module/view name a module expression references — the bases and arguments of imports,
/// summations `A + B`, renamings `M * (…)`, and instantiations `M{V, …}`. This is the dependency-tracking
/// support for redefinition invalidation (A4c): it deliberately **over-approximates** — an instantiation
/// argument that is really an enclosing parameter is captured too (harmless: it won't match a defined
/// name), and a view name used as an instantiation argument is captured (so redefining a view re-flattens
/// its users). Over-approximation can only cause an extra (semantically invisible) rebuild, never a missed
/// one.
fn collect_expr_names(e: &ModuleExpr, out: &mut HashSet<String>) {
    match e {
        ModuleExpr::Named(n) => {
            out.insert(n.clone());
        }
        ModuleExpr::Sum(a, b) => {
            collect_expr_names(a, out);
            collect_expr_names(b, out);
        }
        ModuleExpr::Rename(inner, _) => collect_expr_names(inner, out),
        ModuleExpr::Instantiation(base, args) => {
            collect_expr_names(base, out);
            for a in args {
                collect_expr_names(a, out);
            }
        }
    }
}

/// The direct module/view dependencies of a module: every name mentioned in its imports plus its parameter
/// theories. The module's own name and its formal-parameter names are excluded (a parameter is bound
/// locally, not a dependency). Used to invalidate cached dependents when a module/view is redefined (A4c).
pub fn module_dep_names(pm: &PreModule) -> HashSet<String> {
    let mut out = HashSet::new();
    for p in &pm.params {
        out.insert(p.theory.clone());
    }
    for imp in &pm.imports {
        collect_expr_names(&imp.expr, &mut out);
    }
    for p in &pm.params {
        out.remove(&p.name);
    }
    out.remove(&pm.name);
    out
}

/// The direct module/view dependencies of a view: its `from` source theory, its `to` target module
/// expression, and any parameter theories. Its own name and formal-parameter names are excluded. Used to
/// invalidate cached dependents when a view is redefined (A4c).
pub fn view_dep_names(v: &ViewDecl) -> HashSet<String> {
    let mut out = HashSet::new();
    for p in &v.params {
        out.insert(p.theory.clone());
    }
    collect_expr_names(&v.from, &mut out);
    collect_expr_names(&v.to, &mut out);
    for p in &v.params {
        out.remove(&p.name);
    }
    out.remove(&v.name);
    out
}

/// Parse `src`, flatten every module's import closure, and build each. A module with no imports flattens
/// to itself, so this loader handles import-free files too.
pub fn load_program(src: &str) -> Result<Program, String> {
    let mut interner = Interner::new();
    let toks = tokenize(src, &mut interner);
    let Source {
        modules: pre,
        views: pre_views,
        commands,
    } = Parser::new(&toks, &interner).parse_source()?;

    // Names in file order (the command-index basis), and the database for import resolution.
    let names: Vec<String> = pre.iter().map(|m| m.name.clone()).collect();
    let mut db = ModuleDb::from_modules(pre);

    // Views first (B-ii): validate each against the module DB, then store — so a parameterized
    // instantiation `M{V}` reached while flattening a module can resolve its view (B-iv). A bad view aborts
    // the load with the reference binary's diagnostic.
    let mut views = ViewDb::new();
    for v in pre_views {
        validate_view(&v, &db, &views, &mut interner)?;
        views.insert(v);
    }

    // Then flatten + build each module (instantiations resolve against `views`). Before each flatten,
    // inject any built-in prelude module the module imports (e.g. an `omod`'s auto-imported
    // `CONFIGURATION`) that the user has not defined — in file order, so an imported module's own
    // built-in needs are satisfied by the time a later importer is flattened.
    let mut modules: Vec<LoadedModule> = Vec::with_capacity(names.len());
    let mut module_index: HashMap<String, usize> = HashMap::new();
    for (idx, name) in names.iter().enumerate() {
        let imports = db
            .get(name)
            .map(|pm| pm.imports.clone())
            .unwrap_or_default();
        crate::prelude::ensure_builtins(&imports, &mut db, &mut interner);
        // Resolve an imported statement's home to its already-built module (built earlier in file order —
        // imports precede importers in a well-formed file). Scoped to a block so the immutable borrows of
        // `modules`/`module_index` end before this module is pushed.
        let lm = {
            let built = &modules;
            let built_ix = &module_index;
            let home_mod = |n: &str| built_ix.get(n).map(|&ix| &built[ix]);
            flatten_and_build(name, &db, &views, &home_mod, &mut interner)?
        };
        module_index.insert(name.clone(), idx);
        modules.push(lm);
    }
    Ok(Program {
        interner,
        modules,
        module_index,
        views,
        commands,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tnk_frontend::lex::{Token, tokenize};
    use tnk_frontend::load::{parse_command_term, reduce_command};
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
        Expect {
            sort,
            term,
            rewrites,
        }
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
                Command::Reduce { term, .. } => (*m, term.clone()),
                _ => panic!("import conformance uses only `reduce`"),
            })
            .collect();
        assert_eq!(cmds.len(), expected.len(), "command count");

        for (idx, ((m, term), exp)) in cmds.iter().zip(expected).enumerate() {
            let parsed = parse_command_term(&prog.modules[*m], &prog.interner, term)
                .unwrap_or_else(|err| panic!("command {idx}: {err}"));
            let (got, rw) = reduce_command(&mut prog.modules[*m], &prog.interner, &parsed)
                .unwrap_or_else(|err| panic!("command {idx}: {err}"));
            {
                let eng = &prog.modules[*m].built.engine;
                assert_eq!(
                    eng.sorts().name(eng.sort_of(got)),
                    exp.sort,
                    "command {idx} sort"
                );
            }
            assert_eq!(rw, exp.rewrites, "command {idx} rewrite count");

            // Value: reduce the expected surface term through the same module and compare.
            let exp_toks = tokenize(exp.term, &mut prog.interner);
            let expected_parsed = parse_command_term(&prog.modules[*m], &prog.interner, &exp_toks)
                .unwrap_or_else(|err| panic!("command {idx} expected `{}`: {err}", exp.term));
            let (want, _) = reduce_command(&mut prog.modules[*m], &prog.interner, &expected_parsed)
                .unwrap_or_else(|err| panic!("command {idx} expected `{}`: {err}", exp.term));
            {
                let eng = &prog.modules[*m].built.engine;
                assert!(
                    eng.deep_equal(got, want),
                    "command {idx} value: expected `{}`",
                    exp.term
                );
            }

            // Round-trip: the printed result re-parses to the same term.
            let printed = print_raw(&prog.modules[*m].built, &prog.interner, got);
            let toks = tokenize(&printed, &mut prog.interner);
            let reparsed_term = parse_command_term(&prog.modules[*m], &prog.interner, &toks)
                .unwrap_or_else(|err| panic!("command {idx} reparse `{printed}`: {err}"));
            let (reparsed, _) =
                reduce_command(&mut prog.modules[*m], &prog.interner, &reparsed_term)
                    .unwrap_or_else(|err| panic!("command {idx} reparse `{printed}`: {err}"));
            let eng = &prog.modules[*m].built.engine;
            assert!(
                eng.deep_equal(got, reparsed),
                "command {idx}: `{printed}` did not round-trip"
            );
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

    /// `protecting` a base module; commands use both the imported and the new signatures.
    #[test]
    fn import_protecting_conforms() {
        conform(
            conformance_file!("import-protecting.maude"),
            &[
                e("N", "s(s(s(s(0))))", 4),          // double(2) = 4
                e("N", "s(s(s(s(s(s(s(0)))))))", 7), // 1 + double(3) = 7
            ],
        );
    }

    /// protecting / extending / including all flatten identically — the same `d(2) = 4` in three modules.
    #[test]
    fn import_modes_conforms() {
        conform(
            conformance_file!("import-modes.maude"),
            &[
                e("N", "s(s(s(s(0))))", 4),
                e("N", "s(s(s(s(0))))", 4),
                e("N", "s(s(s(s(0))))", 4),
            ],
        );
    }

    /// Diamond import: `TOP` imports `LEFT` and `RIGHT`, both protecting `BASE` — `BASE` included once,
    /// so `combine(1) = 2·1 + 3·1 = 5` with the binary's exact rewrite count.
    #[test]
    fn import_diamond_conforms() {
        conform(
            conformance_file!("import-diamond.maude"),
            &[e("N", "s(s(s(s(s(0)))))", 12)],
        );
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

    /// A compound identity is a ground term in the copied signature, not a source symbol id. It survives a
    /// plain import, a whole-module sort/operator rename, and parameter instantiation through a view whose
    /// prefix source operator becomes mixfix in the target. Results and counts are the live Maude 3.5.1
    /// outputs for the same source.
    #[test]
    fn compound_identity_transfer_conforms() {
        conform(
            "fmod ID-BASE is\n\
               sort S .\n\
               ops a b : -> S [ctor] .\n\
               op g : S -> S [ctor iter] .\n\
               op pair : S S -> S [ctor] .\n\
               op join : S S -> S [assoc id: pair(g^1000000(a),b)] .\n\
             endfm\n\
             red in ID-BASE : join(pair(g^1000000(a),b),a) .\n\
             fmod ID-IMPORT is protecting ID-BASE . endfm\n\
             red in ID-IMPORT : join(pair(g^1000000(a),b),b) .\n\
             fmod ID-RENAME is\n\
               protecting ID-BASE * (sort S to T, op a to x, op b to y,\n\
                 op g to h, op pair to _+_, op join to merge) .\n\
             endfm\n\
             red in ID-RENAME : merge(h^1000000(x) + y,x) .\n\
             fth ID-TH is\n\
               sort Elt .\n\
               ops zero one : -> Elt [ctor] .\n\
               op step : Elt -> Elt [ctor iter] .\n\
               op mk : Elt Elt -> Elt [ctor] .\n\
             endfth\n\
             fmod COLOR is\n\
               sort Hue .\n\
               ops cx cy : -> Hue [ctor] .\n\
               op hop : Hue -> Hue [ctor iter] .\n\
               op _+_ : Hue Hue -> Hue [ctor] .\n\
             endfm\n\
             view V from ID-TH to COLOR is\n\
               sort Elt to Hue .\n\
               op zero to cx .\n\
               op one to cy .\n\
               op step to hop .\n\
               op mk to _+_ .\n\
             endv\n\
             fmod ID-BAG{X :: ID-TH} is\n\
               sort Bag{X} .\n\
               op box : X$Elt -> Bag{X} [ctor] .\n\
               op put : Bag{X} Bag{X} -> Bag{X}\n\
                 [assoc id: box(mk(step^1000000((zero).X$Elt),(one).X$Elt))] .\n\
             endfm\n\
             fmod ID-USE is protecting ID-BAG{V} . endfm\n\
             red in ID-USE : put(box(hop^1000000((cx).Hue) + (cy).Hue),box(cx)) .\n",
            &[
                e("S", "a", 0),
                e("S", "b", 0),
                e("T", "x", 0),
                e("Bag{V}", "box(cx)", 0),
            ],
        );
    }

    /// A whole-module rename must rewrite a structured sort inside an existing identity qualifier
    /// without wrapping the already-qualified constant again. This is the shape used by the stock
    /// `linear.maude` `Vector{Int0}`/`Matrix{Int0}` renames.
    #[test]
    fn structured_sort_identity_rename_conforms() {
        conform(
            "fmod STRUCT-ID is\n\
               sorts Int0 Vector{Int0} .\n\
               op empty : -> Vector{Int0} [ctor] .\n\
               op _;_ : Vector{Int0} Vector{Int0} -> Vector{Int0}\n\
                 [ctor assoc comm id: (empty).Vector{Int0}] .\n\
             endfm\n\
             fmod RENAMED-STRUCT-ID is\n\
               protecting STRUCT-ID *\n\
                 (sort Vector{Int0} to IntVector, op empty to zeroVector) .\n\
             endfm\n\
             reduce in RENAMED-STRUCT-ID : zeroVector ; zeroVector .\n",
            &[e("IntVector", "zeroVector", 0)],
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
        conform(
            conformance_file!("view-good.maude"),
            &[e("N", "z", 1), e("N", "s(z)", 1)],
        );
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

    /// Axis-A2/A5: a *parameterized view* `BoxV{X :: TRIV}` instantiated by a module-view `ToColor`, used
    /// as the argument of a **nested instantiation** `BOX{BoxV{ToColor}}`. The outer element sort is
    /// `Box{ToColor}`, so `wrap`/`peek` are ad-hoc overloaded across the `Hue` / `Box{ToColor}` /
    /// `Box{BoxV{ToColor}}` kinds and the equation `peek(wrap(E:X$Elt)) = E:X$Elt` is instantiated at two
    /// different element sorts (the colon variable's sort is rewritten per copy). Byte-identical to the
    /// reference binary across all five reduces.
    #[test]
    fn instantiation_nested_conforms() {
        conform(
            conformance_file!("instantiation-nested.maude"),
            &[
                e("Box{ToColor}", "wrap(red)", 0),
                e("Box{BoxV{ToColor}}", "wrap(wrap(red))", 0),
                e("Hue", "red", 1),
                e("Box{ToColor}", "wrap(red)", 1),
                e("Hue", "red", 2),
            ],
        );
    }

    /// Axis-A5 kind 2: a **by-parameter** instantiation. `PAIR{X :: TRIV}` protects `LIST{X}` —
    /// instantiating `LIST` by the *enclosing parameter* `X`, not a view — and `USEP` grounds it with
    /// `PAIR{ToN}`, re-instantiating the bound `X ↦ ToN` (the import `LIST{X}` becomes `LIST{ToN}`).
    /// Reductions fire through both modules' instantiated equations. Byte-identical to the reference.
    #[test]
    fn instantiation_byparam_conforms() {
        conform(
            conformance_file!("instantiation-byparam.maude"),
            &[
                e("List{ToN}", "cons(0, cons(s(0), nil))", 1),
                e(
                    "List{ToN}",
                    "cons(0, cons(0, cons(s(0), cons(s(0), nil))))",
                    5,
                ),
                e("List{ToN}", "cons(0, cons(0, nil))", 2),
            ],
        );
    }

    /// Axis-A5: nested ground instantiation `LIST{List{ToN}}` (the `LIST{List{Nat}}` shape) — the
    /// parameterized view `List` instantiated by `ToN` derives a view to `LIST{ToN}`, so the outer element
    /// sort is `List{ToN}` and `cons`/`nil`/`app` are ad-hoc overloaded across the `Nat` / `List{ToN}` /
    /// `List{List{ToN}}` kinds. Reductions fire (`app` over lists of lists) and the disambiguated constant
    /// `(nil).List{ToN}` round-trips. Byte-identical to the reference.
    #[test]
    fn instantiation_nested_list_conforms() {
        conform(
            conformance_file!("instantiation-nested-list.maude"),
            &[
                e("List{List{ToN}}", "cons(cons(0, nil), nil)", 0),
                e("List{List{ToN}}", "cons(cons(0, nil), cons(nil, nil))", 2),
                e("List{List{ToN}}", "cons(nil, cons(cons(0, nil), nil))", 2),
            ],
        );
    }

    /// Axis-A5 kind 1: a **theory-view** argument. `ToT2`'s target `T2` is a theory, so `BOX{ToT2}` keeps a
    /// free parameter retyped to `T2`; the chain `BOX{ToT2}{C2}` grounds it with the module-view `C2`. The
    /// composition maps `X$Elt ↦ Hue` and names the structured sort `Box{X} ↦ Box{ToT2}{C2}` (the whole
    /// chain). Byte-identical to the reference across the element- and box-typed results.
    #[test]
    fn instantiation_theory_view_conforms() {
        conform(
            conformance_file!("instantiation-theory-view.maude"),
            &[
                e("Box{ToT2}{C2}", "wrap(red)", 0),
                e("Hue", "red", 1),
                e("Hue", "sentinel", 1),
            ],
        );
    }

    /// Bracketed comments `***( … )` / `---( … )` — balanced parens across newlines, with a backquoted paren
    /// not counting and code-looking text inside ignored — plus inline ones and plain line comments with a
    /// stray `(`. The module builds past all of them and reduces. Byte-identical to the reference.
    #[test]
    fn bracketed_comment_conforms() {
        conform(
            conformance_file!("correctness-bracketed-comment.maude"),
            &[e("S", "a", 1), e("S", "a", 2)],
        );
    }

    /// A **user-typed** colon variable over a structured sort (`L:List{Nat}`, written inline in an equation):
    /// the lexer keeps the braces in one token, so it resolves to a variable of sort `List{Nat}` and the
    /// equation fires. Byte-identical to the reference.
    #[test]
    fn structured_colon_var_conforms() {
        conform(
            conformance_file!("correctness-colon-var-structured.maude"),
            &[e("List{Nat}", "c(0, nil)", 1), e("List{Nat}", "hd(nil)", 0)],
        );
    }

    /// A membership over a **structured** sort in a parameterized module (`mb cons(H, T) : NeList{E}`):
    /// both the inline-typed lhs and the structured target sort instantiate (`E ↦ ToN`), so `cons(0, nil)`
    /// has least sort `NeList{ToN}`. Byte-identical to the reference (the structured membership sort and the
    /// multi-token sort resolution are exercised end-to-end).
    #[test]
    fn instantiation_membership_conforms() {
        conform(
            conformance_file!("instantiation-membership.maude"),
            &[
                e("NeList{ToN}", "cons(0, nil)", 1),
                e("NeList{ToN}", "cons(0, cons(s(0), nil))", 2),
                e("Nat", "s(0)", 2),
            ],
        );
    }

    /// A parameterized `SET{X}` with an associative-commutative union (`id: empty`) instantiated by `ToN`:
    /// a theory operator and AC matching inside a parameterized module, with duplicate singletons collapsing
    /// via the idempotence equation. Byte-identical to the reference.
    #[test]
    fn instantiation_set_ac_conforms() {
        conform(
            conformance_file!("instantiation-set-ac.maude"),
            &[
                e("NeSet{ToN}", "sing(0), sing(s(0))", 1),
                e("NeSet{ToN}", "sing(0)", 2),
            ],
        );
    }

    /// A two-parameter `MAP{K, V}` instantiated by two distinct views (`ToN`, `ToS`): each parameter binds
    /// independently and the structured sorts use both arguments (`Map{ToN,ToS}`). Byte-identical.
    #[test]
    fn instantiation_map_multiparam_conforms() {
        conform(
            conformance_file!("instantiation-map.maude"),
            &[
                e("Nat", "0", 1),
                e("Map{ToN,ToS}", "put(0 |-> a, put(s(0) |-> b, mt))", 0),
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

    /// Axis-A1: view operator maps. `ToFL` maps `op zero to term f0` (op→term) and `op wrap to box`
    /// (op→op); at instantiation both are substituted into `ARR`'s statements, so `d0(mk) = zero = f0` and
    /// `d1(mk) = wrap(zero) = box(f0)`. Byte-identical to the binary.
    #[test]
    fn param_view_opmap_conforms() {
        conform(
            conformance_file!("param-view-opmap.maude"),
            &[e("F", "f0", 1), e("F", "box(f0)", 1)],
        );
    }

    /// Axis-A4: a parameter theory `ORD` that `protecting`s a module `B` (sort `Bool`) and `including`s
    /// `TRIV` (sort `Elt`). The parameter copy qualifies only the theory-declared `Elt` (→ `X$Elt`) and
    /// keeps the module-declared `Bool`, so `USE-ORD`'s `-> Bool` resolves; instantiation `USE-ORD{ToNN}`
    /// maps `Elt ↦ N`, `cmp ↦ le`, so `check(w(n0),w(n0)) = tt`. Byte-identical to the binary.
    #[test]
    fn param_theory_module_sorts_conforms() {
        conform(
            conformance_file!("param-theory-module-sorts.maude"),
            &[e("Bool", "tt", 2)],
        );
    }

    #[test]
    fn signature_disambiguated_view_maps_conform() {
        conform(
            conformance_file!("audit/A4g-view-specific-map.maude"),
            &[e("X", "x1", 2), e("Y", "y1", 2)],
        );
    }

    #[test]
    fn transformed_module_imports_in_parameter_theories_conform() {
        conform(
            conformance_file!("audit/A4h-theory-transformed-imports.maude"),
            &[
                e("Truth", "yes", 2),
                e("BoxI{A4H-ToN-I}", "boxi(zi)", 2),
                e("TruthM", "answerM", 2),
            ],
        );
    }

    /// Cross-kind ad-hoc operator overloading (the kernel prerequisite nested instantiation surfaced):
    /// `f : A -> B` and `f : B -> C` are the *same* name+arity in *different* connected components, so they
    /// are distinct symbols (the argument kind selects the declaration), and `f(f(a))` types as `C`.
    /// Byte-identical to the reference binary.
    #[test]
    fn cross_kind_overload_conforms() {
        conform(
            "fmod CK is\n\
               sorts A B C .\n\
               op a : -> A [ctor] .\n\
               op f : A -> B [ctor] .\n\
               op f : B -> C [ctor] .\n\
               op g : C -> A .\n\
               eq g(f(f(a))) = a .\n\
             endfm\n\
             red f(a) .\n\
             red f(f(a)) .\n\
             red g(f(f(a))) .\n",
            &[e("B", "f(a)", 0), e("C", "f(f(a))", 0), e("A", "a", 1)],
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
        assert!(
            err.contains("failed to find sort NoSuch in NUM"),
            "got: {err}"
        );
    }

    #[test]
    fn strategy_home_grammar_actions_use_destination_identities() {
        use tnk_frontend::grammar::Action;

        let program = load_program(
            "fmod STRAT-HOME-SHIFT is
               sort Q .
               ops q0 q1 q2 : -> Q .
             endfm
             smod STRAT-HOME-DONOR is
               sort S .
               op a : -> S .
               op h : S -> S .
               var X : S .
               strat home : S @ S .
               sd home(X) := match h(X) .
             endsm
             smod STRAT-HOME-USE is
               protecting STRAT-HOME-SHIFT .
               protecting STRAT-HOME-DONOR .
             endsm",
        )
        .expect("load homed strategy modules");
        let donor = &program.modules[program.module_index["STRAT-HOME-DONOR"]];
        let importer = &program.modules[program.module_index["STRAT-HOME-USE"]];
        let mapped = importer
            .strategy_grammars
            .get("STRAT-HOME-DONOR")
            .expect("remapped donor grammar");

        let donor_h = donor
            .grammar
            .prods
            .iter()
            .find_map(|production| match production.action {
                Action::MakeTerm(symbol) if donor.built.engine.symbol(symbol).name() == "h" => {
                    Some(symbol)
                }
                _ => None,
            })
            .expect("donor h action");
        let imported_h = mapped
            .prods
            .iter()
            .find_map(|production| match production.action {
                Action::MakeTerm(symbol) if importer.built.engine.symbol(symbol).name() == "h" => {
                    Some(symbol)
                }
                _ => None,
            })
            .expect("destination h action");
        assert_ne!(
            donor_h, imported_h,
            "the preceding import shifts destination symbol identities"
        );
        assert_eq!(importer.built.engine.symbol(imported_h).name(), "h");

        let donor_variable_sort = donor
            .grammar
            .prods
            .iter()
            .find_map(|production| match production.action {
                Action::MakeVariable(sort) if donor.built.engine.sorts().name(sort) == "S" => {
                    Some(sort)
                }
                _ => None,
            })
            .expect("donor S variable action");
        let imported_variable_sort = mapped
            .prods
            .iter()
            .find_map(|production| match production.action {
                Action::MakeVariable(sort) if importer.built.engine.sorts().name(sort) == "S" => {
                    Some(sort)
                }
                _ => None,
            })
            .expect("destination S variable action");
        assert_ne!(
            donor_variable_sort, imported_variable_sort,
            "home variable actions are re-pointed to the destination sort table"
        );
        assert_eq!(
            importer.built.engine.sorts().name(imported_variable_sort),
            "S"
        );
    }
}
