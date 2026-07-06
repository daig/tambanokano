//! D7 gate spike (subsystems-goal.md §3): confirm the `z3` crate's incremental push/pop semantics
//! match `smt-search`'s pruning model before the `SmtEngine` trait is frozen.
//!
//! Maude's SMT surface (3.5.1) is verdict-only — `check` prints sat/unsat/undecided and
//! `smt-search` prints engine-rendered states/substitutions/constraints, never solver models — so
//! the conformance question reduces to: does one incremental solver driven with
//! assert/push/pop along the search tree return the SAME verdicts as a fresh solver given each
//! node's accumulated conjunction from scratch? (That fresh-solver semantics is what Maude's
//! per-node satisfiability pruning assumes.)
//!
//! Probes:
//!   P1  version + build sanity (brew libz3).
//!   P2  the QF_LIA / QF_LRA / Boolean fixture shapes from tests/Misc/smtTest.maude and manual
//!       ch. 16 — expected verdicts hardcoded from the reference .expected file.
//!   P3  the gate: randomized (seeded) linear-integer constraint trees explored DFS with one
//!       incremental solver (push on descend, pop on backtrack) vs a fresh solver per node.
//!   P4  Maude-value mapping edges: bignum integer coefficients (arbitrary precision), rational
//!       Real constants, and Int/Real mixing via to_real.

use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use z3::ast::{Ast, Bool, Int, Real};
use z3::{Config, Context, SatResult, Solver};

fn verdict(s: SatResult) -> &'static str {
    match s {
        SatResult::Sat => "sat",
        SatResult::Unsat => "unsat",
        SatResult::Unknown => "undecided",
    }
}

fn p1_version(ctx: &Context) {
    println!("== P1: z3 build sanity ==");
    // A trivial end-to-end round trip proves the brew libz3 linked and answers.
    let s = Solver::new(ctx);
    s.assert(&Bool::from_bool(ctx, true));
    println!("  linked libz3 answers: {}", verdict(s.check()));
}

fn p2_fixture_shapes(ctx: &Context) {
    println!("\n== P2: fixture-shaped verdicts (expected values from smtTest.expected / manual ch.16) ==");
    let cases: Vec<(&str, Bool, &str)> = {
        let w = Bool::new_const(ctx, "W");
        let x = Bool::new_const(ctx, "X");
        let y = Bool::new_const(ctx, "Y");
        let i = Int::new_const(ctx, "i");
        let j = Int::new_const(ctx, "j");
        let r = Real::new_const(ctx, "r");
        vec![
            // tests/Misc/smtTest.maude TEST-B shapes:
            ("W =/== (X and Y)", w._eq(&Bool::and(ctx, &[&x, &y])).not(), "sat"),
            ("W === (X and Y)", w._eq(&Bool::and(ctx, &[&x, &y])), "sat"),
            (
                "X=/=true, X=/=Y, Y=/=true",
                Bool::and(
                    ctx,
                    &[
                        &x._eq(&Bool::from_bool(ctx, true)).not(),
                        &x._eq(&y).not(),
                        &y._eq(&Bool::from_bool(ctx, true)).not(),
                    ],
                ),
                "unsat",
            ),
            (
                "X=/=true, X=/=Y, Y=/=false",
                Bool::and(
                    ctx,
                    &[
                        &x._eq(&Bool::from_bool(ctx, true)).not(),
                        &x._eq(&y).not(),
                        &y._eq(&Bool::from_bool(ctx, false)).not(),
                    ],
                ),
                "sat", // X = false, Y = true satisfies; verified in smtTest.expected AND the Yices2 oracle
            ),
            // QF_LIA:
            (
                "i > 0 and i < 0",
                Bool::and(ctx, &[&i.gt(&Int::from_i64(ctx, 0)), &i.lt(&Int::from_i64(ctx, 0))]),
                "unsat",
            ),
            (
                "i + j > 10 and i < -5",
                Bool::and(
                    ctx,
                    &[
                        &Int::add(ctx, &[&i, &j]).gt(&Int::from_i64(ctx, 10)),
                        &i.lt(&Int::from_i64(ctx, -5)),
                    ],
                ),
                "sat",
            ),
            // QF_LRA:
            (
                "r > 0 and 3r < 1",
                Bool::and(
                    ctx,
                    &[
                        &r.gt(&Real::from_real(ctx, 0, 1)),
                        &Real::mul(ctx, &[&Real::from_real(ctx, 3, 1), &r])
                            .lt(&Real::from_real(ctx, 1, 1)),
                    ],
                ),
                "sat",
            ),
        ]
    };
    let mut all_ok = true;
    for (label, formula, expected) in &cases {
        let s = Solver::new(ctx);
        s.assert(formula);
        let got = verdict(s.check());
        let ok = got == *expected;
        all_ok &= ok;
        println!("  {} {label}: {got} (expected {expected})", if ok { "ok " } else { "XXX" });
    }
    assert!(all_ok, "P2 verdict mismatch");
}

/// One random linear atom over the given integer variables.
fn random_atom<'a>(ctx: &'a Context, vars: &[Int<'a>], rng: &mut SmallRng) -> Bool<'a> {
    let a = rng.gen_range(-4i64..=4);
    let b = rng.gen_range(-4i64..=4);
    let c = rng.gen_range(-12i64..=12);
    let v1 = &vars[rng.gen_range(0..vars.len())];
    let v2 = &vars[rng.gen_range(0..vars.len())];
    let lhs = Int::add(
        ctx,
        &[
            &Int::mul(ctx, &[&Int::from_i64(ctx, a), v1]),
            &Int::mul(ctx, &[&Int::from_i64(ctx, b), v2]),
        ],
    );
    let rhs = Int::from_i64(ctx, c);
    match rng.gen_range(0..4) {
        0 => lhs.gt(&rhs),
        1 => lhs.lt(&rhs),
        2 => lhs.ge(&rhs),
        _ => lhs._eq(&rhs),
    }
}

fn p3_incremental_vs_fresh(ctx: &Context) {
    println!("\n== P3 (the gate): incremental push/pop DFS vs fresh-solver-per-node ==");
    let vars: Vec<Int> = (0..3).map(|k| Int::new_const(ctx, format!("x{k}"))).collect();
    let mut nodes = 0usize;
    let mut sat_nodes = 0usize;
    for seed in 0..40u64 {
        let mut rng = SmallRng::seed_from_u64(seed);
        // A random constraint tree: branching 2, depth 4 — one atom per edge, like the
        // accumulated path constraints of an smt-search exploration.
        let depth = 4usize;
        let solver = Solver::new(ctx);
        // DFS with explicit stack of (path, child index); incremental solver mirrors the path.
        let mut path: Vec<Bool> = Vec::new();
        // Recursive closure via explicit stack: at each node, verify incremental verdict ==
        // fresh verdict, then descend.
        fn explore<'a>(
            ctx: &'a Context,
            solver: &Solver<'a>,
            vars: &[Int<'a>],
            rng: &mut SmallRng,
            path: &mut Vec<Bool<'a>>,
            depth: usize,
            nodes: &mut usize,
            sat_nodes: &mut usize,
        ) {
            // Verdict from the incremental solver state (path already asserted).
            let inc = solver.check();
            // Verdict from a fresh solver over the accumulated conjunction.
            let fresh_solver = Solver::new(ctx);
            for c in path.iter() {
                fresh_solver.assert(c);
            }
            let fresh = fresh_solver.check();
            assert_eq!(
                verdict(inc),
                verdict(fresh),
                "incremental vs fresh divergence at depth {} (path len {})",
                depth,
                path.len()
            );
            *nodes += 1;
            if inc == SatResult::Sat {
                *sat_nodes += 1;
            }
            // Maude prunes unsat branches: only descend on sat, like smt-search.
            if depth == 0 || inc != SatResult::Sat {
                return;
            }
            for _child in 0..2 {
                let atom = random_atom(ctx, vars, rng);
                solver.push();
                solver.assert(&atom);
                path.push(atom);
                explore(ctx, solver, vars, rng, path, depth - 1, nodes, sat_nodes);
                path.pop();
                solver.pop(1);
            }
        }
        explore(ctx, &solver, &vars, &mut rng, &mut path, depth, &mut nodes, &mut sat_nodes);
        assert_eq!(solver.get_assertions().len(), 0, "pop imbalance after tree {seed}");
    }
    println!("  {nodes} nodes verified across 40 random trees ({sat_nodes} sat); zero divergences, pops balanced");
}

fn p4_value_mapping(ctx: &Context) {
    println!("\n== P4: Maude value-mapping edges ==");
    // Arbitrary-precision integer coefficients (Maude Integers are bignums).
    let big = "123456789012345678901234567890123456789";
    let n = Int::from_str(ctx, big).expect("bignum literal");
    let x = Int::new_const(ctx, "x");
    let s = Solver::new(ctx);
    s.assert(&x.gt(&n));
    assert_eq!(verdict(s.check()), "sat");
    println!("  ok  40-digit integer coefficient accepted (x > {big}... sat)");
    // Rational Real constants (Maude Real is exact rational arithmetic).
    let third = Real::from_real(ctx, 1, 3);
    let r = Real::new_const(ctx, "r");
    let s = Solver::new(ctx);
    s.assert(&Real::add(ctx, &[&r, &r, &r])._eq(&Real::from_real(ctx, 1, 1)));
    s.assert(&r._eq(&third).not());
    assert_eq!(verdict(s.check()), "unsat");
    println!("  ok  exact rational semantics (r+r+r = 1 forces r = 1/3... unsat with r =/= 1/3)");
    // Int/Real mixing via toReal (smt.maude's toReal/toInteger seam).
    let i = Int::new_const(ctx, "i");
    let s = Solver::new(ctx);
    s.assert(&Real::from_int(&i).gt(&Real::from_real(ctx, 1, 2)));
    s.assert(&i.le(&Int::from_i64(ctx, 0)));
    assert_eq!(verdict(s.check()), "unsat");
    println!("  ok  toReal coercion (real(i) > 1/2 and i <= 0... unsat)");
}

fn main() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    p1_version(&ctx);
    p2_fixture_shapes(&ctx);
    p3_incremental_vs_fresh(&ctx);
    p4_value_mapping(&ctx);
    println!("\nall probes green.");
}
