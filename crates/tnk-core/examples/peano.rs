//! Phase-0 go/no-go benchmark (decisions D1/D2): reduce throughput and GC throughput on a Peano
//! workload, using only `tnk-core`'s public API. Compare against the reference C++ Maude on
//! `conformance/fib.maude`.
//!
//! Usage: `cargo run --release --example peano [FIB_INDEX] [REPEATS] [GC_CHAIN]`

use std::time::Instant;
use tnk_core::dag::DagId;
use tnk_core::engine::Engine;
use tnk_core::symbol::SymbolId;
use tnk_core::term::{Equation, Term};

struct Peano {
    zero: SymbolId,
    s: SymbolId,
    fib: SymbolId,
}

/// Build the Peano signature + equations for `+` and naive `fib`.
fn build(e: &mut Engine) -> Peano {
    let nat = e.add_sort("Nat");
    e.close_sorts();
    let zero = e.add_op("0", vec![], nat);
    let s = e.add_op("s", vec![nat], nat);
    let plus = e.add_op("+", vec![nat, nat], nat);
    let fib = e.add_op("fib", vec![nat], nat);

    let v = |i| Term::var(i, nat);
    let s_of = |t| Term::op(s, vec![t]);
    let zero_t = || Term::constant(zero);

    // N + 0 = N ;  N + s M = s (N + M)
    e.add_equation(Equation {
        lhs: Term::op(plus, vec![v(0), zero_t()]),
        rhs: v(0),
        nr_vars: 1,
    });
    e.add_equation(Equation {
        lhs: Term::op(plus, vec![v(0), s_of(v(1))]),
        rhs: s_of(Term::op(plus, vec![v(0), v(1)])),
        nr_vars: 2,
    });
    // fib 0 = 0 ;  fib s 0 = s 0 ;  fib s s N = fib(s N) + fib N
    e.add_equation(Equation {
        lhs: Term::op(fib, vec![zero_t()]),
        rhs: zero_t(),
        nr_vars: 0,
    });
    e.add_equation(Equation {
        lhs: Term::op(fib, vec![s_of(zero_t())]),
        rhs: s_of(zero_t()),
        nr_vars: 0,
    });
    e.add_equation(Equation {
        lhs: Term::op(fib, vec![s_of(s_of(v(0)))]),
        rhs: Term::op(
            plus,
            vec![Term::op(fib, vec![s_of(v(0))]), Term::op(fib, vec![v(0)])],
        ),
        nr_vars: 1,
    });

    Peano { zero, s, fib }
}

/// Build the unary numeral `s^n 0`.
fn numeral(e: &mut Engine, p: &Peano, n: u64) -> DagId {
    let mut acc = e.make_const(p.zero);
    for _ in 0..n {
        acc = e.make_free(p.s, vec![acc]);
    }
    acc
}

/// Decode a canonical Peano numeral back to an integer.
fn decode(e: &Engine, mut id: DagId, p: &Peano) -> u64 {
    let mut n = 0;
    loop {
        let node = e.node(id);
        let sym = node.symbol();
        if sym == p.zero {
            return n;
        } else if sym == p.s {
            n += 1;
            id = node.children().next().expect("successor has one child");
        } else {
            panic!("not a Peano numeral");
        }
    }
}

fn fib_ref(n: u64) -> u64 {
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..n {
        (a, b) = (b, a + b);
    }
    a
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let f: u64 = args.get(1).and_then(|x| x.parse().ok()).unwrap_or(20);
    let reps: u64 = args.get(2).and_then(|x| x.parse().ok()).unwrap_or(50);
    let gc_chain: u64 = args
        .get(3)
        .and_then(|x| x.parse().ok())
        .unwrap_or(2_000_000);

    let mut e = Engine::new();
    let p = build(&mut e);

    // --- correctness ---
    let q = {
        let n = numeral(&mut e, &p, f);
        e.make_free(p.fib, vec![n])
    };
    let r = e.reduce(q);
    let val = decode(&e, r, &p);
    let per_fib = e.rewrites();
    println!(
        "fib({f}) = {val}   ({per_fib} rewrites, expected fib = {})",
        fib_ref(f)
    );
    assert_eq!(val, fib_ref(f), "fib result must match");
    e.gc(Vec::new());

    // --- reduce throughput (GC between iterations keeps memory bounded) ---
    e.reset_rewrites();
    let t0 = Instant::now();
    for _ in 0..reps {
        let n = numeral(&mut e, &p, f);
        let q = e.make_free(p.fib, vec![n]);
        let _ = e.reduce(q);
        e.gc(Vec::new());
    }
    let dt = t0.elapsed();
    let rw = e.rewrites();
    println!(
        "reduce: {rw} rewrites over {reps}x fib({f}) in {:.3?}  =>  {:.2} M rewrites/s",
        dt,
        rw as f64 / dt.as_secs_f64() / 1e6
    );
    println!(
        "        peak DAG-arena capacity (bounded by GC): {} nodes",
        e.node_capacity()
    );

    // --- GC throughput: a long chain, time mark-all then sweep-all ---
    let big = numeral(&mut e, &p, gc_chain); // s^gc_chain 0  (gc_chain + 1 nodes)
    let live = e.live_nodes();
    let tm = Instant::now();
    e.gc([big]); // mark everything reachable, sweep nothing
    let mark_dt = tm.elapsed();
    let ts = Instant::now();
    let freed = e.gc(Vec::new()); // sweep everything
    let sweep_dt = ts.elapsed();
    println!(
        "gc mark: {live} nodes in {:.3?} => {:.1} M nodes/s",
        mark_dt,
        live as f64 / mark_dt.as_secs_f64() / 1e6
    );
    println!(
        "gc sweep: {freed} nodes in {:.3?} => {:.1} M nodes/s",
        sweep_dt,
        freed as f64 / sweep_dt.as_secs_f64() / 1e6
    );
}
