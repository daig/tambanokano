//! The context-free parser: a **plain Earley parser with prec/gather gating** over a module's mixfix
//! [`Grammar`](crate::grammar::Grammar). Ported from Maude's `Parser/` (pass1/pass2) with the **Leo/DRP
//! optimization bypassed** — Maude's DRP is a purely additive memo shortcut (`to keep LR(k) grammars
//! linear`), so omitting it changes only speed, not which parses are produced or their order. It also
//! removes the trickiest, least-documented C++ (the deterministic-reduction-path memo invariants), which
//! is the right correctness/complexity trade for the milestone; the plain parser is the oracle Leo would
//! be validated against if it is ever added.
//!
//! Adaptation: Maude's calls/continuations/returns with signed-int symbols and index-linked free lists
//! become standard Earley item sets over the typed [`grammar`](crate::grammar) symbols. Maude's two
//! gating checks (`rhs[pos].prec >= prec` on a continuation, `prec <= maxPrec` + `rhs[0].prec >= prec` on
//! a left-recursive start-up; `pass1.cc:164/222/230`) collapse to a single completer rule here — a
//! finished production of precedence `p` may advance a waiting item over its hole iff that hole's gather
//! bound `>= p` — because Earley's predictor subsumes Maude's left-recursion expansion tables, and a
//! caller's `maxPrec` is just its own hole bound, checked one level up when *it* completes.

pub mod compile;
pub mod earley;
