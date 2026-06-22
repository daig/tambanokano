//! The pretty-printer: a reduced `DagNode` → surface text. Two products share one core walk:
//! - [`print_raw`] — a **round-trippable** plain rendering (`parse∘print = id`): emits forms our parser
//!   reads back (decimal numerals, `s s 0` for plain iter, `- 3` spaced for negation).
//! - [`print_pretty`] (B4.6c) — a **Maude-faithful** rendering with optional ANSI syntax coloring, for
//!   interactive use (and, uncolored, for the textual diff against the reference binary).
//!
//! The walk is the inverse of the B4.3 grammar + B4.4 parser: parenthesization is the exact inverse of the
//! Earley prec/gather gate — a subterm of precedence `prec` is wrapped iff the position's gather bound
//! `required_prec < prec` (plus Maude's `LEFT_BARE`/`RIGHT_BARE` adjacency "capture" cases). Ported from
//! `Mixfix/dagNodePrint.cc::prettyPrint`. Reads only the frontend's [`SymbolSyntax`] tables + the public
//! kernel accessors (`DagNode::{repr,symbol,children}`).

use crate::grammar::{prec_gather, PREFIX_GATHER};
use crate::lex::{Frag, Interner, Sym};
use crate::sig::syntax::{BuiltModule, SymbolSyntax};
use tnk_core::dag::{DagId, NodeRepr};
use tnk_core::sort::KindId;
use tnk_core::symbol::SymbolId;

/// `s_`'s OBJ3 unary precedence — the precedence of the iterated-successor mixfix form (`grammar`'s
/// `UNARY_PREC`). Used when laying out the round-trip repeated `s s … base` form.
const UNARY_PREC: u32 = crate::grammar::UNARY_PREC;

/// A sentinel "no precedence constraint / no adjacent capture" — larger than any real precedence
/// (`MAX_PREC = 127`), so `required_prec < prec` and `capture <= gather` never fire against it.
const UNBOUNDED: u32 = u32::MAX;

/// An adjacency-capture context (Maude's `leftCapture`/`rightCapture` + their component): the precedence
/// of the token abutting a subterm on one side, and the kind that token belongs to. `NONE` = no abutting
/// token (a top-level or parenthesized position).
#[derive(Clone, Copy)]
struct Cap {
    prec: u32,
    kind: Option<KindId>,
}
const NONE_CAP: Cap = Cap { prec: UNBOUNDED, kind: None };

/// The syntactic category of an emitted token. The raw printer ignores it; the pretty printer (B4.6c)
/// colors by it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Cat {
    /// An operator name fragment / prefix name.
    Op,
    /// A numeric / built-in constant literal.
    Lit,
    /// Structural punctuation (parens, commas).
    Punct,
}

/// Render `d` (a reduced node) as round-trippable plain text: `parse(print_raw(t)) == t`.
pub fn print_raw(m: &BuiltModule, i: &Interner, d: DagId) -> String {
    Printer { m, i }.render(d)
}

/// The shared printer. `m`/`i` are immutable; the output buffer is threaded as a `&mut String`
/// parameter so the recursive walk can read `self` freely while appending. (B4.6c adds a colored mode.)
struct Printer<'a> {
    m: &'a BuiltModule,
    i: &'a Interner,
}

impl Printer<'_> {
    fn render(&self, d: DagId) -> String {
        let mut out = String::new();
        self.print(&mut out, d, UNBOUNDED, NONE_CAP, NONE_CAP);
        out
    }

    /// Print node `d` under a position whose gather bound is `req_prec`, with the given left/right
    /// adjacency-capture contexts.
    fn print(&self, out: &mut String, d: DagId, req_prec: u32, lcap: Cap, rcap: Cap) {
        let node = self.m.engine.node(d);
        let symbol = node.symbol();
        // Extract owned leaf data so the `&node` borrow is released before the recursive `&self` calls.
        let leaf = match node.repr() {
            NodeRepr::App => None,
            NodeRepr::Iter { count, arg } => Some(Leaf::Iter { count, arg }),
            NodeRepr::Str(s) => Some(Leaf::Atom(render_string(s))),
            NodeRepr::Qid(q) => Some(Leaf::Atom(format!("'{q}"))),
            NodeRepr::Float(f) => Some(Leaf::Atom(render_float(f))),
        };
        match leaf {
            Some(Leaf::Atom(text)) => self.emit(out, Cat::Lit, &text),
            Some(Leaf::Iter { count, arg }) => self.print_iter(out, symbol, &count, arg, req_prec, rcap),
            None => self.print_app(out, d, symbol, req_prec, lcap, rcap),
        }
    }

    /// An operator application (free / ACU / AU / CUI) — mixfix, prefix, or constant.
    fn print_app(&self, out: &mut String, d: DagId, symbol: SymbolId, req_prec: u32, lcap: Cap, rcap: Cap) {
        let children: Vec<DagId> = self.m.engine.node(d).children().collect();
        let Some(syn) = self.m.syntax.get(&symbol) else {
            // No recorded syntax (should not happen for a user op): prefix-print with the kernel name.
            self.emit(out, Cat::Op, self.m.engine.symbol(symbol).name());
            self.print_arg_list(out, &children);
            return;
        };
        let has_hole = syn.frags.iter().any(|f| matches!(f, Frag::Hole));
        if !has_hole {
            // Constant or prefix operator: `name` / `name(a, b, …)`.
            self.emit(out, Cat::Op, self.frag_text(&syn.frags[0]));
            if !children.is_empty() {
                self.print_arg_list(out, &children);
            }
            return;
        }
        // Mixfix. Parenthesize iff this op binds looser than the position allows (the inverse of the
        // parser's gather gate), or an adjacency-capture would re-associate it.
        let pg = prec_gather::compute(&syn.frags, syn.domain.len(), syn.prec, syn.gather.as_deref(), syn.assoc);
        let paren = req_prec < pg.prec || self.captures(syn, &pg.gather, lcap, rcap);
        if paren {
            self.emit(out, Cat::Punct, "(");
        }
        // A surrounding paren blocks inherited capture (Maude: inherit leftCapture/rightCapture only when
        // not parenthesized).
        let (lcap, rcap) = if paren { (NONE_CAP, NONE_CAP) } else { (lcap, rcap) };
        self.print_mixfix(out, syn, &pg, &children, lcap, rcap);
        if paren {
            self.emit(out, Cat::Punct, ")");
        }
    }

    /// Emit a mixfix form: walk the syntax fragments, emitting literal tokens and recursing into argument
    /// holes (each at its gather bound + adjacency context). An associative operator with more arguments
    /// than its arity folds its flattened children over the infix tokens (`a + b + c`).
    fn print_mixfix(&self, out: &mut String, syn: &SymbolSyntax, pg: &prec_gather::PrecGather, children: &[DagId], lcap: Cap, rcap: Cap) {
        let nr_args = syn.domain.len();
        let left_bare = matches!(syn.frags.first(), Some(Frag::Hole));
        let right_bare = matches!(syn.frags.last(), Some(Frag::Hole));

        // Associative fold for the pure binary infix `_ OP _` with > 2 flattened children.
        if syn.assoc && nr_args == 2 && left_bare && right_bare && children.len() > 2 {
            let mid: Vec<&Frag> = syn.frags[1..syn.frags.len() - 1].iter().collect();
            for (idx, &c) in children.iter().enumerate() {
                if idx > 0 {
                    for f in &mid {
                        out.push(' ');
                        self.emit(out, Cat::Op, self.frag_text(f));
                    }
                    out.push(' ');
                }
                // Inner elements bind at the tighter gather[1]; left/right ends keep the outer capture.
                let bound = if idx == 0 { pg.gather[0] } else { pg.gather[1] };
                self.print(out, c, bound, NONE_CAP, NONE_CAP);
            }
            return;
        }

        let mut k = 0;
        let mut first = true;
        for (pos, frag) in syn.frags.iter().enumerate() {
            if !first {
                out.push(' ');
            }
            first = false;
            match frag {
                Frag::Tok(_) => self.emit(out, Cat::Op, self.frag_text(frag)),
                Frag::Hole => {
                    let (lc, rc) = self.hole_caps(syn, pg, k, nr_args, left_bare, right_bare, lcap, rcap, pos);
                    self.print(out, children[k], pg.gather[k], lc, rc);
                    k += 1;
                }
            }
        }
    }

    /// The adjacency-capture contexts for the `k`-th argument hole (Maude `dagNodePrint.cc:435-458`): a
    /// bare end abuts this op's token (`rc`/`lc` = this op's precedence + the arg's kind), and the outer
    /// capture flows through the opposite side.
    #[allow(clippy::too_many_arguments)]
    fn hole_caps(&self, syn: &SymbolSyntax, pg: &prec_gather::PrecGather, k: usize, nr_args: usize, left_bare: bool, right_bare: bool, lcap: Cap, rcap: Cap, _pos: usize) -> (Cap, Cap) {
        let sorts = self.m.engine.sorts();
        if k == 0 && left_bare {
            let rc = Cap { prec: pg.prec, kind: Some(sorts.kind_of(syn.domain[0])) };
            (lcap, rc)
        } else if k == nr_args - 1 && right_bare {
            let lc = Cap { prec: pg.prec, kind: Some(sorts.kind_of(syn.domain[nr_args - 1])) };
            (lc, rcap)
        } else {
            (NONE_CAP, NONE_CAP)
        }
    }

    /// Maude's parent-side capture test: a bare end of this op would be captured by an abutting token of
    /// the same kind whose precedence the end's gather bound admits.
    fn captures(&self, syn: &SymbolSyntax, gather: &[u32], lcap: Cap, rcap: Cap) -> bool {
        let sorts = self.m.engine.sorts();
        let nr_args = syn.domain.len();
        let left_bare = matches!(syn.frags.first(), Some(Frag::Hole));
        let right_bare = matches!(syn.frags.last(), Some(Frag::Hole));
        (left_bare && lcap.prec <= gather[0] && lcap.kind == Some(sorts.kind_of(syn.domain[0])))
            || (right_bare && rcap.prec <= gather[nr_args - 1] && rcap.kind == Some(sorts.kind_of(syn.domain[nr_args - 1])))
    }

    /// Print `s^count(arg)`. A successor numeral over the zero base prints in decimal (`5`); a plain
    /// `iter` operator prints `count` repeated mixfix applications (`s s … base`) in round-trip mode.
    fn print_iter(&self, out: &mut String, symbol: SymbolId, count: &str, arg: DagId, req_prec: u32, rcap: Cap) {
        // A SuccSymbol applied to the zero constant is a decimal numeral.
        if self.m.nat_succ == Some(symbol) && self.is_zero(arg) {
            self.emit(out, Cat::Lit, count);
            return;
        }
        // Plain iter (round-trip): `count` repeated successor applications over the base.
        let n: u64 = count.parse().expect("iter count fits u64 for the round-trip form");
        let Some(syn) = self.m.syntax.get(&symbol) else { return };
        let prefix: Vec<&Frag> = syn.frags.iter().take_while(|f| !matches!(f, Frag::Hole)).collect();
        let paren = req_prec < UNARY_PREC;
        if paren {
            self.emit(out, Cat::Punct, "(");
        }
        for _ in 0..n {
            for f in &prefix {
                self.emit(out, Cat::Op, self.frag_text(f));
                out.push(' ');
            }
        }
        // The base sits at the successor's gather bound; its left abuts the last `s` token.
        let lc = Cap { prec: UNARY_PREC, kind: Some(self.m.engine.sorts().kind_of(syn.domain[0])) };
        self.print(out, arg, UNARY_PREC, lc, if paren { NONE_CAP } else { rcap });
        if paren {
            self.emit(out, Cat::Punct, ")");
        }
    }

    /// `(a, b, …)` — a prefix argument list.
    fn print_arg_list(&self, out: &mut String, children: &[DagId]) {
        self.emit(out, Cat::Punct, "(");
        for (idx, &c) in children.iter().enumerate() {
            if idx > 0 {
                self.emit(out, Cat::Punct, ",");
                out.push(' ');
            }
            self.print(out, c, PREFIX_GATHER, NONE_CAP, NONE_CAP);
        }
        self.emit(out, Cat::Punct, ")");
    }

    /// Whether `arg` is the module's zero constant (so a successor over it is a numeral).
    fn is_zero(&self, arg: DagId) -> bool {
        self.m.nat_zero == Some(self.m.engine.node(arg).symbol())
    }

    fn frag_text(&self, frag: &Frag) -> &str {
        match frag {
            Frag::Tok(s) => self.tok_text(*s),
            Frag::Hole => "_",
        }
    }
    fn tok_text(&self, s: Sym) -> &str {
        self.i.resolve(s)
    }

    /// Append `text` for category `cat`. The raw printer emits plain text; the pretty printer (B4.6c)
    /// wraps it in ANSI when `cfg.color`.
    fn emit(&self, out: &mut String, _cat: Cat, text: &str) {
        out.push_str(text);
    }
}

/// Owned leaf rendering data, extracted from a node's `repr` so the borrow is released before recursion.
enum Leaf {
    Iter { count: String, arg: DagId },
    Atom(String),
}

/// A string constant rendered with surrounding quotes and the usual escapes.
fn render_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

/// A float rendered so it re-lexes as a float token (always with a decimal point).
fn render_float(f: f64) -> String {
    let s = format!("{f}");
    if s.contains('.') || s.contains('e') || s.contains("inf") || s.contains("NaN") {
        s
    } else {
        format!("{s}.0")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::load::{load_source, reduce_command};
    use crate::lex::tokenize;
    use crate::surface::ast::Command;

    /// Round-trip: every milestone command's reduced result, raw-printed and re-reduced, is `deep_equal`
    /// to the original result. Drives the existing load/reduce harness.
    fn round_trips(src: &str) {
        let mut loaded = load_source(src).expect("load");
        let cmds: Vec<(usize, Vec<crate::lex::Token>)> = loaded
            .commands
            .iter()
            .map(|(m, c)| match c {
                Command::Reduce { term } => (*m, term.clone()),
                Command::Match { .. } => panic!("milestone uses only reduce"),
            })
            .collect();
        for (idx, (m, term)) in cmds.iter().enumerate() {
            let (result, _) = reduce_command(&mut loaded.modules[*m], &loaded.interner, term)
                .unwrap_or_else(|e| panic!("command {idx}: {e}"));
            let printed = print_raw(&loaded.modules[*m].built, &loaded.interner, result);
            // Re-lex + re-reduce the printed form; it must denote the same term.
            let toks = tokenize(&printed, &mut loaded.interner);
            let (reparsed, _) = reduce_command(&mut loaded.modules[*m], &loaded.interner, &toks)
                .unwrap_or_else(|e| panic!("command {idx} reparse of `{printed}`: {e}"));
            let eng = &loaded.modules[*m].built.engine;
            assert!(eng.deep_equal(result, reparsed), "command {idx}: `{printed}` did not round-trip");
        }
    }

    macro_rules! file {
        ($n:expr) => {
            include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../conformance/", $n))
        };
    }

    #[test]
    fn iter_round_trips() {
        round_trips(file!("iter.maude"));
    }
    #[test]
    fn bool_round_trips() {
        round_trips(file!("bool.maude"));
    }
    #[test]
    fn nat_round_trips() {
        round_trips(file!("nat.maude"));
    }
    #[test]
    fn int_round_trips() {
        round_trips(file!("int.maude"));
    }
}
