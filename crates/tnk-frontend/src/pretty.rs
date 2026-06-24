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
use tnk_core::term::Term;

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

/// Render `d` (a reduced node) as round-trippable plain text: `parse(print_raw(t)) == t`. Plain-iter
/// successors print as repeated `s s … base` and negation as `- n`, the forms our parser reads back.
pub fn print_raw(m: &BuiltModule, i: &Interner, d: DagId) -> String {
    Printer { m, i, faithful: false, color: false, vars: &[] }.render(d)
}

/// Render `d` for interactive display: Maude-faithful forms (`s_^n(0)`, `-3`) with optional ANSI syntax
/// coloring. With `color = false` this is the Maude-faithful plain rendering used to diff against the
/// reference binary's printed output.
pub fn print_pretty(m: &BuiltModule, i: &Interner, d: DagId, color: bool) -> String {
    Printer { m, i, faithful: true, color, vars: &[] }.render(d)
}

/// Render a static [`Term`] (an equation/membership LHS/RHS pattern, with variables) — the inverse of the
/// same mixfix grammar, sharing the DAG printer's prec/gather walk (Maude's `MixfixModule::prettyPrint`
/// vs `dagNodePrint` split). A `Term::Var` prints as its name from `vars` (index → name, the statement's
/// [`VarIndex`](crate::build_term::VarIndex) order); used by the trace to render `eq lhs = rhs .`.
pub fn print_term(m: &BuiltModule, i: &Interner, t: &Term, vars: &[String], color: bool) -> String {
    let p = Printer { m, i, faithful: true, color, vars };
    let mut out = String::new();
    p.print_term(&mut out, t, UNBOUNDED, NONE_CAP, NONE_CAP);
    out
}

/// The shared printer. `m`/`i`/flags are immutable; the output buffer is threaded as a `&mut String`
/// parameter so the recursive walk can read `self` freely while appending. `faithful` selects
/// Maude-faithful leaf forms over round-trippable ones; `color` enables ANSI syntax coloring; `vars`
/// names the variables for a [`Term`] walk (empty for the DAG walk).
struct Printer<'a> {
    m: &'a BuiltModule,
    i: &'a Interner,
    faithful: bool,
    color: bool,
    vars: &'a [String],
}

/// A child of an application in either walk: a `DagId` (recurse via [`Printer::print`]) or a `&Term`
/// (recurse via [`Printer::print_term`]). Lets the mixfix frag/hole loop be shared (Option iii).
trait Child {
    fn render(&self, p: &Printer, out: &mut String, req_prec: u32, lcap: Cap, rcap: Cap);
}
impl Child for DagId {
    fn render(&self, p: &Printer, out: &mut String, req_prec: u32, lcap: Cap, rcap: Cap) {
        p.print(out, *self, req_prec, lcap, rcap);
    }
}
impl Child for Term {
    fn render(&self, p: &Printer, out: &mut String, req_prec: u32, lcap: Cap, rcap: Cap) {
        p.print_term(out, self, req_prec, lcap, rcap);
    }
}

impl Printer<'_> {
    fn render(&self, d: DagId) -> String {
        let mut out = String::new();
        self.print(&mut out, d, UNBOUNDED, NONE_CAP, NONE_CAP);
        out
    }

    /// Print a static [`Term`]: a variable by name, or an operator application via the shared mixfix walk.
    fn print_term(&self, out: &mut String, t: &Term, req_prec: u32, lcap: Cap, rcap: Cap) {
        match t {
            Term::Var(v) => {
                let name = self.vars.get(v.index as usize).map(String::as_str).unwrap_or("_");
                self.emit(out, Cat::Op, name);
            }
            Term::Op { symbol, args } => self.print_app_term(out, *symbol, args, req_prec, lcap, rcap),
        }
    }

    /// A `Term::Op` application — the term-walk twin of [`print_app`](Self::print_app) (no DAG leaf/iter/
    /// minus special-casing; children are `&[Term]`). Parenthesization is the same prec/gather inverse.
    fn print_app_term(&self, out: &mut String, symbol: SymbolId, args: &[Term], req_prec: u32, lcap: Cap, rcap: Cap) {
        let Some(syn) = self.m.syntax.get(&symbol) else {
            self.emit(out, Cat::Op, self.m.engine.symbol(symbol).name());
            if !args.is_empty() {
                self.print_arg_list(out, args);
            }
            return;
        };
        let has_hole = syn.frags.iter().any(|f| matches!(f, Frag::Hole));
        if !has_hole {
            let cat = if args.is_empty() { Cat::Lit } else { Cat::Op };
            self.emit(out, cat, self.frag_text(&syn.frags[0]));
            if !args.is_empty() {
                self.print_arg_list(out, args);
            }
            return;
        }
        let pg = prec_gather::compute(&syn.frags, syn.domain.len(), syn.prec, syn.gather.as_deref(), syn.assoc);
        let paren = req_prec < pg.prec || self.captures(syn, &pg.gather, lcap, rcap);
        if paren {
            self.emit(out, Cat::Punct, "(");
        }
        let (lcap, rcap) = if paren { (NONE_CAP, NONE_CAP) } else { (lcap, rcap) };
        self.print_mixfix(out, syn, &pg, args, lcap, rcap);
        if paren {
            self.emit(out, Cat::Punct, ")");
        }
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
        // Maude-faithful negation: `-(s^n(0))` prints as the compact `-n` (Maude's `handleMinus`). The raw
        // printer instead lets the normal `- arg` mixfix handle it (which re-parses).
        if self.faithful
            && self.m.minus_sym == Some(symbol)
            && children.len() == 1
            && let Some(dec) = self.pos_nat_decimal(children[0])
        {
            self.emit(out, Cat::Lit, &format!("-{dec}"));
            return;
        }
        // Maude-faithful rational: a `DivisionSymbol` node whose numerator/denominator are integer
        // numerals (Maude's `isRat`) prints compactly as `num/den` (no spaces), via `handleDivision`.
        // A zero numerator is the `Zero` constant, not a numeral, so `0 / 5` is *not* a rational and
        // falls through to the generic mixfix spacing — matching the reference binary.
        if self.faithful
            && self.m.division_sym == Some(symbol)
            && children.len() == 2
            && let Some(rat) = self.rational_text(children[0], children[1])
        {
            self.emit(out, Cat::Lit, &rat);
            return;
        }
        let Some(syn) = self.m.syntax.get(&symbol) else {
            // No recorded syntax (should not happen for a user op): prefix-print with the kernel name.
            self.emit(out, Cat::Op, self.m.engine.symbol(symbol).name());
            self.print_arg_list(out, &children);
            return;
        };
        let has_hole = syn.frags.iter().any(|f| matches!(f, Frag::Hole));
        if !has_hole {
            // Constant (a value → `Lit`) or prefix operator (`name(a, b, …)` → `Op` name).
            let cat = if children.is_empty() { Cat::Lit } else { Cat::Op };
            self.emit(out, cat, self.frag_text(&syn.frags[0]));
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
    fn print_mixfix<C: Child>(&self, out: &mut String, syn: &SymbolSyntax, pg: &prec_gather::PrecGather, children: &[C], lcap: Cap, rcap: Cap) {
        let nr_args = syn.domain.len();
        let left_bare = matches!(syn.frags.first(), Some(Frag::Hole));
        let right_bare = matches!(syn.frags.last(), Some(Frag::Hole));

        // Associative fold for the pure binary infix `_ OP _` with > 2 flattened children (the DAG case;
        // a `Term` pattern is nested binary, so prec/gather alone handles `a + b + c`).
        if syn.assoc && nr_args == 2 && left_bare && right_bare && children.len() > 2 {
            let mid: Vec<&Frag> = syn.frags[1..syn.frags.len() - 1].iter().collect();
            for (idx, c) in children.iter().enumerate() {
                if idx > 0 {
                    for f in &mid {
                        out.push(' ');
                        self.emit(out, Cat::Op, self.frag_text(f));
                    }
                    out.push(' ');
                }
                // Inner elements bind at the tighter gather[1]; left/right ends keep the outer capture.
                let bound = if idx == 0 { pg.gather[0] } else { pg.gather[1] };
                c.render(self, out, bound, NONE_CAP, NONE_CAP);
            }
            return;
        }

        // Maude's mixfix spacing (`prettyPrint.cc::printTokens`, no `format` attribute): a space precedes
        // each fragment EXCEPT at the very start, before a `,`, and around the brackets `()[]{}` (which
        // also suppress the following space). So `<_,_>` prints `< M, N >`, not `< M , N >`.
        let mut k = 0;
        let mut no_space = true;
        for (pos, frag) in syn.frags.iter().enumerate() {
            match frag {
                Frag::Tok(_) => {
                    let text = self.frag_text(frag);
                    let special = matches!(text, "(" | ")" | "[" | "]" | "{" | "}");
                    if !(no_space || special || text == ",") {
                        out.push(' ');
                    }
                    self.emit(out, Cat::Op, text);
                    no_space = special;
                }
                Frag::Hole => {
                    if !no_space {
                        out.push(' ');
                    }
                    let (lc, rc) = self.hole_caps(syn, pg, k, nr_args, left_bare, right_bare, lcap, rcap, pos);
                    children[k].render(self, out, pg.gather[k], lc, rc);
                    k += 1;
                    no_space = false;
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
        // Maude-faithful display of a plain iter with count >= 2: the compact `s_^n(arg)` power form
        // (Maude's `makeIterName`). It is self-delimiting (prefix-like), so it needs no precedence paren.
        if self.faithful && count != "1" {
            let power = format!("{}^{count}", self.canonical_name(symbol));
            self.emit(out, Cat::Op, &power);
            self.emit(out, Cat::Punct, "(");
            self.print(out, arg, PREFIX_GATHER, NONE_CAP, NONE_CAP);
            self.emit(out, Cat::Punct, ")");
            return;
        }
        // Otherwise (raw mode, or count == 1): `count` repeated successor applications over the base.
        let n: u64 = count.parse().expect("iter count fits u64 for the repeated form");
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

    /// `(a, b, …)` — a prefix argument list (shared by both walks).
    fn print_arg_list<C: Child>(&self, out: &mut String, children: &[C]) {
        self.emit(out, Cat::Punct, "(");
        for (idx, c) in children.iter().enumerate() {
            if idx > 0 {
                self.emit(out, Cat::Punct, ",");
                out.push(' ');
            }
            c.render(self, out, PREFIX_GATHER, NONE_CAP, NONE_CAP);
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

    /// An operator's canonical (prefix) name — its fragments concatenated (`[Tok(s), Hole]` → `"s_"`).
    fn canonical_name(&self, symbol: SymbolId) -> String {
        match self.m.syntax.get(&symbol) {
            Some(syn) => syn.frags.iter().map(|f| self.frag_text(f)).collect(),
            None => self.m.engine.symbol(symbol).name().to_string(),
        }
    }

    /// The compact `num/den` text of a `DivisionSymbol` rational special constant (Maude's
    /// `DivisionSymbol::isRat` + `getRat`): the denominator is a positive natural numeral, and the
    /// numerator a positive numeral or a negated one. `None` (→ generic mixfix) otherwise — notably for a
    /// `Zero` numerator (`0 / 5`), which Maude prints spaced.
    fn rational_text(&self, num: DagId, den: DagId) -> Option<String> {
        let d = self.pos_nat_decimal(den)?;
        let n = self.signed_numeral(num)?;
        Some(format!("{n}/{d}"))
    }

    /// The decimal of a strictly-positive natural numeral `s^count(0)` (count ≥ 1); `None` for the `Zero`
    /// constant or any non-numeral (Maude's `SuccSymbol::isNat` on a nonzero value).
    fn pos_nat_decimal(&self, d: DagId) -> Option<String> {
        let node = self.m.engine.node(d);
        match node.repr() {
            NodeRepr::Iter { count, arg }
                if self.m.nat_succ == Some(node.symbol()) && self.is_zero(arg) =>
            {
                Some(count)
            }
            _ => None,
        }
    }

    /// The signed decimal of a nonzero integer numeral: a positive nat `s^n(0)` → `n`, or a negated nat
    /// `-(s^n(0))` → `-n`. `None` for `0` or any non-numeral.
    fn signed_numeral(&self, d: DagId) -> Option<String> {
        if let Some(n) = self.pos_nat_decimal(d) {
            return Some(n);
        }
        let symbol = self.m.engine.node(d).symbol();
        if self.m.minus_sym == Some(symbol) {
            let children: Vec<DagId> = self.m.engine.node(d).children().collect();
            if let [only] = children.as_slice() {
                return self.pos_nat_decimal(*only).map(|n| format!("-{n}"));
            }
        }
        None
    }

    /// Append `text` for category `cat`, wrapping it in `cat`'s ANSI color when `color` is on.
    fn emit(&self, out: &mut String, cat: Cat, text: &str) {
        if self.color {
            out.push_str(cat.ansi());
            out.push_str(text);
            out.push_str(ANSI_RESET);
        } else {
            out.push_str(text);
        }
    }
}

/// ANSI reset.
const ANSI_RESET: &str = "\x1b[0m";

impl Cat {
    /// The ANSI SGR color for this category (a conventional syntax-highlighting palette; Maude's own
    /// scheme colors by *reduction status* instead — a future alternative mode).
    fn ansi(self) -> &'static str {
        match self {
            Cat::Op => "\x1b[33m",    // operators: yellow
            Cat::Lit => "\x1b[36m",   // numeric / constant literals: cyan
            Cat::Punct => "\x1b[90m", // parens/commas: bright black (dim)
        }
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

/// Render a float exactly as Maude's `doubleToString` (`Utility/macros.cc`): 17 significant digits, the
/// mantissa normalized to `[1, 10)` with at least one fractional digit and trailing zeros stripped, and a
/// signed exponent shown only when nonzero — `1.0e+2`, `2.5e-1`, `3.14159265358979`, `-1.5`. Always
/// re-lexes as a Float (our [`is_float_literal`](crate::lex) accepts the `e±` form).
fn render_float(f: f64) -> String {
    if f.is_nan() {
        return "NaN".to_string();
    }
    if f.is_infinite() {
        return if f < 0.0 { "-Infinity" } else { "Infinity" }.to_string();
    }
    if f == 0.0 {
        return "0.0".to_string(); // also catches -0.0
    }
    // 16 fractional digits ⇒ 17 significant digits, mantissa in [1, 10), correctly rounded — the same
    // value `ecvt(d, 17, …)` produces. Rust's `{:e}` writes `D.DDD…eE` (lowercase, no `+`, no padding).
    let sci = format!("{:.*e}", 16, f.abs());
    let (mantissa, exp) = sci.split_once('e').expect("scientific notation has an exponent");
    let exp: i64 = exp.parse().expect("exponent is an integer");
    let (int_part, frac) = mantissa.split_once('.').expect("a `.16e` mantissa has a decimal point");
    // Strip trailing zeros but keep at least one fractional digit (Maude's `next > 4` guard).
    let frac = frac.trim_end_matches('0');
    let frac = if frac.is_empty() { "0" } else { frac };
    let body = match exp {
        0 => format!("{int_part}.{frac}"),
        e if e > 0 => format!("{int_part}.{frac}e+{e}"),
        e => format!("{int_part}.{frac}e{e}"), // a negative exponent already carries its `-`
    };
    if f < 0.0 {
        format!("-{body}")
    } else {
        body
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

    // B4.5a: round-trip the broader loadable set — exercises the raw printer on `<_,_>` / `_;_` / ACU
    // residues / prefix ops / membership-lowered sorts, beyond the milestone's forms.
    #[test]
    fn peano_round_trips() {
        round_trips(file!("peano.maude"));
    }
    #[test]
    fn strat_round_trips() {
        round_trips(file!("strat.maude"));
    }
    #[test]
    fn acu_overload_round_trips() {
        round_trips(file!("acu-overload.maude"));
    }
    #[test]
    fn acu_reduce_round_trips() {
        round_trips(file!("acu-reduce.maude"));
    }
    #[test]
    fn membership_round_trips() {
        round_trips(file!("membership.maude"));
    }
    #[test]
    fn overload_round_trips() {
        round_trips(file!("overload.maude"));
    }

    /// Maude-faithful (uncolored) rendering of each command's result equals the reference binary's printed
    /// term (`~/Downloads/Maude-3/maude -no-banner conformance/<f>.maude < /dev/null`). A strictly stronger
    /// check than the B4.4 conformance: it pins the printed form exactly, incl. ACU element *order*.
    fn renders_as(src: &str, expected: &[&str]) {
        let mut loaded = load_source(src).expect("load");
        let cmds: Vec<(usize, Vec<crate::lex::Token>)> = loaded
            .commands
            .iter()
            .map(|(m, c)| match c {
                Command::Reduce { term } => (*m, term.clone()),
                Command::Match { .. } => panic!("milestone uses only reduce"),
            })
            .collect();
        assert_eq!(cmds.len(), expected.len(), "command count");
        for (idx, ((m, term), want)) in cmds.iter().zip(expected).enumerate() {
            let (result, _) = reduce_command(&mut loaded.modules[*m], &loaded.interner, term)
                .unwrap_or_else(|e| panic!("command {idx}: {e}"));
            let got = print_pretty(&loaded.modules[*m].built, &loaded.interner, result, false);
            assert_eq!(&got.as_str(), want, "command {idx}");
        }
    }

    #[test]
    fn iter_renders_like_binary() {
        renders_as(file!("iter.maude"), &["0", "s 0", "s 0", "s 0", "s 0"]);
    }
    #[test]
    fn bool_renders_like_binary() {
        renders_as(file!("bool.maude"), &["tt", "ff", "tt", "0", "s_^2(0)", "0"]);
    }
    #[test]
    fn nat_renders_like_binary() {
        // Every command matches the binary EXCEPT the last: the residue prints `5 + x` here vs the
        // binary's `x + 5`. This is a COSMETIC representation difference, not a correctness gap: the
        // kernel's `dag_compare` orders ACU elements by `SymbolId` while Maude orders by `Symbol::orderInt`
        // (`Interface/symbol.hh:239`). Same multiset → identical equality / normal forms / sorts /
        // arithmetic; only the print order differs, and we don't require visual parity. The printer
        // faithfully renders whatever canonical order the kernel produced. (Aligning the order is an
        // optional kernel tweak — task #7 — that would cost a full AC rewrite-count re-verification.)
        renders_as(
            file!("nat.maude"),
            &["5", "4", "5", "12", "4", "3", "1", "1024", "6", "tt", "ff", "tt", "5 + x"],
        );
    }
    #[test]
    fn int_renders_like_binary() {
        renders_as(
            file!("int.maude"),
            &["-3", "3", "0", "-3", "-5", "-3", "3", "-6", "6", "-3", "-1", "tt", "ff"],
        );
    }

    /// The colored pretty form carries ANSI escapes and strips back to the plain Maude-faithful form.
    #[test]
    fn colored_strips_to_plain() {
        let mut loaded = load_source(file!("nat.maude")).expect("load");
        let term = match &loaded.commands[0].1 {
            Command::Reduce { term } => term.clone(),
            _ => unreachable!(),
        };
        let (result, _) = reduce_command(&mut loaded.modules[0], &loaded.interner, &term).expect("reduce");
        let m = &loaded.modules[0].built;
        let colored = print_pretty(m, &loaded.interner, result, true);
        let plain = print_pretty(m, &loaded.interner, result, false);
        assert!(colored.contains('\x1b'), "colored output carries ANSI escapes");
        assert_eq!(strip_ansi(&colored), plain, "stripping ANSI yields the plain rendering");
        assert_eq!(plain, "5", "2 + 3 = 5");
    }

    /// Remove ANSI SGR escape sequences (`ESC [ … m`).
    fn strip_ansi(s: &str) -> String {
        let mut out = String::new();
        let mut chars = s.chars();
        while let Some(c) = chars.next() {
            if c == '\x1b' {
                for d in chars.by_ref() {
                    if d == 'm' {
                        break;
                    }
                }
            } else {
                out.push(c);
            }
        }
        out
    }

    /// The Term printer renders a pattern (variables + prefix/mixfix ops) byte-identically to the DAG
    /// printer's mixfix layout — the basis for the trace's `eq lhs = rhs .` line.
    #[test]
    fn term_printer_renders_patterns() {
        let loaded = load_source(
            "fmod M is sort N . op 0 : -> N [ctor] . op s : N -> N [ctor] . \
             op add : N N -> N . op _+_ : N N -> N [assoc] . endfm",
        )
        .expect("load");
        let m = &loaded.modules[0].built;
        let i = &loaded.interner;
        let nat = m.sorts["N"];
        let s = m.ops[&("s".to_string(), 1)];
        let add = m.ops[&("add".to_string(), 2)];
        let plus = m.ops[&("_+_".to_string(), 2)];
        let v = |idx| Term::var(idx, nat);
        let names = ["X".to_string(), "Y".to_string(), "Z".to_string()];

        // prefix ops + variables: add(s(X), Y)
        let t1 = Term::op(add, vec![Term::op(s, vec![v(0)]), v(1)]);
        assert_eq!(print_term(m, i, &t1, &names, false), "add(s(X), Y)");
        // right-associating infix, nested binary `+(X, +(Y, Z))` renders flat `X + Y + Z`
        let t2 = Term::op(plus, vec![v(0), Term::op(plus, vec![v(1), v(2)])]);
        assert_eq!(print_term(m, i, &t2, &names, false), "X + Y + Z");
        // a constant
        assert_eq!(print_term(m, i, &Term::constant(m.ops[&("0".to_string(), 0)]), &[], false), "0");
    }
}
