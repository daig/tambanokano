//! The pretty-printer: a reduced `DagNode` → surface text. Two products share one core walk:
//! - [`print_raw`] — a **round-trippable** plain rendering (`parse∘print = id`): emits forms our parser
//!   reads back (decimal numerals, compact `f^N(t)` for iter counts ≥ 2, `- 3` spaced for negation).
//! - [`print_pretty`] (B4.6c) — a **Maude-faithful** rendering with optional ANSI syntax coloring, for
//!   interactive use (and, uncolored, for the textual diff against the reference binary).
//!
//! The walk is the inverse of the B4.3 grammar + B4.4 parser: parenthesization is the exact inverse of the
//! Earley prec/gather gate — a subterm of precedence `prec` is wrapped iff the position's gather bound
//! `required_prec < prec` (plus Maude's `LEFT_BARE`/`RIGHT_BARE` adjacency "capture" cases). Ported from
//! `Mixfix/dagNodePrint.cc::prettyPrint`. Reads only the frontend's [`SymbolSyntax`] tables + the public
//! kernel accessors (`DagNode::{repr,symbol,children}`).

use crate::grammar::{PREFIX_GATHER, prec_gather};
use crate::lex::{Frag, Interner, Sym};
use crate::sig::syntax::{BuiltModule, SymbolSyntax};
use std::borrow::Cow;
use tnk_core::Nat;
use tnk_core::dag::{DagId, NaValue, NodeRepr};
use tnk_core::smt::SmtNumber;
use tnk_core::sort::KindId;
use tnk_core::symbol::SymbolId;
use tnk_core::term::Term;

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
const NONE_CAP: Cap = Cap {
    prec: UNBOUNDED,
    kind: None,
};

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

/// Render `d` (a reduced node) as round-trippable plain text: `parse(print_raw(t)) == t`. Iter counts
/// ≥ 2 print in compact power form and negation as `- n`, both forms our parser reads back.
pub fn print_raw(m: &BuiltModule, i: &Interner, d: DagId) -> String {
    Printer {
        m,
        i,
        faithful: false,
        color: false,
        mixfix: true,
        number: true,
        rational: false,
        vars: &[],
    }
    .render(d)
}

/// Render `d` for interactive display: Maude-faithful forms (`s_^n(0)`, `-3`) with optional ANSI syntax
/// coloring. With `color = false` this is the Maude-faithful plain rendering used to diff against the
/// reference binary's printed output.
pub fn print_pretty(m: &BuiltModule, i: &Interner, d: DagId, color: bool) -> String {
    Printer {
        m,
        i,
        faithful: true,
        color,
        mixfix: true,
        number: true,
        rational: true,
        vars: &[],
    }
    .render(d)
}

/// Render a symbolic DAG while naming variable slots from the command's source-variable table.
pub fn print_pretty_with_variables(
    m: &BuiltModule,
    i: &Interner,
    d: DagId,
    variables: &[String],
    color: bool,
) -> String {
    Printer {
        m,
        i,
        faithful: true,
        color,
        vars: variables,
        mixfix: true,
        number: true,
        rational: true,
    }
    .render(d)
}

/// Render a DAG with META-LEVEL's independently selectable `mixfix`, `number`, and `rat` options.
/// This is deliberately separate from [`print_pretty`]: omitted options expose the underlying
/// successor/division constructors rather than silently inheriting the interactive defaults.
pub fn print_with_options(
    m: &BuiltModule,
    i: &Interner,
    d: DagId,
    mixfix: bool,
    number: bool,
    rational: bool,
) -> String {
    Printer {
        m,
        i,
        faithful: true,
        color: false,
        vars: &[],
        mixfix,
        number,
        rational,
    }
    .render(d)
}

/// Render a static [`Term`] (an equation/membership LHS/RHS pattern, with variables) — the inverse of the
/// same mixfix grammar, sharing the DAG printer's prec/gather walk (Maude's `MixfixModule::prettyPrint`
/// vs `dagNodePrint` split). A `Term::Var` prints as its name from `vars` (index → name, the statement's
/// [`VarIndex`](crate::build_term::VarIndex) order); used by the trace to render `eq lhs = rhs .`.
pub fn print_term(m: &BuiltModule, i: &Interner, t: &Term, vars: &[String], color: bool) -> String {
    Printer {
        m,
        i,
        faithful: true,
        color,
        vars,
        mixfix: true,
        number: true,
        rational: true,
    }
    .print_term_top(t)
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
    mixfix: bool,
    number: bool,
    rational: bool,
}

/// A child to lay out in either walk: a reduced DAG node, or a static [`Term`] (pattern) node. Unifies the
/// DAG printer (`print_raw`/`print_pretty`) and the `Term` printer (`print_term`, for the trace) under one
/// iterative driver.
#[derive(Clone, Copy)]
enum Item<'t> {
    Dag(DagId),
    Term(&'t Term),
}

/// One pending unit of output on the explicit work-stack. The recursive descent of the former
/// `print`/`print_app`/… is replaced by this stack, so a very deep subject — e.g. `s^17711(0)` from
/// `fib(22)`, a plain-`ctor` tower — can't overflow the *call* stack (the same iterative treatment A1 gave
/// `reduce`/`deep_equal`; the depth now lives in this heap `Vec`). `Text` is a colored emission; `Space` is
/// a raw inter-token space (Maude never colors whitespace); `Visit` is expanded by [`Printer::layout`].
enum Work<'a, 't> {
    Text {
        cat: Cat,
        text: Cow<'a, str>,
    },
    Space,
    /// A `format`-attribute newline (`n`) — `\n` with no trailing space.
    Newline,
    /// A `format`-attribute indent (`i`) — spaces to the current indentation level.
    Indent,
    /// A `format`-attribute indent-level change (`+`/`-`) — no output, shifts later `Indent`s.
    IndentDelta(i32),
    Visit {
        item: Item<'t>,
        req_prec: u32,
        lcap: Cap,
        rcap: Cap,
        range_known: bool,
        top_level: bool,
    },
}

impl<'a> Printer<'a> {
    fn render(&self, d: DagId) -> String {
        let mut out = String::new();
        self.run_stack(&mut out, Item::Dag(d));
        out
    }

    /// Print a static [`Term`] (a pattern, with named variables) — the trace's `eq lhs = rhs .` renderer.
    fn print_term_top(&self, t: &Term) -> String {
        let mut out = String::new();
        self.run_stack(&mut out, Item::Term(t));
        out
    }

    /// Drive the explicit work-stack: pop a unit and emit text / a space, or expand a node into more work.
    /// [`layout`](Self::layout) yields a node's pieces in forward order; they are pushed *reversed* so a
    /// LIFO `pop` replays them — and, transitively, their children — in emission order. The recursion depth
    /// of the former walk now lives in this heap `Vec`, so an arbitrarily deep subject can't overflow the
    /// call stack.
    fn run_stack<'t>(&self, out: &mut String, start: Item<'t>) {
        // The top-level term's range is not known from any context (Maude prints it with `rangeKnown`
        // false), so an ambiguous top constant is disambiguated.
        let mut stack: Vec<Work<'a, 't>> = vec![Work::Visit {
            item: start,
            req_prec: UNBOUNDED,
            lcap: NONE_CAP,
            rcap: NONE_CAP,
            range_known: false,
            top_level: true,
        }];
        let mut pieces: Vec<Work<'a, 't>> = Vec::new();
        // The `format`-attribute indentation level (in spaces), shifted by `+`/`-` directives as the walk
        // proceeds; an `Indent` emits this many spaces. `+`/`-` are balanced within each format op, so it
        // returns to 0 between top-level pieces.
        let mut indent: i32 = 0;
        while let Some(w) = stack.pop() {
            match w {
                Work::Text { cat, text } => self.emit(out, cat, &text),
                Work::Space => out.push(' '),
                Work::Newline => out.push('\n'),
                Work::Indent => {
                    for _ in 0..indent.max(0) {
                        out.push(' ');
                    }
                }
                Work::IndentDelta(d) => indent += d,
                Work::Visit {
                    item,
                    req_prec,
                    lcap,
                    rcap,
                    range_known,
                    top_level,
                } => {
                    self.layout(
                        item,
                        req_prec,
                        lcap,
                        rcap,
                        range_known,
                        top_level,
                        &mut pieces,
                    );
                    stack.extend(pieces.drain(..).rev());
                }
            }
        }
    }

    /// Lay out ONE node into its forward piece sequence — emitting `Text`/`Space` and pushing each child as
    /// a `Visit` (no recursion into children). Ports the dispatch of the former `print`/`print_term`.
    fn layout<'t>(
        &self,
        item: Item<'t>,
        req_prec: u32,
        lcap: Cap,
        rcap: Cap,
        range_known: bool,
        top_level: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        match item {
            Item::Term(Term::Var(v)) => {
                let name = self
                    .vars
                    .get(v.index as usize)
                    .map(String::as_str)
                    .unwrap_or("_");
                out.push(Work::Text {
                    cat: Cat::Op,
                    text: Cow::Borrowed(name),
                });
            }
            Item::Term(Term::Op { symbol, args }) => {
                // A `nat_succ` tower over `nat_zero` folds to its decimal — `f(2)`, not `f(s s 0)`.
                // Static terms may mix ordinary unary `Op` layers with compact `Iter` runs; Maude folds
                // both when printing (fable-audit.md §3.3 B5).
                if let Some(dec) = self.term_nat_decimal(*symbol, args) {
                    out.push(Work::Text {
                        cat: Cat::Lit,
                        text: Cow::Owned(dec),
                    });
                } else {
                    // A `Term` (pattern, in a trace) has no inferred sort to disambiguate with, so its
                    // children keep `range_known` true (Maude does not disambiguate inside statement printing).
                    let children: Vec<Item> = args.iter().map(Item::Term).collect();
                    self.layout_app(*symbol, &children, req_prec, lcap, rcap, true, out);
                }
            }
            Item::Term(Term::Iter { symbol, count, arg }) => {
                let count = count.to_decimal();
                if self.m.nat_succ == Some(*symbol) && self.is_zero_term(arg) {
                    out.push(Work::Text {
                        cat: Cat::Lit,
                        text: Cow::Owned(count),
                    });
                } else {
                    self.layout_iter(*symbol, &count, Item::Term(arg), req_prec, lcap, rcap, out);
                }
            }
            // A built-in literal renders exactly as its DAG leaf would.
            Item::Term(Term::Na { symbol, value }) => {
                let text = match value {
                    NaValue::Str(s) => render_string(s),
                    NaValue::Qid(q) => render_qid(q),
                    NaValue::Float(bits) => render_float(f64::from_bits(*bits)),
                    NaValue::SmtNum(number) => self.smt_number_text(*symbol, number),
                };
                out.push(Work::Text {
                    cat: Cat::Lit,
                    text: Cow::Owned(text),
                });
            }
            Item::Dag(d) => self.layout_dag(d, req_prec, lcap, rcap, range_known, top_level, out),
        }
    }

    /// Lay out one DAG node: a leaf (numeral / string / qid / float), an `iter`, or an application (with the
    /// faithful minus/rational special cases). The `&node` borrow is released — owned leaf data, then a
    /// freshly-fetched child list — before the `&self` layout calls.
    fn layout_dag<'t>(
        &self,
        d: DagId,
        req_prec: u32,
        lcap: Cap,
        rcap: Cap,
        range_known: bool,
        top_level: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        let symbol = self.m.engine.node(d).symbol();
        let leaf = {
            let node = self.m.engine.node(d);
            match node.repr() {
                NodeRepr::App => None,
                NodeRepr::Iter { count, arg } => Some(Leaf::Iter { count, arg }),
                NodeRepr::Str(s) => Some(Leaf::Atom(render_string(s))),
                NodeRepr::Qid(q) => Some(Leaf::Atom(render_qid(q))),
                NodeRepr::Float(f) => Some(Leaf::Atom(render_float(f))),
                NodeRepr::SmtNum(number) => Some(Leaf::Atom(self.smt_number_text(symbol, number))),
                // A genuine variable leaf (symbolic-engine DAGs): `base:Sort`, the form Maude
                // prints for a `VariableDagNode` (only fresh `#n`/`%n`/`@n` variables survive into
                // printed unifiers, and those always print with their sort).
                NodeRepr::Var { name } => {
                    let base = node
                        .variable_index()
                        .and_then(|slot| self.vars.get(slot as usize))
                        .map(String::as_str)
                        .unwrap_or_else(|| self.i.resolve(crate::lex::Sym::from_raw(name)));
                    let text = if base.contains(':') {
                        base.to_string()
                    } else if matches!(base.as_bytes().first(), Some(b'#' | b'%' | b'@')) {
                        format!(
                            "{}:{}",
                            base,
                            self.m.engine.sorts().name(self.m.engine.sort_of(d))
                        )
                    } else {
                        base.to_string()
                    };
                    Some(Leaf::Atom(text))
                }
            }
        };
        match leaf {
            Some(Leaf::Atom(text)) => out.push(Work::Text {
                cat: Cat::Lit,
                text: Cow::Owned(text),
            }),
            Some(Leaf::Iter { count, arg }) => {
                // A Nat numeral is a pseudo literal. In an unknown-range context Maude qualifies it only
                // if two kinds provide integer syntax (for example NAT plus SMT integers), or a nullary
                // user operator has the same numeric spelling.
                if !top_level
                    && !range_known
                    && self.m.nat_succ == Some(symbol)
                    && self.is_zero(arg)
                    && (self.m.integer_literal_kind_count > 1
                        || self.m.overloaded_naturals.contains(&count))
                {
                    let sort = self.m.engine.sorts().name(self.m.engine.sort_of(d));
                    out.push(Work::Text {
                        cat: Cat::Lit,
                        text: Cow::Owned(format!("({count}).{sort}")),
                    });
                } else {
                    self.layout_iter(symbol, &count, Item::Dag(arg), req_prec, lcap, rcap, out);
                }
            }
            None => {
                let children: Vec<DagId> = self.m.engine.node(d).children().collect();
                // Maude-faithful negation: `-(s^n(0))` → the compact `-n` (Maude's `handleMinus`). The raw
                // printer instead lets the normal `- arg` mixfix handle it (which re-parses).
                if self.faithful
                    && self.m.minus_sym == Some(symbol)
                    && children.len() == 1
                    && let Some(dec) = self.pos_nat_decimal(children[0])
                {
                    out.push(Work::Text {
                        cat: Cat::Lit,
                        text: Cow::Owned(format!("-{dec}")),
                    });
                    return;
                }
                // Maude-faithful rational: a `DivisionSymbol` node over integer numerals (Maude's `isRat`)
                // → the compact `num/den`. A zero numerator is the `Zero` constant, not a numeral, so
                // `0 / 5` falls through to the generic mixfix spacing — matching the reference binary.
                if self.rational
                    && self.m.division_sym == Some(symbol)
                    && children.len() == 2
                    && let Some(rat) = self.rational_text(children[0], children[1])
                {
                    out.push(Work::Text {
                        cat: Cat::Lit,
                        text: Cow::Owned(rat),
                    });
                    return;
                }
                let items: Vec<Item> = children.iter().map(|&c| Item::Dag(c)).collect();
                // Disambiguation (Maude `dagNodePrint.cc`): an ad-hoc-overloaded symbol whose range is not
                // determined by context prints `(t).Sort` so the output round-trips. The wrap is emitted
                // around the whole application, and the arguments inherit a possibly-unknown range.
                let need_disambig = !range_known && self.ambiguous(symbol);
                let arg_rk = self.range_of_args_known(symbol, range_known, need_disambig);
                if need_disambig {
                    out.push(Work::Text {
                        cat: Cat::Punct,
                        text: Cow::Borrowed("("),
                    });
                }
                self.layout_app(symbol, &items, req_prec, lcap, rcap, arg_rk, out);
                if need_disambig {
                    let sort = self.m.engine.sorts().name(self.m.engine.sort_of(d));
                    out.push(Work::Text {
                        cat: Cat::Punct,
                        text: Cow::Owned(format!(").{sort}")),
                    });
                }
            }
        }
    }

    /// Lay out an application from its symbol + already-extracted child [`Item`]s: prefix/constant, or a
    /// mixfix form with the prec/gather parenthesization (the inverse of the parser's gather gate, plus the
    /// adjacency-capture cases). Shared by the DAG and `Term` walks.
    #[allow(clippy::too_many_arguments)]
    fn layout_app<'t>(
        &self,
        symbol: SymbolId,
        children: &[Item<'t>],
        req_prec: u32,
        lcap: Cap,
        rcap: Cap,
        arg_rk: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        let command_arguments = self.m.engine.symbol(symbol).is_meta_operation();
        if !self.mixfix {
            out.push(Work::Text {
                cat: if children.is_empty() {
                    Cat::Lit
                } else {
                    Cat::Op
                },
                text: Cow::Borrowed(self.m.engine.symbol(symbol).name()),
            });
            if !children.is_empty() {
                self.layout_arg_list(children, arg_rk, command_arguments, out);
            }
            return;
        }
        let Some(syn) = self.m.syntax.get(&symbol) else {
            // No recorded syntax (should not happen for a user op): prefix-print with the kernel name.
            out.push(Work::Text {
                cat: Cat::Op,
                text: Cow::Borrowed(self.m.engine.symbol(symbol).name()),
            });
            if !children.is_empty() {
                self.layout_arg_list(children, arg_rk, command_arguments, out);
            }
            return;
        };
        let has_hole = syn.frags.iter().any(|f| matches!(f, Frag::Hole));
        if !has_hole {
            // Constant (a value → `Lit`) or prefix operator (`name(a, b, …)` → `Op` name). The name can be
            // several fragments when it lexes with punctuation (`[]`, `{}`, `<>` — split on `[`/`]`/…) or
            // with an inter-token blank (a multi-token name `a b`), so emit them all with Maude's default
            // spacing (a space before each fragment except at the start, before a `,`, and around brackets)
            // — `[]` stays glued, `a b` keeps its blank.
            let cat = if children.is_empty() {
                Cat::Lit
            } else {
                Cat::Op
            };
            let mut name = String::new();
            let mut no_space = true;
            for f in &syn.frags {
                let text = self.frag_cow(f);
                let special = matches!(&*text, "(" | ")" | "[" | "]" | "{" | "}");
                if !(no_space || special || &*text == ",") {
                    name.push(' ');
                }
                name.push_str(&text);
                no_space = special;
            }
            out.push(Work::Text {
                cat,
                text: Cow::Owned(name),
            });
            if !children.is_empty() {
                self.layout_arg_list(children, arg_rk, command_arguments, out);
            }
            return;
        }
        let pg = prec_gather::compute(
            &syn.frags,
            syn.domain.len(),
            syn.prec,
            syn.gather.as_deref(),
            syn.assoc,
        );
        let paren = req_prec < pg.prec || self.captures(syn, &pg.gather, lcap, rcap);
        if paren {
            out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Borrowed("("),
            });
        }
        // A surrounding paren blocks inherited capture (Maude inherits left/right capture only unparenthesized).
        let (lcap, rcap) = if paren {
            (NONE_CAP, NONE_CAP)
        } else {
            (lcap, rcap)
        };
        self.layout_mixfix(
            symbol,
            syn,
            &pg,
            children,
            lcap,
            rcap,
            arg_rk,
            command_arguments,
            out,
        );
        if paren {
            out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Borrowed(")"),
            });
        }
    }

    /// Lay out a mixfix form: walk the syntax fragments, emitting literal tokens and pushing each argument
    /// hole as a `Visit` (at its gather bound + adjacency context). An associative operator with more
    /// arguments than its arity folds its flattened children over the infix tokens (`a + b + c`).
    #[allow(clippy::too_many_arguments)]
    fn layout_mixfix<'t>(
        &self,
        symbol: SymbolId,
        syn: &SymbolSyntax,
        pg: &prec_gather::PrecGather,
        children: &[Item<'t>],
        lcap: Cap,
        rcap: Cap,
        arg_rk: bool,
        command_arguments: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        let nr_args = syn.domain.len();
        let left_bare = matches!(syn.frags.first(), Some(Frag::Hole));
        let right_bare = matches!(syn.frags.last(), Some(Frag::Hole));

        // Associative fold for the pure binary infix `_ OP _` with > 2 flattened children (the DAG case;
        // a `Term` pattern is nested binary, so prec/gather alone handles `a + b + c`). The between-section
        // (mid fragments + the gap before the next element) repeats per element, with the same default
        // spacing as the binary path — and the same `format`-attribute override (the META `__`
        // declaration/trace lists put each element on a new line, `format (d ni d)` / `(d n d)`).
        if syn.assoc && nr_args == 2 && left_bare && right_bare && children.len() > 2 {
            let format = syn
                .format
                .as_deref()
                .filter(|f| f.len() == syn.frags.len() + 1 && format_supported(f));
            let m = syn.frags.len() - 1; // the trailing Hole's index (`f0`/`f_m` are the two arg holes)
            emit_gap(format.map(|f| f[0].as_str()), false, out); // leading gap (before the first element)
            for (idx, c) in children.iter().enumerate() {
                if idx > 0 {
                    let mut no_space = false; // just emitted the previous element
                    for k in 1..m {
                        let text = self.frag_cow(&syn.frags[k]);
                        let special = matches!(&*text, "(" | ")" | "[" | "]" | "{" | "}");
                        emit_gap(
                            format.map(|f| f[k].as_str()),
                            !(no_space || special || &*text == ","),
                            out,
                        );
                        out.push(Work::Text { cat: Cat::Op, text });
                        no_space = special;
                    }
                    emit_gap(format.map(|f| f[m].as_str()), !no_space, out); // gap before the next element
                }
                // A flattened associative node prints as a left fold: every element except the final
                // right operand occupies the left gather position; only the final element uses gather[1].
                let bound = if idx + 1 == children.len() {
                    pg.gather[1]
                } else {
                    pg.gather[0]
                };
                out.push(Work::Visit {
                    item: *c,
                    req_prec: bound,
                    lcap: NONE_CAP,
                    rcap: NONE_CAP,
                    range_known: arg_rk || (command_arguments && self.is_nonzero_nat_item(*c)),
                    top_level: false,
                });
            }
            if let Some(f) = format {
                emit_gap(Some(f[m + 1].as_str()), false, out); // trailing gap
            }
            return;
        }

        // Maude's mixfix spacing (`prettyPrint.cc::printTokens`). Default (no `format` attribute): a space
        // precedes each fragment EXCEPT at the very start, before a `,`, around brackets `()[]{}`, and
        // between an ordinary literal label and its following `:` (`result:_` prints `result: value`).
        // Colons between holes remain spaced, so the type constructor `_ : _` is unaffected.
        // Thus `<_,_>` prints `< M, N >`, not `< M , N >`. With a
        // `format` attribute (the META result/declaration constructors — `_<-_`, `rl_=>_[_].`, …): one
        // directive word per **gap** (before each fragment, plus a trailing one), where `d` is exactly that
        // default, `s`/`n`/`i`/`+`/`-` the explicit space/newline/indent/level. An op whose format uses a
        // directive we don't model (`r`/`o`, on some IO/array ops) falls back to the default.
        let format = syn
            .format
            .as_deref()
            .filter(|f| f.len() == syn.frags.len() + 1 && format_supported(f));
        let object_colons = matches!(
            syn.frags.first(),
            Some(Frag::Tok(symbol)) if self.i.resolve(*symbol) == "<"
        ) && syn
            .frags
            .iter()
            .any(|frag| matches!(frag, Frag::Tok(symbol) if self.i.resolve(*symbol) == "|"));
        // Attribute constructors preserve whether their declaration spelled `label:_` compactly or
        // separated the label from `:_`; object notation exposes that source-level distinction.
        let spaced_label_colons = syn.spaced_label_colon;
        let mut k = 0;
        let mut no_space = true;
        for (pos, frag) in syn.frags.iter().enumerate() {
            let word = format.map(|f| f[pos].as_str());
            match frag {
                Frag::Tok(s) => {
                    let text = self.i.resolve(*s);
                    let special = matches!(text, "(" | ")" | "[" | "]" | "{" | "}");
                    let label_colon = text == ":"
                        && matches!(
                            pos.checked_sub(1).and_then(|p| syn.frags.get(p)),
                            Some(Frag::Tok(_))
                        );
                    let default_space = if spaced_label_colons && text == ":" {
                        true
                    } else if object_colons && text == ":" {
                        matches!(
                            pos.checked_sub(1).and_then(|p| syn.frags.get(p)),
                            Some(Frag::Hole)
                        )
                    } else if label_colon {
                        false
                    } else {
                        !(no_space || special || text == ",")
                    };
                    emit_gap(word, default_space, out);
                    out.push(Work::Text {
                        cat: Cat::Op,
                        text: Cow::Borrowed(text),
                    });
                    no_space = special || ((object_colons || spaced_label_colons) && text == ":");
                }
                Frag::Hole => {
                    let after_object_colon = (object_colons || spaced_label_colons)
                        && matches!(
                            pos.checked_sub(1).and_then(|p| syn.frags.get(p)),
                            Some(Frag::Tok(symbol)) if self.i.resolve(*symbol) == ":"
                        );
                    emit_gap(word, after_object_colon || !no_space, out);
                    let (lc, rc) =
                        self.hole_caps(syn, pg, k, nr_args, left_bare, right_bare, lcap, rcap, pos);
                    out.push(Work::Visit {
                        item: children[k],
                        req_prec: pg.gather[k],
                        lcap: lc,
                        rcap: rc,
                        range_known: arg_rk
                            || (command_arguments && self.is_nonzero_nat_item(children[k])),
                        top_level: false,
                    });
                    k += 1;
                    no_space = false;
                }
            }
        }
        // The trailing gap (after the last fragment): only its non-spacing directives matter (the `--` that
        // closes `_<-_`'s indent). A trailing default contributes nothing (no following token).
        if let Some(f) = format {
            emit_gap(Some(f[syn.frags.len()].as_str()), false, out);
        }
    }

    /// The adjacency-capture contexts for the `k`-th argument hole (Maude `dagNodePrint.cc:435-458`): a
    /// bare end abuts this op's token (`rc`/`lc` = this op's precedence + the arg's kind), and the outer
    /// capture flows through the opposite side.
    #[allow(clippy::too_many_arguments)]
    fn hole_caps(
        &self,
        syn: &SymbolSyntax,
        pg: &prec_gather::PrecGather,
        k: usize,
        nr_args: usize,
        left_bare: bool,
        right_bare: bool,
        lcap: Cap,
        rcap: Cap,
        _pos: usize,
    ) -> (Cap, Cap) {
        let sorts = self.m.engine.sorts();
        if k == 0 && left_bare {
            let rc = Cap {
                prec: pg.prec,
                kind: Some(sorts.kind_of(syn.domain[0])),
            };
            (lcap, rc)
        } else if k == nr_args - 1 && right_bare {
            let lc = Cap {
                prec: pg.prec,
                kind: Some(sorts.kind_of(syn.domain[nr_args - 1])),
            };
            (lc, rcap)
        } else {
            (NONE_CAP, NONE_CAP)
        }
    }

    /// Whether `symbol` must be disambiguated when its range is not known from context (Maude's
    /// `ambiguous`): another symbol shares its name *and* domain kinds, so the argument kinds alone do not
    /// select it. (Maude additionally disambiguates built-in literal lookalikes via the `PSEUDO` flags —
    /// a separate concern not needed by hand-rolled overloading.)
    fn ambiguous(&self, symbol: SymbolId) -> bool {
        self.m
            .overload
            .get(&symbol)
            .is_some_and(|f| f & crate::sig::syntax::OVL_DOMAIN != 0)
    }

    /// Whether the arguments of `symbol` have a known range (Maude's `rangeOfArgumentsKnown`): true unless
    /// `symbol` is ad-hoc overloaded and neither the context's range nor a just-emitted disambiguation pins
    /// the operator — in which case the arguments must each be unambiguous, so their range is unknown.
    fn range_of_args_known(
        &self,
        symbol: SymbolId,
        range_known: bool,
        range_disambiguated: bool,
    ) -> bool {
        use crate::sig::syntax::{OVL_ADHOC, OVL_RANGE};
        let f = self.m.overload.get(&symbol).copied().unwrap_or(0);
        if f & OVL_ADHOC == 0 {
            return true; // not overloaded ⇒ argument kinds are determined
        }
        f & OVL_RANGE == 0 && (range_known || range_disambiguated)
    }

    /// Maude's parent-side capture test: a bare end of this op would be captured by an abutting token of
    /// the same kind whose precedence the end's gather bound admits.
    fn captures(&self, syn: &SymbolSyntax, gather: &[u32], lcap: Cap, rcap: Cap) -> bool {
        let sorts = self.m.engine.sorts();
        let nr_args = syn.domain.len();
        let left_bare = matches!(syn.frags.first(), Some(Frag::Hole));
        let right_bare = matches!(syn.frags.last(), Some(Frag::Hole));
        (left_bare && lcap.prec <= gather[0] && lcap.kind == Some(sorts.kind_of(syn.domain[0])))
            || (right_bare
                && rcap.prec <= gather[nr_args - 1]
                && rcap.kind == Some(sorts.kind_of(syn.domain[nr_args - 1])))
    }

    /// Lay out `symbol^count(arg)`. A SuccSymbol numeral over the zero base becomes its decimal;
    /// every count ≥ 2 uses Maude's compact `f^N(arg)` name in both printer modes, so rendering a
    /// million-count iter node is independent of `N`. Count 1 uses the operator's ordinary syntax:
    /// a mixfix successor prints `s arg`, while a genuine prefix operator prints `g(arg)`.
    fn layout_iter<'t>(
        &self,
        symbol: SymbolId,
        count: &str,
        arg: Item<'t>,
        req_prec: u32,
        lcap: Cap,
        rcap: Cap,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        if self.number && self.m.nat_succ == Some(symbol) && self.is_zero_item(arg) {
            out.push(Work::Text {
                cat: Cat::Lit,
                text: Cow::Owned(count.to_string()),
            });
            return;
        }
        if count != "1" {
            let power = format!("{}^{count}", self.canonical_name(symbol));
            out.push(Work::Text {
                cat: Cat::Op,
                text: Cow::Owned(power),
            });
            out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Borrowed("("),
            });
            out.push(Work::Visit {
                item: arg,
                req_prec: PREFIX_GATHER,
                lcap: NONE_CAP,
                rcap: NONE_CAP,
                range_known: true,
                top_level: false,
            });
            out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Borrowed(")"),
            });
            return;
        }
        self.layout_app(symbol, &[arg], req_prec, lcap, rcap, true, out);
    }

    /// `(a, b, …)` — a prefix argument list (shared by both walks). `arg_rk` is the arguments' inherited
    /// `range_known` (false propagates disambiguation into them under an ad-hoc-overloaded operator).
    fn layout_arg_list<'t>(
        &self,
        children: &[Item<'t>],
        arg_rk: bool,
        command_arguments: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        out.push(Work::Text {
            cat: Cat::Punct,
            text: Cow::Borrowed("("),
        });
        for (idx, c) in children.iter().enumerate() {
            if idx > 0 {
                out.push(Work::Text {
                    cat: Cat::Punct,
                    text: Cow::Borrowed(","),
                });
                out.push(Work::Space);
            }
            out.push(Work::Visit {
                item: *c,
                req_prec: PREFIX_GATHER,
                lcap: NONE_CAP,
                rcap: NONE_CAP,
                range_known: arg_rk || (command_arguments && self.is_nonzero_nat_item(*c)),
                top_level: false,
            });
        }
        out.push(Work::Text {
            cat: Cat::Punct,
            text: Cow::Borrowed(")"),
        });
    }

    /// Nonzero Nat pseudo literals in META command arguments retain their source-style bare spelling.
    /// Zero is an ordinary constant and still receives Maude's `(0).Zero` disambiguation when required.
    fn is_nonzero_nat_item(&self, item: Item<'_>) -> bool {
        match item {
            Item::Dag(d) => {
                let node = self.m.engine.node(d);
                self.m.nat_succ == Some(node.symbol())
                    && matches!(node.repr(), NodeRepr::Iter { arg, .. } if self.is_zero(arg))
            }
            Item::Term(Term::Iter { symbol, arg, .. }) => {
                self.m.nat_succ == Some(*symbol) && self.is_zero_term(arg)
            }
            Item::Term(_) => false,
        }
    }

    /// Whether `arg` is the module's zero constant (so a successor over it is a numeral).
    fn is_zero(&self, arg: DagId) -> bool {
        self.m.nat_zero == Some(self.m.engine.node(arg).symbol())
    }

    fn is_zero_term(&self, arg: &Term) -> bool {
        matches!(
            arg,
            Term::Op { symbol, args } if self.m.nat_zero == Some(*symbol) && args.is_empty()
        )
    }

    fn is_zero_item(&self, arg: Item<'_>) -> bool {
        match arg {
            Item::Dag(d) => self.is_zero(d),
            Item::Term(t) => self.is_zero_term(t),
        }
    }

    fn frag_text(&self, frag: &Frag) -> &str {
        match frag {
            Frag::Tok(s) => self.tok_text(*s),
            Frag::Hole => "_",
        }
    }

    /// A fragment's text as a `Cow` borrowing the interner for the printer's lifetime `'a`, so it can sit on
    /// the work-stack outliving the `&self` call that produced it (an argument hole renders as `_`).
    fn frag_cow(&self, frag: &Frag) -> Cow<'a, str> {
        match frag {
            Frag::Tok(s) => Cow::Borrowed(self.i.resolve(*s)),
            Frag::Hole => Cow::Borrowed("_"),
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

    fn smt_number_text(&self, symbol: SymbolId, number: &SmtNumber) -> String {
        let range = self.m.syntax[&symbol].range;
        let kind = self
            .m
            .engine
            .smt_type(range)
            .expect("SMT number symbol without range metadata");
        number.to_maude(kind)
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

    /// The decimal of a strictly-positive natural numeral pattern: any mix of unary `nat_succ`
    /// applications and compact [`Term::Iter`] runs, bottoming at `nat_zero`. Iterative and bignum-backed,
    /// so neither a deep explicit tower nor a million-count compact run overflows or truncates.
    fn term_nat_decimal(&self, symbol: SymbolId, args: &[Term]) -> Option<String> {
        if self.m.nat_succ != Some(symbol) || args.len() != 1 {
            return None;
        }
        let mut count = Nat::one();
        let mut cur = &args[0];
        loop {
            match cur {
                Term::Op { symbol: s, args } if self.m.nat_succ == Some(*s) && args.len() == 1 => {
                    count = count.add(&Nat::one());
                    cur = &args[0];
                }
                Term::Iter {
                    symbol: s,
                    count: n,
                    arg,
                } if self.m.nat_succ == Some(*s) => {
                    count = count.add(n);
                    cur = arg;
                }
                Term::Op { symbol: s, args } if self.m.nat_zero == Some(*s) && args.is_empty() => {
                    return Some(count.to_decimal());
                }
                _ => return None,
            }
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

/// Whether every directive in `format` is one the printer interprets (`d s t n i + -`). If not — an `r`/`o`
/// or numeric directive, used by a few IO/array ops — the operator falls back to default spacing rather
/// than mis-render, so a partial format model never produces wrong output.
fn format_supported(format: &[String]) -> bool {
    format.iter().all(|w| {
        w.chars()
            .all(|c| matches!(c, 'd' | 's' | 't' | 'n' | 'i' | '+' | '-'))
    })
}

/// Push the [`Work`] for one `format` gap (or the no-format default if `word` is `None`): `d` is the
/// default space (`default_space`), `s` a space, `t` a tab, `n` a newline, `i` an indent to the current
/// level, `+`/`-` a level change. A multi-directive word (`n++i`, `ni`) emits each in turn.
fn emit_gap<'a, 't>(word: Option<&str>, default_space: bool, out: &mut Vec<Work<'a, 't>>) {
    let Some(w) = word else {
        if default_space {
            out.push(Work::Space);
        }
        return;
    };
    for c in w.chars() {
        match c {
            'd' if default_space => out.push(Work::Space),
            's' => out.push(Work::Space),
            't' => out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Borrowed("\t"),
            }),
            'n' => out.push(Work::Newline),
            'i' => out.push(Work::Indent),
            '+' => out.push(Work::IndentDelta(1)),
            '-' => out.push(Work::IndentDelta(-1)),
            _ => {} // `d` with no default space, or an unmodelled directive (filtered upstream)
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

/// Render a quoted identifier with its leading `'` and Maude's token-name escapes. Raw punctuation
/// gets a backtick; punctuation already carrying its canonical backtick is not escaped twice.
fn render_qid(q: &str) -> String {
    let mut out = String::with_capacity(q.len() + 1);
    out.push('\'');
    let mut escaped = false;
    for c in q.chars() {
        match c {
            '`' => {
                if !escaped {
                    out.push('`');
                }
                escaped = true;
            }
            ' ' => {
                if !escaped {
                    out.push('`');
                }
                escaped = true;
            }
            '(' | ')' | '[' | ']' | '{' | '}' | ',' => {
                if !escaped {
                    out.push('`');
                }
                out.push(c);
                escaped = false;
            }
            _ => {
                out.push(c);
                escaped = false;
            }
        }
    }
    out
}

/// A string constant (raw bytes) rendered with surrounding quotes and Maude's escaping (`Token::
/// ropeToString`): a printable ASCII byte (0x20–0x7E) verbatim (with `"` and `\` backslash-escaped), the
/// named control escapes `\a \b \f \n \r \t \v`, and EVERY other byte (0x00–0x06, 0x0E–0x1F, 0x7F, and
/// all of 0x80–0xFF) as a 3-digit octal `\ooo`. The output is pure ASCII — no raw control/high bytes.
pub fn render_string(s: &[u8]) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for &b in s {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            0x20..=0x7e => out.push(b as char), // printable ASCII, verbatim
            0x07 => out.push_str("\\a"),
            0x08 => out.push_str("\\b"),
            0x0c => out.push_str("\\f"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x0b => out.push_str("\\v"),
            _ => {
                // 0x00–0x06, 0x0E–0x1F, 0x7F, 0x80–0xFF → 3-digit octal.
                out.push('\\');
                out.push((b'0' + b / 64) as char);
                out.push((b'0' + (b / 8) % 8) as char);
                out.push((b'0' + b % 8) as char);
            }
        }
    }
    out.push('"');
    out
}

/// Render a float exactly as Maude's `doubleToString` — delegated to the kernel so the pretty-printer and
/// the `string(Float)` conversion render identically (see [`tnk_core::double_to_string`]).
pub fn render_float(f: f64) -> String {
    tnk_core::double_to_string(f)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::tokenize;
    use crate::load::{load_source, reduce_command};
    use crate::surface::ast::Command;

    /// Round-trip: every milestone command's reduced result, raw-printed and re-reduced, is `deep_equal`
    /// to the original result. Drives the existing load/reduce harness.
    fn round_trips(src: &str) {
        let mut loaded = load_source(src).expect("load");
        let cmds: Vec<(usize, Vec<crate::lex::Token>)> = loaded
            .commands
            .iter()
            .map(|(m, c)| match c {
                Command::Reduce { term, .. } => (*m, term.clone()),
                _ => panic!("milestone uses only reduce"),
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
            assert!(
                eng.deep_equal(result, reparsed),
                "command {idx}: `{printed}` did not round-trip"
            );
        }
    }

    macro_rules! file {
        ($n:expr) => {
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../conformance/",
                $n
            ))
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
                Command::Reduce { term, .. } => (*m, term.clone()),
                _ => panic!("milestone uses only reduce"),
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
    /// An ad-hoc-overloaded constant (`nil` in two kinds) prints disambiguated as `(nil).Sort` at top
    /// level so it round-trips; a unique constant (`a`) stays bare. Byte-identical to the reference.
    #[test]
    fn disambiguated_constant_renders_like_binary() {
        renders_as(
            file!("correctness-disambig.maude"),
            &["(nil).A", "(nil).B", "a"],
        );
    }
    #[test]
    fn bool_renders_like_binary() {
        renders_as(
            file!("bool.maude"),
            &["tt", "ff", "tt", "0", "s_^2(0)", "0"],
        );
    }
    #[test]
    fn nat_renders_like_binary() {
        // Every command matches the binary, including the last: the residue prints `x + 5`, exactly as
        // the reference does. The kernel's `dag_compare` now orders ACU elements by Maude's
        // `Symbol::orderInt` key — **arity first** (`orderInt = symbolCount | (arity << 24)`,
        // `Interface/symbol.{hh,cc}`), then creation index — so the nullary `x` sorts before the unary
        // `s^5(0)` (`5`), giving `x + 5`. (Before that fix it printed `5 + x`, a documented cosmetic
        // discrepancy; aligning the order made the object-configuration soups byte-identical too,
        // Pillar 2.5-A.)
        renders_as(
            file!("nat.maude"),
            &[
                "5", "4", "5", "12", "4", "3", "1", "1024", "6", "tt", "ff", "tt", "x + 5",
            ],
        );
    }
    #[test]
    fn int_renders_like_binary() {
        renders_as(
            file!("int.maude"),
            &[
                "-3", "3", "0", "-3", "-5", "-3", "3", "-6", "6", "-3", "-1", "tt", "ff",
            ],
        );
    }

    /// The colored pretty form carries ANSI escapes and strips back to the plain Maude-faithful form.
    #[test]
    fn colored_strips_to_plain() {
        let mut loaded = load_source(file!("nat.maude")).expect("load");
        let term = match &loaded.commands[0].1 {
            Command::Reduce { term, .. } => term.clone(),
            _ => unreachable!(),
        };
        let (result, _) =
            reduce_command(&mut loaded.modules[0], &loaded.interner, &term).expect("reduce");
        let m = &loaded.modules[0].built;
        let colored = print_pretty(m, &loaded.interner, result, true);
        let plain = print_pretty(m, &loaded.interner, result, false);
        assert!(
            colored.contains('\x1b'),
            "colored output carries ANSI escapes"
        );
        assert_eq!(
            strip_ansi(&colored),
            plain,
            "stripping ANSI yields the plain rendering"
        );
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
        assert_eq!(
            print_term(
                m,
                i,
                &Term::constant(m.ops[&("0".to_string(), 0)]),
                &[],
                false
            ),
            "0"
        );
    }
}
