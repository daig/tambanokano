//! Parse-forest extraction (Maude's `pass2`, DRP path omitted): walk the Earley [`Chart`] to build the
//! first parse tree for the start nonterminal, and flag ambiguity (a second valid parse anywhere).
//!
//! Reconstruction is right-to-left over each production's rhs (Maude's `extractFirstSubparse`,
//! pass2.cc:168): for a finished item spanning `[origin, end)`, walk its rhs from the right, peeling one
//! token per terminal and, at each nonterminal hole, finding a finished sub-item that ends at the current
//! position, whose precedence the hole's gather bound admits, and whose start `s` the prefix `rhs[0..k]`
//! actually reached (the `chart.contains(s, <prefix item>)` check — Maude's `existsCall`). The first such
//! split (in chart/completion order) is taken; a second flags ambiguity (Maude reports two and takes the
//! first).

use super::compile::CompiledGrammar;
use super::earley::{Chart, Item};
use crate::grammar::{GSym, Nt};

/// A concrete parse tree: the production applied, the token span `[start, end)`, and the subtrees for the
/// rhs **nonterminals** (left-to-right). Terminals are not stored as children — `build_term` reads any
/// literal/variable token it needs from `start` (each such production has a single leading terminal).
#[derive(Debug, Clone)]
pub struct PTree {
    pub prod: u32,
    pub start: usize,
    pub end: usize,
    pub nt_children: Vec<PTree>,
}

/// The outcome of extraction: the first parse tree and whether the input was ambiguous.
#[derive(Debug)]
pub struct Parse {
    pub tree: PTree,
    pub ambiguous: bool,
}

/// Extract the first parse for `start` from the chart, or an error describing why there is none.
pub fn extract(g: &CompiledGrammar, chart: &Chart, n_tokens: usize, start: Nt) -> Result<Parse, String> {
    let roots: Vec<Item> = chart.root_items(g, start).collect();
    let root = match roots.first() {
        None => return Err("no parse".to_string()),
        Some(&r) => r,
    };
    let mut ambiguous = roots.len() > 1;
    let tree = extract_item(g, chart, root.prod, 0, n_tokens, &mut ambiguous);
    Ok(Parse { tree, ambiguous })
}

/// Reconstruct the subtree for a finished item `(prod, ·, origin)` spanning `[origin, end)`.
fn extract_item(
    g: &CompiledGrammar,
    chart: &Chart,
    prod: u32,
    origin: usize,
    end: usize,
    ambiguous: &mut bool,
) -> PTree {
    let rhs = &g.prods[prod as usize].rhs;
    let mut pos = end;
    let mut kids_rev = Vec::new();
    for k in (0..rhs.len()).rev() {
        match rhs[k] {
            GSym::T(_) => pos -= 1, // a terminal consumed exactly one token
            GSym::N(nt) => {
                let bound = g.prods[prod as usize].bound[k].unwrap();
                let (s, q) = find_split(g, chart, prod, origin, k, nt, bound, pos, ambiguous);
                kids_rev.push(extract_item(g, chart, q, s, pos, ambiguous));
                pos = s;
            }
        }
    }
    debug_assert_eq!(pos, origin, "rhs spans did not tile [origin, end)");
    kids_rev.reverse();
    PTree { prod, start: origin, end, nt_children: kids_rev }
}

/// Find the split for the `k`-th rhs symbol (a nonterminal `nt`) of `prod` (started at `origin`) whose
/// finished sub-item ends at `end`: a finished item for `nt` in `sets[end]` with precedence `<= bound`
/// whose start `s` is reachable by the prefix `rhs[0..k]` (`(prod, dot=k, origin)` present at `s`).
/// Returns `(s, q_prod)`; sets `*ambiguous` if a second valid split exists.
#[allow(clippy::too_many_arguments)]
fn find_split(
    g: &CompiledGrammar,
    chart: &Chart,
    prod: u32,
    origin: usize,
    k: usize,
    nt: Nt,
    bound: u32,
    end: usize,
    ambiguous: &mut bool,
) -> (usize, u32) {
    let prefix = Item { prod, dot: k as u16, origin: origin as u32 };
    let mut found: Option<(usize, u32)> = None;
    for &it in &chart.sets[end] {
        let q = &g.prods[it.prod as usize];
        if q.lhs == nt && it.dot as usize == q.rhs.len() && q.prec <= bound {
            let s = it.origin as usize;
            if chart.contains(s, prefix) {
                if found.is_none() {
                    found = Some((s, it.prod));
                } else {
                    *ambiguous = true;
                    break;
                }
            }
        }
    }
    found.expect("recognizer accepted but no split found (parser invariant)")
}
