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
use super::{EffortExceeded, ParseEffort};
use crate::grammar::{GSym, Nt};

/// A concrete parse tree: the production applied, the token span `[start, end)`, and the subtrees for the
/// rhs **nonterminals** (left-to-right). Terminals are not stored as children — `build_term` reads any
/// literal/variable token it needs from `start` (each such production has a single leading terminal).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PTree {
    pub prod: u32,
    pub start: usize,
    pub end: usize,
    pub nt_children: Vec<PTree>,
}

/// The outcome of extraction: the first parse tree, whether the input was ambiguous, and (when
/// ambiguous) the second concrete parse in extraction order. Ordinary command parsing consumes only
/// `tree`; META-LEVEL's `metaParse` reifies both trees in an `ambiguity` result.
#[derive(Debug)]
pub struct Parse {
    pub tree: PTree,
    pub ambiguous: bool,
    pub alternative: Option<PTree>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExtractError {
    NoParse,
    Effort(EffortExceeded),
}

impl std::fmt::Display for ExtractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoParse => f.write_str("no parse"),
            Self::Effort(exceeded) => {
                write!(f, "parse effort limit exceeded at token {}", exceeded.at)
            }
        }
    }
}

impl From<EffortExceeded> for ExtractError {
    fn from(value: EffortExceeded) -> Self {
        Self::Effort(value)
    }
}

/// Extract the first parse for `start` from the chart, or an error describing why there is none.
pub fn extract(
    g: &CompiledGrammar,
    chart: &Chart,
    n_tokens: usize,
    start: Nt,
    effort: &mut ParseEffort,
) -> Result<Parse, ExtractError> {
    effort.charge_many(chart.sets[n_tokens].len(), n_tokens)?;
    let roots: Vec<Item> = chart.root_items(g, start).collect();
    let root = match roots.first() {
        None => return Err(ExtractError::NoParse),
        Some(&r) => r,
    };
    let mut ambiguous = roots.len() > 1;
    let tree = extract_item(g, chart, root.prod, 0, n_tokens, &mut ambiguous, effort)?;
    let alternative = if ambiguous {
        second_parse(g, chart, &roots, n_tokens, &tree, effort)?
    } else {
        None
    };
    Ok(Parse {
        tree,
        ambiguous,
        alternative,
    })
}

/// Reconstruct the subtree for a finished item `(prod, ·, origin)` spanning `[origin, end)`.
fn extract_item(
    g: &CompiledGrammar,
    chart: &Chart,
    prod: u32,
    origin: usize,
    end: usize,
    ambiguous: &mut bool,
    effort: &mut ParseEffort,
) -> Result<PTree, EffortExceeded> {
    effort.charge(end)?;
    let rhs = &g.prods[prod as usize].rhs;
    let mut pos = end;
    let mut kids_rev = Vec::new();
    for k in (0..rhs.len()).rev() {
        effort.charge(pos)?;
        match rhs[k] {
            GSym::T(_) => pos -= 1,
            GSym::N(nt) => {
                let bound = g.prods[prod as usize].bound[k].unwrap();
                let (s, q) =
                    find_split(g, chart, prod, origin, k, nt, bound, pos, ambiguous, effort)?;
                kids_rev.push(extract_item(g, chart, q, s, pos, ambiguous, effort)?);
                pos = s;
            }
        }
    }
    debug_assert_eq!(pos, origin, "rhs spans did not tile [origin, end)");
    kids_rev.reverse();
    Ok(PTree {
        prod,
        start: origin,
        end,
        nt_children: kids_rev,
    })
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
    effort: &mut ParseEffort,
) -> Result<(usize, u32), EffortExceeded> {
    let prefix = Item {
        prod,
        dot: k as u16,
        origin: origin as u32,
    };
    let mut found: Option<(usize, u32)> = None;
    for &it in &chart.sets[end] {
        effort.charge(end)?;
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
    Ok(found.expect("recognizer accepted but no split found (parser invariant)"))
}

/// Enumerate just enough of the packed forest to recover the second concrete parse. The walk follows
/// the same right-to-left split order as [`extract_item`], caps every branch at two trees, and rejects
/// cyclic unit-production paths. The ordinary parser never pays this cost unless ambiguity was already
/// detected by the first extraction.
fn second_parse(
    g: &CompiledGrammar,
    chart: &Chart,
    roots: &[Item],
    n_tokens: usize,
    first: &PTree,
    effort: &mut ParseEffort,
) -> Result<Option<PTree>, EffortExceeded> {
    let mut visiting = Vec::new();
    for root in roots {
        for tree in enumerate_item(g, chart, root.prod, 0, n_tokens, &mut visiting, effort)? {
            effort.charge(n_tokens)?;
            if &tree != first {
                return Ok(Some(tree));
            }
        }
    }
    Ok(None)
}

fn enumerate_item(
    g: &CompiledGrammar,
    chart: &Chart,
    prod: u32,
    origin: usize,
    end: usize,
    visiting: &mut Vec<(u32, usize, usize)>,
    effort: &mut ParseEffort,
) -> Result<Vec<PTree>, EffortExceeded> {
    effort.charge(end)?;
    effort.charge_many(visiting.len(), end)?;
    let key = (prod, origin, end);
    if visiting.contains(&key) {
        return Ok(Vec::new());
    }
    visiting.push(key);
    let children = enumerate_prefix(
        g,
        chart,
        prod,
        origin,
        g.prods[prod as usize].rhs.len(),
        end,
        visiting,
        effort,
    )?;
    visiting.pop();
    Ok(children
        .into_iter()
        .map(|nt_children| PTree {
            prod,
            start: origin,
            end,
            nt_children,
        })
        .take(2)
        .collect())
}

#[allow(clippy::too_many_arguments)]
fn enumerate_prefix(
    g: &CompiledGrammar,
    chart: &Chart,
    prod: u32,
    origin: usize,
    upto: usize,
    end: usize,
    visiting: &mut Vec<(u32, usize, usize)>,
    effort: &mut ParseEffort,
) -> Result<Vec<Vec<PTree>>, EffortExceeded> {
    effort.charge(end)?;
    if upto == 0 {
        return Ok((end == origin).then(Vec::new).into_iter().collect());
    }
    let k = upto - 1;
    match g.prods[prod as usize].rhs[k] {
        GSym::T(_) => {
            if end == 0 {
                Ok(Vec::new())
            } else {
                enumerate_prefix(g, chart, prod, origin, k, end - 1, visiting, effort)
            }
        }
        GSym::N(nt) => {
            let bound = g.prods[prod as usize].bound[k].unwrap();
            let prefix = Item {
                prod,
                dot: k as u16,
                origin: origin as u32,
            };
            let mut results = Vec::new();
            for &item in &chart.sets[end] {
                effort.charge(end)?;
                let child_prod = &g.prods[item.prod as usize];
                if child_prod.lhs != nt
                    || item.dot as usize != child_prod.rhs.len()
                    || child_prod.prec > bound
                {
                    continue;
                }
                let split = item.origin as usize;
                if !chart.contains(split, prefix) {
                    continue;
                }
                let child_trees =
                    enumerate_item(g, chart, item.prod, split, end, visiting, effort)?;
                for child in child_trees {
                    for mut siblings in
                        enumerate_prefix(g, chart, prod, origin, k, split, visiting, effort)?
                    {
                        effort.charge(end)?;
                        siblings.push(child.clone());
                        if !results.contains(&siblings) {
                            results.push(siblings);
                            if results.len() == 2 {
                                return Ok(results);
                            }
                        }
                    }
                }
            }
            Ok(results)
        }
    }
}
