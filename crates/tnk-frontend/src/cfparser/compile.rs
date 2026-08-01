//! Compile a [`Grammar`] into the parser's working form: productions indexed by their lhs nonterminal
//! (for prediction) with the gather bounds re-aligned to rhs positions (for the completer's prec gate).

use crate::grammar::{Action, GSym, Grammar, Nt};
use std::collections::HashMap;

/// A compiled production: like [`crate::grammar::Production`] but with the per-nonterminal gather bounds
/// spread to a per-rhs-position vector (`None` at terminals), so the Earley completer can read the bound
/// for a hole directly from its dot position.
#[derive(Debug, Clone)]
pub struct CProd {
    pub lhs: Nt,
    pub rhs: Vec<GSym>,
    /// Production precedence.
    pub prec: u32,
    /// Per-rhs-position gather bound: `Some(b)` at a nonterminal hole, `None` at a terminal.
    pub bound: Vec<Option<u32>>,
    pub action: Action,
}

/// A grammar in working form: productions plus an index `lhs nonterminal → production numbers` used by
/// the Earley predictor.
///
/// `Clone` supports per-import statement reparsing: a home module's compiled grammar is cloned and its
/// production *actions* re-pointed at a flattened module's symbol table
/// ([`crate::load::remap_home_grammar`]), so an imported statement re-parses in its home grammar while
/// building over the flattened module's symbols.
#[derive(Debug, Clone)]
pub struct CompiledGrammar {
    pub prods: Vec<CProd>,
    by_lhs: HashMap<Nt, Vec<u32>>,
}

impl CompiledGrammar {
    pub fn compile(g: &Grammar) -> Self {
        let mut prods = Vec::with_capacity(g.productions.len());
        let mut by_lhs: HashMap<Nt, Vec<u32>> = HashMap::new();
        for (idx, p) in g.productions.iter().enumerate() {
            // Spread the per-nonterminal gather vector across rhs positions.
            let mut bound = Vec::with_capacity(p.rhs.len());
            let mut gi = 0;
            for s in &p.rhs {
                if s.is_nonterminal() {
                    bound.push(Some(p.gather[gi]));
                    gi += 1;
                } else {
                    bound.push(None);
                }
            }
            debug_assert_eq!(gi, p.gather.len(), "gather length mismatch in {p:?}");
            by_lhs.entry(p.lhs).or_default().push(idx as u32);
            prods.push(CProd {
                lhs: p.lhs,
                rhs: p.rhs.clone(),
                prec: p.prec,
                bound,
                action: p.action,
            });
        }
        CompiledGrammar { prods, by_lhs }
    }

    /// The production numbers whose lhs is `nt` (empty if none) — the predictor's expansion of `nt`.
    pub fn productions_for(&self, nt: Nt) -> &[u32] {
        self.by_lhs.get(&nt).map_or(&[], Vec::as_slice)
    }
}
