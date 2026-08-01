//! Compute default and user-supplied precedence/gather bounds for mixfix operators. The arithmetic is
//! observable through parser disambiguation.

use super::{ANY, INFIX_PREC, UNARY_PREC};
use crate::lex::Frag;
use crate::surface::ast::GatherElem;

/// The computed precedence and per-argument gather bounds of an operator with mixfix syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrecGather {
    pub prec: u32,
    /// One numeric bound per argument (per `_` in the syntax), left-to-right.
    pub gather: Vec<u32>,
}

/// Compute `(prec, gather)` for an operator whose name has mixfix syntax `frags` and arity `nr_args`.
///
/// - `user_prec`/`user_gather`: the `prec (n)` / `gather (…)` attributes, if the user gave them.
/// - `is_assoc`: whether the operator carries the `assoc` axiom (selects the right-associating default
///   gather `(e E)` for a bare binary infix).
///
/// Includes default bare-operator precedence and associative infix bias. Cross-profile bias is omitted
/// because this function receives one declaration profile.
pub fn compute(
    frags: &[Frag],
    nr_args: usize,
    user_prec: Option<u32>,
    user_gather: Option<&[GatherElem]>,
    is_assoc: bool,
) -> PrecGather {
    let n = frags.len();
    let left_bare = matches!(frags.first(), Some(Frag::Hole));
    let right_bare = matches!(frags.last(), Some(Frag::Hole));

    // Bare operators use unary/infix defaults; pure prefix mixfix uses zero.
    let prec = user_prec.unwrap_or({
        if left_bare || right_bare {
            if nr_args == 1 { UNARY_PREC } else { INFIX_PREC }
        } else {
            0
        }
    });

    let gather = if let Some(ug) = user_gather {
        // User gather: `&` → ANY; otherwise the element's offset (E=0, e=-1) plus prec, clamped at 0.
        debug_assert_eq!(ug.len(), nr_args, "gather length must equal arity");
        ug.iter()
            .map(|e| match e {
                GatherElem::Any => ANY,
                GatherElem::Strong => prec,                 // E: 0 + prec
                GatherElem::Weak => prec.saturating_sub(1), // e: -1 + prec, clamped at 0
            })
            .collect()
    } else if nr_args == 0 {
        Vec::new()
    } else if is_assoc && left_bare && right_bare && prec > 0 {
        // Right-associate a bare binary infix assoc operator: gather `(e E)` = [prec-1, prec].
        vec![prec - 1, prec]
    } else {
        // Default per-hole gather: a `_` at an end, or adjacent to another `_`, binds at `prec`
        // (so a sub-term there must be strictly tighter); a `_` flanked by name tokens is unbounded.
        let mut g = Vec::with_capacity(nr_args);
        for (i, f) in frags.iter().enumerate() {
            if !matches!(f, Frag::Hole) {
                continue;
            }
            let adjacent = i == 0
                || i + 1 == n
                || matches!(frags[i - 1], Frag::Hole)
                || matches!(frags[i + 1], Frag::Hole);
            g.push(if adjacent { prec } else { ANY });
        }
        g
    };

    PrecGather { prec, gather }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::{Frag, Interner};

    /// Build mixfix `frags` from a name with the shared interner used by [`split_mixfix`].
    fn frags(name: &str, i: &mut Interner) -> Vec<Frag> {
        crate::lex::split_mixfix(name, i)
    }

    #[test]
    fn bare_binary_infix_assoc_right_associates() {
        // `_+_ [assoc]`: prec 41, gather (e E) = [40, 41].
        let mut i = Interner::new();
        let pg = compute(&frags("_+_", &mut i), 2, None, None, true);
        assert_eq!(pg.prec, INFIX_PREC);
        assert_eq!(pg.gather, vec![40, 41]);
    }

    #[test]
    fn bare_binary_infix_nonassoc() {
        // `_<_` (free): prec 41, default per-hole gather [41, 41] (both holes at an end).
        let mut i = Interner::new();
        let pg = compute(&frags("_<_", &mut i), 2, None, None, false);
        assert_eq!(pg.prec, 41);
        assert_eq!(pg.gather, vec![41, 41]);
    }

    #[test]
    fn bare_unary_prefix() {
        // `s_`: prec 15, gather [15] (the hole is at the end).
        let mut i = Interner::new();
        let pg = compute(&frags("s_", &mut i), 1, None, None, false);
        assert_eq!(pg.prec, UNARY_PREC);
        assert_eq!(pg.gather, vec![15]);
    }

    #[test]
    fn outfix_holes_are_unbounded() {
        // `if_then_else_fi`: bare? no leading/trailing `_` → prec 0; every hole flanked by tokens → ANY.
        let mut i = Interner::new();
        let pg = compute(&frags("if_then_else_fi", &mut i), 3, None, None, false);
        assert_eq!(pg.prec, 0);
        assert_eq!(pg.gather, vec![ANY, ANY, ANY]);
    }

    #[test]
    fn user_gather_offsets_from_prec() {
        // gather (E e &) with prec 9 → [9, 8, 127].
        let mut i = Interner::new();
        let pg = compute(
            &frags("_;_;_", &mut i),
            3,
            Some(9),
            Some(&[GatherElem::Strong, GatherElem::Weak, GatherElem::Any]),
            false,
        );
        assert_eq!(pg.prec, 9);
        assert_eq!(pg.gather, vec![9, 8, ANY]);
    }

    #[test]
    fn user_weak_gather_clamps_at_zero() {
        // gather (e) with prec 0 → -1 clamped to 0.
        let mut i = Interner::new();
        let pg = compute(
            &frags("_!", &mut i),
            1,
            Some(0),
            Some(&[GatherElem::Weak]),
            false,
        );
        assert_eq!(pg.gather, vec![0]);
    }
}
