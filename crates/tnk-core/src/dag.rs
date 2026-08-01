//! The runtime term representation: a GC'd DAG of [`DagNode`]s.
//!
//! The `NodeTerm` enum distinguishes the supported theory representations. Each node
//! caches its least sort, the equation-set epoch at which it was proved canonical, and an optional
//! normal-form forward. All supported theory representations live behind the same node interface.
//!
//! Invariant-bearing fields are `pub(crate)`: only the engine may set a node's sort or reduced epoch,
//! preventing callers from marking an unreduced node as reduced or desynchronizing the cached sort.

use crate::id::Id;
use crate::smt::SmtNumber;
use crate::sort::SortId;
use crate::symbol::SymbolId;

pub type DagId = Id<DagNode>;

#[derive(Debug)]
pub struct DagNode {
    /// Cached least sort. Construction computes the structural base sort; membership axioms may lower
    /// it lazily when reduction reaches the node's normal-form point.
    pub(crate) sort: SortId,
    /// The `Engine` equation-set epoch at which this node was last proved canonical, or `0` if it
    /// has never been reduced. The engine treats the node as reduced only while this equals the
    /// current epoch, so adding equations invalidates stale results.
    pub(crate) reduced_epoch: u32,
    /// This node's normal form while `reduced_epoch` matches the equation epoch. `None` means the node is
    /// canonical; `Some(nf)` forwards shared references to an out-of-place rewrite result. The target is
    /// traced as a pseudo-child for GC and ignored once its epoch becomes stale.
    pub(crate) nf: Option<DagId>,
    pub(crate) term: NodeTerm,
}

/// Key for construction-time structural deduplication. Children are already canonicalized bottom-up;
/// sort is excluded because it is determined by the term and child sorts.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum NodeTerm {
    /// A free-theory application `symbol(args...)`; `args.len()` equals the symbol's arity.
    Free { symbol: SymbolId, args: Vec<DagId> },
    /// An **ACU** application (`assoc comm`, optionally `id:`): a canonical multiset of
    /// `(element, multiplicity)` pairs. Equal elements are merged, identities dropped, nested
    /// applications flattened, and pairs sorted by the engine's total node order. A canonical node
    /// contains at least two total arguments; singleton and empty multisets collapse. Multiplicities
    /// use `u32`.
    Acu {
        symbol: SymbolId,
        args: Vec<(DagId, u32)>,
    },
    /// An **AU** application (`assoc`, optionally `id:`; **not** commutative): the operator's
    /// arguments as a canonical **ordered sequence** — nested same-symbol applications flattened and
    /// identity elements dropped, but **not** sorted or multiplicity-merged (order is significant). A
    /// canonical AU node always holds ≥ 2 arguments (a lone argument collapses to the element itself,
    /// the empty sequence to the identity). Built only by `make_au`. Traversal is the same slice-based
    /// form as [`Free`](NodeTerm::Free).
    Au { symbol: SymbolId, args: Vec<DagId> },
    /// A **CUI** application (`comm`, optionally `id:`/`idem`; **not** associative): a binary node
    /// whose two arguments are in canonical (sorted) order. `f(a, a)` (idem) and `f(a, e)` (identity)
    /// collapse to a single element at construction, so a canonical CUI node always has exactly two
    /// arguments. Built only by `make_cui`; traversal is the slice-based form.
    Cui { symbol: SymbolId, args: Vec<DagId> },
    /// An **S** (`iter`) application `s^count(arg)` — a unary stacked successor with a **bignum**
    /// `count` (so `s^(10^9) 0` is O(1)). The single child is `arg`; `count` is **scalar payload, not a
    /// child id**, so it is invisible to the generic [`children`](DagNode::children) traversal — which
    /// is exactly why `deep_equal`/`dag_compare` need theory-specific arms that also compare `count`
    /// (without them `s^2(0)` and `s^3(0)` would compare equal). Built only by `make_s`, which keeps
    /// `count >= 1` (`s^0(x)` collapses to `x`) and flattens nested same-symbol successors.
    S {
        symbol: SymbolId,
        count: crate::num::Nat,
        arg: DagId,
    },
    /// An **NA** (atomic built-in constant): a leaf carrying a [`NaValue`] (a string / quoted-id /
    /// float), built by the built-in seam (string/qid/float literals + results). Like the S `count`,
    /// the `value` is scalar payload rather than a child, so equality and ordering use
    /// representation-specific arms. Has no children and matches only itself. Built only by `make_na`.
    Na { symbol: SymbolId, value: NaValue },
    /// A **variable** leaf used only by unification, variant, and narrowing DAGs. `symbol` is the
    /// per-sort variable symbol created by [`Engine::variable_symbol`](crate::engine::Engine::variable_symbol);
    /// the cached node sort equals that symbol's range sort. `name` is the interned base-name token
    /// code and determines identity and canonical order among same-sort variables; the frontend
    /// resolves it back to text. `index` is the variable's substitution slot and deliberately does
    /// not participate in equality or ordering. Built only by `make_var`.
    Var {
        symbol: SymbolId,
        name: u32,
        index: u32,
    },
}

/// The value of an atomic built-in constant (`NodeTerm::Na`). Strings and quoted identifiers share
/// immutable reference-counted backing. Floats are stored by IEEE-754 bit pattern. A string is a raw
/// byte sequence (`Rc<[u8]>`) and need not be valid UTF-8; comparison and hashing are byte-based.
/// A quoted identifier remains text (`Rc<str>`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NaValue {
    /// A `<Strings>` literal or result stored as a raw byte sequence.
    Str(std::rc::Rc<[u8]>),
    /// A `<Qids>` quoted identifier stored without its leading quote.
    Qid(std::rc::Rc<str>),
    /// An IEEE double stored as `f64::to_bits`, giving `NaValue` total `Eq`/`Ord`/`Hash`. Bitwise and
    /// value equality differ only for signed zero and NaN; built-in equality handles floats by value,
    /// while float operators reject NaN.
    Float(u64),
    /// An exact SMT integer/rational literal.
    SmtNum(std::rc::Rc<SmtNumber>),
}

/// Compare two strings as sequences of signed bytes, placing 0x80–0xFF before ASCII. String relational
/// operators and [`Runtime::dag_compare`](crate::engine::Runtime) share this order.
pub(crate) fn rope_cmp(a: &[u8], b: &[u8]) -> std::cmp::Ordering {
    a.iter().map(|&x| x as i8).cmp(b.iter().map(|&x| x as i8))
}

/// A static empty child slice — the children of a leaf ([`NodeTerm::Na`]) without allocating.
const NO_CHILDREN: &[DagId] = &[];

/// Public read-only node representation exposing scalar payloads that child traversal cannot: iteration
/// counts, strings, quoted identifiers, floats, SMT numbers, and variables.
#[derive(Debug)]
pub enum NodeRepr<'a> {
    /// A free / ACU / AU / CUI operator application — render via `symbol()` + `children()`.
    App,
    /// An `iter` successor `s^count(arg)`; `count` is the base-10 rendering (it may be a bignum).
    Iter { count: String, arg: DagId },
    /// A string constant's value (the raw bytes, without surrounding quotes).
    Str(&'a [u8]),
    /// A quoted-identifier constant's name (without the leading quote).
    Qid(&'a str),
    /// A float constant's value.
    Float(f64),
    /// An exact SMT integer/rational constant.
    SmtNum(&'a SmtNumber),
    /// A variable (`NodeTerm::Var`): `name` is the interned base-name token code the frontend
    /// resolves to text; the sort for the printed `name:Sort` form is the node's [`sort`](DagNode::sort).
    Var { name: u32 },
}

impl DagNode {
    /// Visit each child once without materializing a collection. A callback accommodates non-slice
    /// representations such as ACU `(child, multiplicity)` pairs and compact iteration
    /// `(count, argument)` nodes. The GC marker currently uses [`children`](Self::children) and its
    /// free-node slice fast path; both APIs traverse the same logical children.
    pub fn for_each_child(&self, mut f: impl FnMut(DagId)) {
        match &self.term {
            // Free, AU, and CUI are all an ordered `Vec<DagId>` (a contiguous child slice).
            NodeTerm::Free { args, .. }
            | NodeTerm::Au { args, .. }
            | NodeTerm::Cui { args, .. } => args.iter().for_each(|&c| f(c)),
            // The ACU multiset: each distinct element is visited `multiplicity` times, in canonical
            // order — the same sequence [`children`](Self::children) yields (the equality/GC contract).
            NodeTerm::Acu { args, .. } => {
                for &(id, mult) in args {
                    for _ in 0..mult {
                        f(id);
                    }
                }
            }
            // The S successor has exactly one child (`arg`); `count` is scalar, not a child.
            NodeTerm::S { arg, .. } => f(*arg),
            // An atomic NA constant or a variable is a leaf — no children.
            NodeTerm::Na { .. } | NodeTerm::Var { .. } => {}
        }
    }

    /// Iterate this node's logical children without requiring every representation to expose a
    /// slice. Equality, reduction, and GC can therefore traverse nodes theory-agnostically. The ACU
    /// arm yields the flattened multiset with repeats in canonical order, so canonical ACU nodes are
    /// equal exactly when their child streams are pairwise equal.
    pub fn children(&self) -> ChildIter<'_> {
        match &self.term {
            NodeTerm::Free { args, .. }
            | NodeTerm::Au { args, .. }
            | NodeTerm::Cui { args, .. } => ChildIter::Free(args.iter()),
            NodeTerm::Acu { args, .. } => ChildIter::Acu {
                pairs: args.iter(),
                current: None,
            },
            // Reuse the slice iterator for the S successor's single child.
            NodeTerm::S { arg, .. } => ChildIter::Free(std::slice::from_ref(arg).iter()),
            // An atomic NA constant or a variable is a leaf — an empty child iterator.
            NodeTerm::Na { .. } | NodeTerm::Var { .. } => ChildIter::Free(NO_CHILDREN.iter()),
        }
    }

    pub fn symbol(&self) -> SymbolId {
        match &self.term {
            NodeTerm::Free { symbol, .. }
            | NodeTerm::Acu { symbol, .. }
            | NodeTerm::Au { symbol, .. }
            | NodeTerm::Cui { symbol, .. }
            | NodeTerm::S { symbol, .. }
            | NodeTerm::Na { symbol, .. }
            | NodeTerm::Var { symbol, .. } => *symbol,
        }
    }

    /// The node's cached least sort.
    pub fn sort(&self) -> SortId {
        self.sort
    }

    /// The owning substitution slot for a symbolic variable leaf.
    pub fn variable_index(&self) -> Option<u32> {
        match &self.term {
            NodeTerm::Var { index, .. } => Some(*index),
            _ => None,
        }
    }

    /// Expose scalar payloads not represented by the generic child iterator.
    pub fn repr(&self) -> NodeRepr<'_> {
        match &self.term {
            NodeTerm::Free { .. }
            | NodeTerm::Acu { .. }
            | NodeTerm::Au { .. }
            | NodeTerm::Cui { .. } => NodeRepr::App,
            NodeTerm::S { count, arg, .. } => NodeRepr::Iter {
                count: count.to_decimal(),
                arg: *arg,
            },
            NodeTerm::Na { value, .. } => match value {
                NaValue::Str(s) => NodeRepr::Str(s),
                NaValue::Qid(q) => NodeRepr::Qid(q),
                NaValue::Float(bits) => NodeRepr::Float(f64::from_bits(*bits)),
                NaValue::SmtNum(number) => NodeRepr::SmtNum(number),
            },
            NodeTerm::Var { name, .. } => NodeRepr::Var { name: *name },
        }
    }
}

/// The iterator returned by [`DagNode::children`]: one arm per `NodeTerm` rep, unified into a single
/// type so callers (GC, `deep_equal`, `reduce`) stay theory-agnostic. The free arm is the borrowed
/// slice; the ACU arm expands `(element, multiplicity)` pairs into the element repeated `multiplicity`
/// times (so the yielded sequence is the full canonical multiset, repeats included).
pub enum ChildIter<'a> {
    Free(std::slice::Iter<'a, DagId>),
    Acu {
        pairs: std::slice::Iter<'a, (DagId, u32)>,
        current: Option<(DagId, u32)>,
    },
}

impl Iterator for ChildIter<'_> {
    type Item = DagId;

    fn next(&mut self) -> Option<DagId> {
        match self {
            ChildIter::Free(it) => it.next().copied(),
            ChildIter::Acu { pairs, current } => loop {
                // Emit one of the current element while its remaining count is positive…
                if let Some((id, remaining)) = current
                    && *remaining > 0
                {
                    *remaining -= 1;
                    return Some(*id);
                }
                // …otherwise advance to the next pair (or finish).
                *current = Some(*pairs.next()?);
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::engine::Engine;

    /// The iterator and visitor traversal forms agree, and a constant has no children.
    #[test]
    fn children_iterator_and_visitor_agree() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let x = e.make_const(a);
        let y = e.make_const(a);
        let parent = e.make_free(f, vec![x, y]); // f(x, y), distinct child ids

        let node = e.node(parent);
        let via_iter: Vec<_> = node.children().collect();
        let mut via_visitor = Vec::new();
        node.for_each_child(|c| via_visitor.push(c));
        assert_eq!(via_iter, vec![x, y], "children() yields the args in order");
        assert_eq!(
            via_iter, via_visitor,
            "children() and for_each_child enumerate the same set"
        );

        assert_eq!(
            e.node(x).children().count(),
            0,
            "a constant has no children"
        );
    }

    /// `repr` exposes the S-theory iter `count` (a value the generic child visitor cannot reach) as a
    /// decimal, and reports operator applications as `App`.
    #[test]
    fn repr_exposes_iter_count_and_app() {
        use super::NodeRepr;
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let nznat = e.add_sort("NzNat");
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let z = e.make_const(zero);
        let five = e.make_iter(s, 5, z); // s^5(0)

        match e.node(five).repr() {
            NodeRepr::Iter { count, arg } => {
                assert_eq!(count, "5", "the iter count renders in decimal");
                assert_eq!(arg, z, "the successor's base is the 0 constant");
            }
            other => panic!("expected Iter, got {other:?}"),
        }
        assert!(
            matches!(e.node(z).repr(), NodeRepr::App),
            "a constant is an App"
        );
    }
}
