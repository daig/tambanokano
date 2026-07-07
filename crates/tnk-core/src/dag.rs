//! The runtime term representation: a GC'd DAG of [`DagNode`]s.
//!
//! Decision **D3**: the closed theory set is an `enum` ([`NodeTerm`]), not a C++-style virtual
//! hierarchy. Each node caches its least sort (computed at construction by the `engine`) and the
//! equation-set epoch at which it was last proved canonical. Phase 0 implements only the
//! **free-theory** arm.
//!
//! Invariant-bearing fields are `pub(crate)`: only the engine may set a node's sort or its reduced
//! epoch (review R3 H4 — public fields previously let callers mark an unreduced node "reduced" or
//! desync the cached sort).

use crate::id::Id;
use crate::sort::SortId;
use crate::symbol::SymbolId;

pub type DagId = Id<DagNode>;

#[derive(Debug)]
pub struct DagNode {
    /// Least sort of this node (Phase 0: the operator's range sort, or the kind's error sort if
    /// arguments are ill-sorted). Computed once at construction.
    pub(crate) sort: SortId,
    /// The `Engine` equation-set epoch at which this node was last proved canonical, or `0` if it
    /// has never been reduced. The engine treats the node as reduced only while this equals the
    /// current epoch, so adding equations invalidates stale results (review R2 H2).
    pub(crate) reduced_epoch: u32,
    /// This node's **normal form** when it is reduced (`reduced_epoch == eq_epoch`): `None` means the
    /// node *is* its own normal form, `Some(nf)` forwards to a structurally different result it rewrote
    /// to. This is the out-of-place counterpart of Maude's in-place rewrite (C7): our `reduce` abandons
    /// a rewritten redex rather than mutating it, so a *shared* redex would be re-reduced once per
    /// reference; the forward lets every reference deliver the already-computed result and skip the
    /// re-reduction (matching Maude's `rewrites:` count). Metadata only — set via `get_mut`, exactly
    /// like `sort`/`reduced_epoch` — so the node's *content* stays immutable and the render-after trace
    /// keeps reading the redex it was handed. Meaningful only while `reduced_epoch == eq_epoch`; a stale
    /// `Some` from an earlier epoch is never followed (the read is epoch-guarded) and is overwritten at
    /// the node's next normal-form point. Marked by [`Runtime::mark_reachable`](crate::engine::Runtime)
    /// as a pseudo-child, so it stays alive only while its forwarding node is alive (freed with it).
    pub(crate) nf: Option<DagId>,
    pub(crate) term: NodeTerm,
}

/// Two structurally-identical nodes (same theory rep, same child ids, same scalar payload) — what the
/// C7 construction-dedup memo keys on. Built bottom-up, so identical subtrees already share child ids,
/// keeping the key shallow (no deep structural hashing). `sort` is *not* part of the key: a node's base
/// sort is a function of its children's sorts, so two equal `NodeTerm`s necessarily share it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum NodeTerm {
    /// A free-theory application `symbol(args...)`; `args.len()` equals the symbol's arity.
    Free { symbol: SymbolId, args: Vec<DagId> },
    /// An **ACU** application (`assoc comm`, optionally `id:`): the operator's arguments as a
    /// **canonical** multiset of `(element, multiplicity)` pairs — equal elements merged, identity
    /// elements dropped, nested same-symbol applications flattened, and the pairs sorted by the
    /// engine's total node order ([`Runtime::dag_compare`](crate::engine::Runtime)). A canonical ACU
    /// node always holds ≥ 2 total arguments: a lone argument collapses to the element itself and the
    /// empty multiset to the identity (so `args` here is never a single `(e, 1)`). `u32` multiplicity
    /// matches Maude's `ArgVec<Pair>` (the red-black tree rep above `CONVERT_THRESHOLD` is a later
    /// perf step). Built only by `make_acu` (decision **D3**: a pure additive arm — GC, equality, and
    /// reduction traverse it through the [`children`](DagNode::children) visitor unchanged).
    Acu { symbol: SymbolId, args: Vec<(DagId, u32)> },
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
    S { symbol: SymbolId, count: crate::num::Nat, arg: DagId },
    /// An **NA** (atomic built-in constant): a leaf carrying a [`NaValue`] (a string / quoted-id /
    /// float), built by the built-in seam (string/qid/float literals + results). Like the S `count`,
    /// the `value` is scalar payload, not a child, so equality/order need theory-specific arms. Has no
    /// children; matches only itself (Maude's `NA_DagNode`). Built only by `make_na`.
    Na { symbol: SymbolId, value: NaValue },
    /// A **variable** leaf (Maude's `VariableDagNode`) — the symbolic engine's genuine logic
    /// variable; appears only in unification/variant/narrowing DAGs, never during ordinary
    /// reduction. `symbol` is the per-sort variable symbol ([`Engine::variable_symbol`]
    /// (crate::engine::Engine::variable_symbol), Maude's `Module::instantiateVariable`); the node's
    /// cached `sort` equals that symbol's range sort. `name` is the interned **base-name token
    /// code** (Maude's `NamedEntity::id()`): identity and canonical order among same-sort variables
    /// (`variableDagNode.cc compareArguments` is `id() - id()`), resolved back to text by the
    /// frontend for printing. `index` is the variable's slot in the owning problem's substitution
    /// (`VariableDagNode::index`) — bookkeeping, deliberately **not** part of equality or order.
    /// Built only by `make_var`.
    Var { symbol: SymbolId, name: u32, index: u32 },
}

/// The value of an atomic built-in constant ([`NodeTerm::Na`]). Strings/quoted-ids share an immutable
/// reference-counted backing (cheap to clone); the float arm lands with `FLOAT` (B3.7). A **string** is a
/// raw **byte** sequence (`Rc<[u8]>`), exactly Maude's `Rope` of `char`s — it is NOT required to be UTF-8
/// (`substr("héllo", 1, 1)` is the lone byte `0xC3`). The derived `Eq`/`Ord`/`Hash` on the byte slice is
/// byte-lexicographic, matching Maude's Rope comparison. A `Qid` stays `Rc<str>` (identifiers are text).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NaValue {
    /// A string literal / result (the `<Strings>` `StringSymbol`) — a raw byte sequence.
    Str(std::rc::Rc<[u8]>),
    /// A quoted identifier (the `<Qids>` `QuotedIdentifierSymbol`).
    Qid(std::rc::Rc<str>),
    /// An IEEE double, stored as its bit pattern (`f64::to_bits`) so `NaValue` keeps a total
    /// `Eq`/`Ord`/`Hash` (the float ops convert via `from_bits`). Bitwise equality agrees with Maude's
    /// value equality for all normal floats; it diverges only at the IEEE edge cases `+0.0`/`-0.0`
    /// (distinct bits, value-equal) and `NaN` (value-unequal, bit-equal) — both unreachable here, since
    /// float ops are free (never AC, so `dag_compare` is not exercised on floats) and `==` on floats is
    /// not used (the float relational ops compare values directly).
    Float(u64),
}

/// Compare two string byte sequences exactly as Maude's `Rope::compare` does — as sequences of **signed**
/// `char` (the C `int d = *p - *q`), so a high byte (0x80–0xFF, negative as a signed char) orders *before*
/// an ASCII byte. Both the `_<_`/`_>_`/`_<=_`/`_>=_` string ops and the DAG canonical order
/// ([`Runtime::dag_compare`](crate::engine::Runtime)) use this: unsigned byte-lexicographic would put high
/// bytes last, diverging from the reference (`"\303" < "b"` is true in Maude, false unsigned).
pub(crate) fn rope_cmp(a: &[u8], b: &[u8]) -> std::cmp::Ordering {
    a.iter().map(|&x| x as i8).cmp(b.iter().map(|&x| x as i8))
}

/// A static empty child slice — the children of a leaf ([`NodeTerm::Na`]) without allocating.
const NO_CHILDREN: &[DagId] = &[];

/// A public, read-only view of a node's representation, for a consumer (the frontend pretty-printer,
/// B4.6) that must render the **scalar payload** the generic [`symbol`](DagNode::symbol) /
/// [`children`](DagNode::children) visitor cannot reach — the S-theory iter `count` and the `Na` constant
/// value. [`App`](NodeRepr::App) covers *every* operator application (free / ACU / AU / CUI); the consumer
/// renders it from `symbol()` + `children()`. This keeps [`NodeTerm`]/[`NaValue`] crate-private while
/// exposing exactly what surface rendering needs.
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
    /// A variable ([`NodeTerm::Var`]): `name` is the interned base-name token code the frontend
    /// resolves to text; the sort for the printed `name:Sort` form is the node's [`sort`](DagNode::sort).
    Var { name: u32 },
}

impl DagNode {
    /// Visit each child once via a closure — the form a consumer uses when it wants to act on each
    /// child *without materializing a collection* (the C++ `markArguments` visitor). Rather than
    /// handing out a `&[DagId]`, it lets non-slice representations participate: ACU's
    /// `(child, multiplicity)` pairs, the S-theory's `(count, arg)`, a red-black `ACU_TreeDagNode`
    /// have no contiguous child array to borrow (review R3 H3). (The GC marker currently uses
    /// [`children`](Self::children)`().extend(..)` instead, whose slice fast-path is faster for the
    /// free rep; both are equivalent traversals through this seam.)
    pub fn for_each_child(&self, mut f: impl FnMut(DagId)) {
        match &self.term {
            // Free, AU, and CUI are all an ordered `Vec<DagId>` (a contiguous child slice).
            NodeTerm::Free { args, .. } | NodeTerm::Au { args, .. } | NodeTerm::Cui { args, .. } => {
                args.iter().for_each(|&c| f(c))
            }
            // The ACU multiset: each distinct element is visited `multiplicity` times, in canonical
            // order — the same sequence [`children`](Self::children) yields (the equality/GC contract
            // of review R3 H3 / `07` §1.3).
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

    /// Iterate this node's children. Returns an iterator (not a slice) so the non-slice reps fit:
    /// equality and reduction enumerate children theory-agnostically, so a new arm is a pure addition
    /// to this method rather than an edit to GC / equality / reduction (review R3 H3). The ACU arm
    /// yields the **flattened multiset with repeats, in canonical order** — so two canonical ACU nodes
    /// are equal iff their `children()` sequences are pairwise equal, exactly the contract
    /// [`crate::engine::Runtime::deep_equal`] relies on.
    pub fn children(&self) -> ChildIter<'_> {
        match &self.term {
            NodeTerm::Free { args, .. }
            | NodeTerm::Au { args, .. }
            | NodeTerm::Cui { args, .. } => ChildIter::Free(args.iter()),
            NodeTerm::Acu { args, .. } => ChildIter::Acu { pairs: args.iter(), current: None },
            // The S successor's single child reuses the slice iterator via `from_ref` — no new arm.
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

    /// A read-only view exposing the scalar payload (`iter` count / `Na` value) the generic child visitor
    /// cannot — for the frontend pretty-printer (B4.6). Operator applications are [`NodeRepr::App`]
    /// (rendered from `symbol()` + `children()`); only S/NA carry extra payload.
    pub fn repr(&self) -> NodeRepr<'_> {
        match &self.term {
            NodeTerm::Free { .. }
            | NodeTerm::Acu { .. }
            | NodeTerm::Au { .. }
            | NodeTerm::Cui { .. } => NodeRepr::App,
            NodeTerm::S { count, arg, .. } => NodeRepr::Iter { count: count.to_decimal(), arg: *arg },
            NodeTerm::Na { value, .. } => match value {
                NaValue::Str(s) => NodeRepr::Str(s),
                NaValue::Qid(q) => NodeRepr::Qid(q),
                NaValue::Float(bits) => NodeRepr::Float(f64::from_bits(*bits)),
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
    Acu { pairs: std::slice::Iter<'a, (DagId, u32)>, current: Option<(DagId, u32)> },
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

    /// The two traversal forms of the A5 seam agree, and a constant has no children.
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
        assert_eq!(via_iter, via_visitor, "children() and for_each_child enumerate the same set");

        assert_eq!(e.node(x).children().count(), 0, "a constant has no children");
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
        assert!(matches!(e.node(z).repr(), NodeRepr::App), "a constant is an App");
    }
}
