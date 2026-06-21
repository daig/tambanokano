//! Order-sorted type system: the sort poset, **kinds** (connected components, each with a
//! synthesized error/top sort), and the subsort partial order [`Sorts::leq`].
//!
//! Ports the A3 design, minimized for Phase 0: build the poset, compute connected components and
//! the reflexive-transitive subsort closure. The full per-symbol sort *decision diagram* (which
//! gives least sorts under ad-hoc overloading and preregularity) lands with the complete theory
//! set in Phase 1; Phase 0 symbols carry a single declaration, so a node's sort is its operator's
//! range sort (see `engine`).

use crate::id::Id;
use std::collections::{BTreeMap, BTreeSet};

pub type SortId = Id<Sort>;
pub type KindId = Id<Kind>;

#[derive(Debug, Clone)]
pub struct Sort {
    pub name: String,
    /// `true` for the synthesized error/top sort of a kind (Maude's `[Kind]`).
    pub is_error: bool,
}

#[derive(Debug, Clone)]
pub struct Kind {
    /// User member sorts of this connected component (excludes the error sort).
    pub members: Vec<SortId>,
    /// The synthesized error/top sort: a supersort of every member.
    pub error: SortId,
}

/// The sort signature: declare sorts and subsort edges, then [`Sorts::close`] computes kinds and
/// the subsort closure. Immutable thereafter.
#[derive(Default)]
pub struct Sorts {
    sorts: Vec<Sort>,
    kinds: Vec<Kind>,
    /// Declared immediate supersorts: `up[sub]` lists each `sup` with `sub < sup`.
    up: Vec<Vec<SortId>>,
    /// Computed: `geq[s]` = every `x` with `s <= x` (includes `s` and `s`'s kind error sort).
    geq: Vec<BTreeSet<SortId>>,
    /// Computed: `leqs[r]` = every `y` with `y <= r` — the **down-set** of `r` (Maude's
    /// `Sort::getLeqSorts`). The inverse of `geq`; the key B2's least-sort resolution intersects.
    leqs: Vec<BTreeSet<SortId>>,
    kind_of: Vec<KindId>,
    closed: bool,
}

impl Sorts {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_sort(&mut self, name: impl Into<String>) -> SortId {
        assert!(!self.closed, "cannot add sorts after close()");
        let id = Id::from_raw(self.sorts.len() as u32);
        self.sorts.push(Sort { name: name.into(), is_error: false });
        self.up.push(Vec::new());
        id
    }

    /// Declare `sub < sup` (an immediate subsort relation).
    pub fn add_subsort(&mut self, sub: SortId, sup: SortId) {
        assert!(!self.closed, "cannot add subsorts after close()");
        self.up[sub.index()].push(sup);
    }

    pub fn sort(&self, s: SortId) -> &Sort {
        &self.sorts[s.index()]
    }
    pub fn name(&self, s: SortId) -> &str {
        &self.sorts[s.index()].name
    }
    pub fn kind_of(&self, s: SortId) -> KindId {
        debug_assert!(self.closed);
        self.kind_of[s.index()]
    }
    pub fn kind(&self, k: KindId) -> &Kind {
        &self.kinds[k.index()]
    }
    pub fn error_sort(&self, k: KindId) -> SortId {
        self.kinds[k.index()].error
    }
    pub fn num_sorts(&self) -> usize {
        self.sorts.len()
    }
    pub fn num_kinds(&self) -> usize {
        self.kinds.len()
    }

    /// `a <= b` in the subsort order. Requires [`close`](Self::close).
    pub fn leq(&self, a: SortId, b: SortId) -> bool {
        debug_assert!(self.closed, "leq before close()");
        self.geq[a.index()].contains(&b)
    }

    /// The **down-set** of `s`: every sort `y` with `y <= s` (Maude's `Sort::getLeqSorts`). B2's
    /// least-sort resolution intersects these to find the GLB-with-earliest-declaration-tie-break.
    /// Requires [`close`](Self::close).
    pub(crate) fn down_set(&self, s: SortId) -> &BTreeSet<SortId> {
        debug_assert!(self.closed, "down_set before close()");
        &self.leqs[s.index()]
    }

    /// `true` if `a` and `b` are in the same kind (connected component).
    pub fn same_kind(&self, a: SortId, b: SortId) -> bool {
        self.kind_of(a) == self.kind_of(b)
    }

    /// Compute kinds (connected components + error sorts) and the subsort closure.
    pub fn close(&mut self) {
        assert!(!self.closed, "already closed");
        let n0 = self.sorts.len();

        // 1. Connected components over the *undirected* subsort graph (union-find with halving).
        fn find(p: &mut [usize], mut x: usize) -> usize {
            while p[x] != x {
                p[x] = p[p[x]];
                x = p[x];
            }
            x
        }
        let mut parent: Vec<usize> = (0..n0).collect();
        for sub in 0..n0 {
            for sup in self.up[sub].clone() {
                let a = find(&mut parent, sub);
                let b = find(&mut parent, sup.index());
                if a != b {
                    parent[a] = b;
                }
            }
        }

        // 2. Group members by component root (BTreeMap → deterministic order).
        let mut groups: BTreeMap<usize, Vec<SortId>> = BTreeMap::new();
        for s in 0..n0 {
            let r = find(&mut parent, s);
            groups.entry(r).or_default().push(Id::from_raw(s as u32));
        }

        // 3. One error sort + kind per component.
        let mut kind_of: Vec<KindId> = vec![Id::from_raw(0); n0];
        for members in groups.into_values() {
            let kid: KindId = Id::from_raw(self.kinds.len() as u32);
            let repr = self.sorts[members[0].index()].name.clone();
            let err: SortId = Id::from_raw(self.sorts.len() as u32);
            self.sorts.push(Sort { name: format!("[{repr}]"), is_error: true });
            self.up.push(Vec::new());
            for &m in &members {
                kind_of[m.index()] = kid;
            }
            self.kinds.push(Kind { members, error: err });
        }

        // 4. Subsort closure: BFS upward for each user sort, then add its kind's error sort.
        let n = self.sorts.len();
        let mut geq: Vec<BTreeSet<SortId>> = vec![BTreeSet::new(); n];
        for s in 0..n0 {
            let mut seen: BTreeSet<SortId> = BTreeSet::new();
            let mut stack = vec![Id::<Sort>::from_raw(s as u32)];
            while let Some(x) = stack.pop() {
                if seen.insert(x) {
                    stack.extend_from_slice(&self.up[x.index()]);
                }
            }
            seen.insert(self.kinds[kind_of[s].index()].error);
            geq[s] = seen;
        }

        // 4b. Reject subsort cycles: two distinct user sorts that are mutually `<=` (Maude errors
        // on these; review R2 L6 / R3 M3).
        for s in 0..n0 {
            let sid = Id::<Sort>::from_raw(s as u32);
            for &t in &geq[s] {
                if t != sid && t.index() < n0 && geq[t.index()].contains(&sid) {
                    panic!(
                        "subsort cycle: `{}` and `{}` are mutually <=",
                        self.sorts[s].name,
                        self.sorts[t.index()].name
                    );
                }
            }
        }

        // 5. Finalize kind_of including error sorts; error sorts are <= only themselves.
        let mut kind_of_full: Vec<KindId> = vec![Id::from_raw(0); n];
        kind_of_full[..n0].copy_from_slice(&kind_of);
        for (ki, k) in self.kinds.iter().enumerate() {
            kind_of_full[k.error.index()] = Id::from_raw(ki as u32);
            geq[k.error.index()].insert(k.error);
        }

        // 6. Invert `geq` into down-sets: `leqs[r] = { y : y <= r }` (since `y <= r` iff `r ∈ geq[y]`).
        let mut leqs: Vec<BTreeSet<SortId>> = vec![BTreeSet::new(); n];
        for (y, up) in geq.iter().enumerate() {
            let yid = Id::<Sort>::from_raw(y as u32);
            for &r in up {
                leqs[r.index()].insert(yid);
            }
        }

        self.geq = geq;
        self.leqs = leqs;
        self.kind_of = kind_of_full;
        self.closed = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subsort_order_and_kinds() {
        let mut s = Sorts::new();
        let zero = s.add_sort("Zero");
        let nznat = s.add_sort("NzNat");
        let nat = s.add_sort("Nat");
        let boolean = s.add_sort("Bool"); // separate component
        s.add_subsort(zero, nat);
        s.add_subsort(nznat, nat);
        s.close();

        // reflexivity + declared + (none transitive here beyond declared)
        assert!(s.leq(nat, nat));
        assert!(s.leq(zero, nat));
        assert!(s.leq(nznat, nat));
        assert!(!s.leq(nat, zero));
        assert!(!s.leq(zero, nznat));

        // kinds: Nat-family together, Bool apart
        assert!(s.same_kind(zero, nat));
        assert!(s.same_kind(nznat, nat));
        assert!(!s.same_kind(boolean, nat));
        assert!(!s.leq(boolean, nat));
        assert_eq!(s.num_kinds(), 2);
    }

    #[test]
    fn every_sort_is_below_its_kind_error() {
        let mut s = Sorts::new();
        let a = s.add_sort("A");
        let b = s.add_sort("B");
        s.add_subsort(a, b);
        s.close();

        let k = s.kind_of(a);
        let err = s.error_sort(k);
        assert!(s.sort(err).is_error);
        assert!(s.leq(a, err));
        assert!(s.leq(b, err));
        assert_eq!(s.kind_of(b), k);
        assert_eq!(s.kind_of(err), k);
        // the error sort is maximal: not below any proper sort
        assert!(!s.leq(err, a));
        assert!(!s.leq(err, b));
    }

    #[test]
    fn transitive_closure() {
        let mut s = Sorts::new();
        let a = s.add_sort("A");
        let mid = s.add_sort("Mid");
        let top = s.add_sort("Top");
        s.add_subsort(a, mid);
        s.add_subsort(mid, top);
        s.close();
        assert!(s.leq(a, top), "a <= mid <= top should imply a <= top");
        assert!(s.leq(a, mid));
        assert!(!s.leq(top, a));
    }

    #[test]
    #[should_panic(expected = "subsort cycle")]
    fn subsort_cycle_is_rejected() {
        let mut s = Sorts::new();
        let a = s.add_sort("A");
        let b = s.add_sort("B");
        s.add_subsort(a, b);
        s.add_subsort(b, a);
        s.close();
    }
}
