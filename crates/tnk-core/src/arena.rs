//! A non-moving, garbage-collected index arena (decision **D2**).
//!
//! Slots are never relocated, so [`Id<T>`] handles stay valid for a node's lifetime. Reclaimed
//! slots return to a free list and may be reused; because the GC only frees *unreachable* nodes,
//! no live id ever dangles, so we do not need generational tags (deferred — see D2).
//!
//! The arena exposes mark/sweep primitives so a theory-aware tracer (the DAG's GC) can drive
//! reachability from a root set: [`Arena::clear_marks`] → mark roots transitively via
//! [`Arena::mark`] → [`Arena::sweep`].

use crate::id::Id;

enum Slot<T> {
    Occupied(T),
    Free,
}

/// A slab of `T` addressed by stable [`Id<T>`] handles, with mark-and-sweep GC support.
pub struct Arena<T> {
    slots: Vec<Slot<T>>,
    free: Vec<u32>,
    marks: Vec<bool>,
    live: usize,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self { slots: Vec::new(), free: Vec::new(), marks: Vec::new(), live: 0 }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            slots: Vec::with_capacity(cap),
            free: Vec::new(),
            marks: Vec::with_capacity(cap),
            live: 0,
        }
    }

    /// Number of live (occupied) slots.
    pub fn len(&self) -> usize {
        self.live
    }

    pub fn is_empty(&self) -> bool {
        self.live == 0
    }

    /// Total slots ever allocated (live + free); the high-water mark of the slab.
    pub fn capacity(&self) -> usize {
        self.slots.len()
    }

    /// Allocate `value`, reusing a free slot if one is available. O(1).
    pub fn alloc(&mut self, value: T) -> Id<T> {
        self.live += 1;
        if let Some(raw) = self.free.pop() {
            self.slots[raw as usize] = Slot::Occupied(value);
            self.marks[raw as usize] = false;
            Id::from_raw(raw)
        } else {
            let raw = u32::try_from(self.slots.len()).expect("arena exceeded u32 capacity");
            self.slots.push(Slot::Occupied(value));
            self.marks.push(false);
            Id::from_raw(raw)
        }
    }

    pub fn get(&self, id: Id<T>) -> &T {
        match &self.slots[id.index()] {
            Slot::Occupied(v) => v,
            Slot::Free => panic!("Arena::get on freed {id:?}"),
        }
    }

    pub(crate) fn get_mut(&mut self, id: Id<T>) -> &mut T {
        match &mut self.slots[id.index()] {
            Slot::Occupied(v) => v,
            Slot::Free => panic!("Arena::get_mut on freed {id:?}"),
        }
    }

    pub fn try_get(&self, id: Id<T>) -> Option<&T> {
        match self.slots.get(id.index())? {
            Slot::Occupied(v) => Some(v),
            Slot::Free => None,
        }
    }

    /// True if `id` currently points at a live node.
    pub fn contains(&self, id: Id<T>) -> bool {
        matches!(self.slots.get(id.index()), Some(Slot::Occupied(_)))
    }

    // ---- GC ----

    /// Mark `id` reachable. Returns `true` if this newly marked it (lets a tracer prune
    /// already-visited subgraphs and terminate on shared DAG structure).
    pub(crate) fn mark(&mut self, id: Id<T>) -> bool {
        let slot = &mut self.marks[id.index()];
        if *slot {
            false
        } else {
            *slot = true;
            true
        }
    }

    pub fn is_marked(&self, id: Id<T>) -> bool {
        self.marks[id.index()]
    }

    pub(crate) fn clear_marks(&mut self) {
        self.marks.fill(false);
    }

    /// Reclaim every occupied-but-unmarked slot, handing each freed value to `on_free`
    /// (e.g. to release external resources). Returns the count reclaimed.
    pub(crate) fn sweep(&mut self, mut on_free: impl FnMut(T)) -> usize {
        let mut reclaimed = 0;
        for raw in 0..self.slots.len() {
            if !self.marks[raw] && matches!(self.slots[raw], Slot::Occupied(_)) {
                if let Slot::Occupied(v) = core::mem::replace(&mut self.slots[raw], Slot::Free) {
                    on_free(v);
                }
                self.free.push(raw as u32);
                self.live -= 1;
                reclaimed += 1;
            }
        }
        reclaimed
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn alloc_and_get() {
        let mut a = Arena::new();
        let x = a.alloc(10u32);
        let y = a.alloc(20u32);
        assert_eq!(*a.get(x), 10);
        assert_eq!(*a.get(y), 20);
        assert_eq!(a.len(), 2);
        assert_eq!(a.capacity(), 2);
    }

    #[test]
    fn mark_reports_newly_marked() {
        let mut a = Arena::new();
        let x = a.alloc(());
        a.clear_marks();
        assert!(a.mark(x), "first mark is new");
        assert!(!a.mark(x), "second mark is a no-op");
        assert!(a.is_marked(x));
    }

    #[test]
    fn sweep_reclaims_unmarked_and_reuses_slot() {
        let mut a: Arena<u32> = Arena::new();
        let keep = a.alloc(1);
        let gone = a.alloc(2);
        assert_eq!(a.len(), 2);

        a.clear_marks();
        a.mark(keep);
        let freed = a.sweep(|_| {});

        assert_eq!(freed, 1);
        assert_eq!(a.len(), 1);
        assert!(a.contains(keep));
        assert!(!a.contains(gone));
        assert_eq!(*a.get(keep), 1);

        // the reclaimed slot is recycled (non-moving: no growth)
        let reused = a.alloc(3);
        assert_eq!(reused, gone, "freed slot id is recycled");
        assert_eq!(a.capacity(), 2);
        assert_eq!(*a.get(reused), 3);
    }

    #[test]
    fn sweep_runs_destructors_via_callback() {
        let mut a = Arena::new();
        let _ = a.alloc(String::from("garbage"));
        a.clear_marks();
        let mut freed = Vec::new();
        a.sweep(|s| freed.push(s));
        assert_eq!(freed, vec![String::from("garbage")]);
    }
}
