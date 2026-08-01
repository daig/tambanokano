//! A non-moving, garbage-collected index arena.
//!
//! Slots are never relocated, so [`Id<T>`] handles stay valid for a node's lifetime. Reclaimed
//! slots return to a free list and may be reused; because the GC only frees *unreachable* nodes,
//! no live id ever dangles, so we do not need generational tags in release builds.
//!
//! The arena exposes mark/sweep primitives so a theory-aware tracer (the DAG's GC) can drive
//! reachability from a root set: `Arena::clear_marks` → mark roots transitively via
//! `Arena::mark` → `Arena::sweep`.

use crate::id::Id;

enum Slot<T> {
    Occupied(T),
    Free,
}

/// Hands out a fresh process-global arena id each call (debug only). `0` is reserved as the
/// "no arena" sentinel used by [`Id::from_raw`], so this starts at `1`. (Wraps after 2^32−1 arenas
/// in one process — a debug-only diagnostic limit, far beyond any real run.)
#[cfg(debug_assertions)]
fn next_arena_id() -> u32 {
    use core::sync::atomic::{AtomicU32, Ordering};
    static COUNTER: AtomicU32 = AtomicU32::new(1);
    COUNTER.fetch_add(1, Ordering::Relaxed)
}

/// A slab of `T` addressed by stable [`Id<T>`] handles, with mark-and-sweep GC support.
///
/// In debug builds each slot also carries a *generation* (bumped on free) and the arena carries a
/// unique id, both stamped into the [`Id`]s it mints, so a stale or cross-arena handle is caught at
/// access time. These cost nothing in release (the fields and checks are
/// `cfg(debug_assertions)`-gated and compiled out).
pub struct Arena<T> {
    slots: Vec<Slot<T>>,
    free: Vec<u32>,
    marks: Vec<bool>,
    live: usize,
    /// Per-slot generation, bumped each time the slot is freed; parallel to `slots`.
    #[cfg(debug_assertions)]
    generations: Vec<u32>,
    /// This arena's unique id, stamped into every handle it mints.
    #[cfg(debug_assertions)]
    id: u32,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self {
            slots: Vec::new(),
            free: Vec::new(),
            marks: Vec::new(),
            live: 0,
            #[cfg(debug_assertions)]
            generations: Vec::new(),
            #[cfg(debug_assertions)]
            id: next_arena_id(),
        }
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            slots: Vec::with_capacity(cap),
            free: Vec::new(),
            marks: Vec::with_capacity(cap),
            live: 0,
            #[cfg(debug_assertions)]
            generations: Vec::with_capacity(cap),
            #[cfg(debug_assertions)]
            id: next_arena_id(),
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
        let raw = if let Some(raw) = self.free.pop() {
            self.slots[raw as usize] = Slot::Occupied(value);
            self.marks[raw as usize] = false;
            raw
        } else {
            let raw = u32::try_from(self.slots.len()).expect("arena exceeded u32 capacity");
            self.slots.push(Slot::Occupied(value));
            self.marks.push(false);
            #[cfg(debug_assertions)]
            self.generations.push(0);
            raw
        };
        // Stamp the slot's current generation + this arena's id into the handle (debug only).
        let id = Id::from_raw(raw);
        #[cfg(debug_assertions)]
        let id = id.stamp(self.generations[raw as usize], self.id);
        id
    }

    pub fn get(&self, id: Id<T>) -> &T {
        self.check(id);
        match &self.slots[id.index()] {
            Slot::Occupied(v) => v,
            Slot::Free => panic!("Arena::get on freed {id:?}"),
        }
    }

    /// Iterate every live `(id, &value)` in slot order, with each handle properly stamped for this arena
    /// (so it round-trips through [`get`](Self::get)). Used for reverse lookups (name → symbol) that the
    /// kernel does not index.
    pub fn iter(&self) -> impl Iterator<Item = (Id<T>, &T)> + '_ {
        self.slots
            .iter()
            .enumerate()
            .filter_map(move |(raw, slot)| match slot {
                Slot::Occupied(v) => {
                    let id = Id::from_raw(raw as u32);
                    #[cfg(debug_assertions)]
                    let id = id.stamp(self.generations[raw], self.id);
                    Some((id, v))
                }
                Slot::Free => None,
            })
    }

    pub(crate) fn get_mut(&mut self, id: Id<T>) -> &mut T {
        self.check(id);
        match &mut self.slots[id.index()] {
            Slot::Occupied(v) => v,
            Slot::Free => panic!("Arena::get_mut on freed {id:?}"),
        }
    }

    /// Borrow `id` if it is live, else `None`. **Release caveat:** with the generational check
    /// compiled out, a *stale* handle whose slot was freed and then recycled reads as `Some` (the
    /// recycled node), so this is not a reliable cross-GC liveness probe in release — pin live nodes
    /// with a [`RootGuard`](crate::root::RootGuard) instead. (Debug returns `None` for such a handle.)
    pub fn try_get(&self, id: Id<T>) -> Option<&T> {
        if !self.id_is_current(id) {
            return None;
        }
        match self.slots.get(id.index())? {
            Slot::Occupied(v) => Some(v),
            Slot::Free => None,
        }
    }

    /// True if `id` currently points at a live node (debug: also false for a stale/cross-arena id).
    /// **Release caveat:** like [`try_get`](Self::try_get), a recycled slot makes a stale handle read
    /// as present, so this is not a reliable cross-GC liveness check in release.
    pub fn contains(&self, id: Id<T>) -> bool {
        self.id_is_current(id) && matches!(self.slots.get(id.index()), Some(Slot::Occupied(_)))
    }

    // ---- handle validity (debug-only; no-ops in release) ----

    /// Whether `id` is a live handle into *this* arena at its minted generation. Used by the
    /// non-panicking queries ([`try_get`](Self::try_get)/[`contains`](Self::contains)). Always
    /// `true` in release (no provenance is tracked).
    #[cfg(debug_assertions)]
    fn id_is_current(&self, id: Id<T>) -> bool {
        let (generation, arena) = id.meta();
        arena == self.id
            && id.index() < self.generations.len()
            && generation == self.generations[id.index()]
    }
    #[cfg(not(debug_assertions))]
    #[inline]
    fn id_is_current(&self, _id: Id<T>) -> bool {
        true
    }

    /// Assert `id` is a live handle into this arena (panics on a cross-arena or stale id — a logical
    /// use-after-free that would otherwise silently alias a recycled slot). No-op in release.
    #[cfg(debug_assertions)]
    fn check(&self, id: Id<T>) {
        let (generation, arena) = id.meta();
        assert_eq!(
            arena, self.id,
            "cross-arena/cross-engine Id {id:?}: minted by arena {arena}, used on arena {}",
            self.id
        );
        assert!(
            id.index() < self.generations.len(),
            "out-of-range Id {id:?}"
        );
        assert_eq!(
            generation,
            self.generations[id.index()],
            "stale Id {id:?}: its slot was freed/reused since the id was minted (use-after-free)"
        );
    }
    #[cfg(not(debug_assertions))]
    #[inline]
    fn check(&self, _id: Id<T>) {}

    // ---- GC ----

    /// Mark `id` reachable. Returns `true` if this newly marked it (lets a tracer prune
    /// already-visited subgraphs and terminate on shared DAG structure).
    pub(crate) fn mark(&mut self, id: Id<T>) -> bool {
        self.check(id);
        let slot = &mut self.marks[id.index()];
        if *slot {
            false
        } else {
            *slot = true;
            true
        }
    }

    pub fn is_marked(&self, id: Id<T>) -> bool {
        self.check(id);
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
                // Bump the slot generation so any surviving handle to the freed node is now stale and
                // will be caught at access time (debug only). Plain `+= 1` (not `wrapping_add`): if a
                // single slot were somehow freed 2^32 times, the debug overflow check aborts rather
                // than silently wrapping a generation back to a value an ancient handle still carries.
                #[cfg(debug_assertions)]
                {
                    self.generations[raw] += 1;
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

    /// Free a slot, let the next `alloc` recycle it, then access the *old* handle. In release this
    /// silently aliases the recycled node; in debug the generation check
    /// turns it into a panic at the point of misuse.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "stale")]
    fn recycled_slot_makes_stale_handle_panic() {
        let mut a: Arena<u32> = Arena::new();
        let stale = a.alloc(1);
        a.clear_marks(); // mark nothing
        a.sweep(|_| {}); // free `stale`'s slot, bumping its generation
        let _recycled = a.alloc(2); // reuses the same slot at the next generation
        let _ = a.get(stale); // old generation -> panic
    }

    /// The non-panicking queries report a stale handle as absent rather than aliasing the recycled
    /// node (debug only).
    #[cfg(debug_assertions)]
    #[test]
    fn stale_handle_reads_as_absent_in_safe_queries() {
        let mut a: Arena<u32> = Arena::new();
        let stale = a.alloc(1);
        a.clear_marks();
        a.sweep(|_| {});
        let recycled = a.alloc(2);
        assert!(!a.contains(stale), "stale handle is not contained");
        assert!(a.try_get(stale).is_none(), "stale handle reads as None");
        assert!(a.contains(recycled), "the recycled handle is live");
        assert_eq!(*a.get(recycled), 2);
    }

    /// A handle minted by one arena, used on another, is caught in debug.
    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "cross-arena")]
    fn cross_arena_handle_panics() {
        let mut a: Arena<u32> = Arena::new();
        let mut b: Arena<u32> = Arena::new();
        let from_a = a.alloc(1);
        let _ = b.alloc(2);
        let _ = b.get(from_a); // a's handle on b's arena -> panic
    }
}
