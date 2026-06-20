//! GC roots: an [`Engine`](crate::engine::Engine) root registry and the RAII [`RootGuard`]
//! (decision **D2 amendment**, Stage A2).
//!
//! A `RootGuard` pins a `DagId` so the collector keeps it — and everything reachable from it — live;
//! it registers on construction and unregisters on `Drop`. Crucially it holds a *shared handle* to
//! the registry (`Rc<RefCell<…>>`), **not a borrow of the `Engine`**: a guard that borrowed the
//! engine would forbid the very `&mut self` calls (`reduce`, `make_free`) a caller needs to make
//! while holding roots. Reads/writes of the registry happen only at GC time and while minting/
//! dropping guards, so the `RefCell` is effectively uncontended.

use crate::dag::DagId;
use std::cell::RefCell;
use std::rc::Rc;

/// The set of currently-pinned roots. Slot-indexed with a free list so a [`RootGuard`] unregisters
/// in O(1) on drop. Shared between the `Engine` and every guard via [`Roots`].
#[derive(Default)]
pub(crate) struct RootRegistry {
    slots: Vec<Option<DagId>>,
    free: Vec<usize>,
}

impl RootRegistry {
    fn register(&mut self, id: DagId) -> usize {
        if let Some(slot) = self.free.pop() {
            self.slots[slot] = Some(id);
            slot
        } else {
            self.slots.push(Some(id));
            self.slots.len() - 1
        }
    }

    fn unregister(&mut self, slot: usize) {
        self.slots[slot] = None;
        self.free.push(slot);
    }

    /// Iterate the live (pinned) roots, in registration-slot order.
    pub(crate) fn live_roots(&self) -> impl Iterator<Item = DagId> + '_ {
        self.slots.iter().filter_map(|s| *s)
    }
}

/// A shared handle to an [`Engine`](crate::engine::Engine)'s root registry.
pub(crate) type Roots = Rc<RefCell<RootRegistry>>;

/// An RAII GC root: while it is alive its `DagId` (and everything reachable from it) survives
/// collection; dropping it releases the root. Obtain one from
/// [`Engine::root`](crate::engine::Engine::root). The pinned id can be read with [`get`](Self::get)
/// and retargeted with [`set`](Self::set) — e.g. to follow a term as a reduction rewrites it into a
/// new node.
///
/// Bind it to a named local; `let _ = engine.root(id)` drops it immediately (releasing the root).
/// Forgetting it (`mem::forget`) *leaks* the root — the pinned subgraph is never reclaimed, like any
/// leaked RAII guard. The `DagId` passed to [`Engine::root`](crate::engine::Engine::root) and
/// [`set`](Self::set) is not validated; a stale or cross-engine id surfaces at the next collection
/// (a debug panic, or a silently-kept wrong node in release), not at the call.
#[must_use = "dropping a RootGuard immediately unregisters the root it protects"]
pub struct RootGuard {
    registry: Roots,
    slot: usize,
}

impl RootGuard {
    pub(crate) fn new(registry: &Roots, id: DagId) -> Self {
        let slot = registry.borrow_mut().register(id);
        RootGuard { registry: Rc::clone(registry), slot }
    }

    /// The currently-pinned id.
    pub fn get(&self) -> DagId {
        self.registry.borrow().slots[self.slot].expect("RootGuard slot vacated while still held")
    }

    /// Retarget this root at `id` (e.g. after a reduction produced a new node).
    pub fn set(&self, id: DagId) {
        self.registry.borrow_mut().slots[self.slot] = Some(id);
    }
}

impl Drop for RootGuard {
    fn drop(&mut self) {
        self.registry.borrow_mut().unregister(self.slot);
    }
}
