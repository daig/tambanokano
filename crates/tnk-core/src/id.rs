//! Engine-relative typed indices.
//!
//! An [`Id<T>`] indexes into an [`crate::arena::Arena<T>`] owned by a single `Engine`. Ids from
//! different engines must not be mixed, and a stable id must not outlive the slot it names. In
//! **release** builds `Id<T>` is a bare `u32` and both invariants are unenforced (stable ids +
//! non-moving slot reuse trade detection for size). In **debug** builds the id also
//! carries the arena's identity and the slot's *generation* at mint time:
//! [`Arena`](crate::arena::Arena) bumps a slot's generation when it frees it, so a stale
//! handle (slot reused since the id was minted — a logical use-after-free) or a cross-arena/
//! cross-engine handle **panics at access** instead of silently aliasing the wrong node.
//!
//! Equality/ordering/hashing are **raw-only in both profiles**, so program behavior is identical
//! across debug and release: the debug metadata only powers access-time assertions, it is never part
//! of a node's identity (a recycled slot's new id still compares equal to the old raw index).

use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;

/// Debug-only provenance carried inside an [`Id<T>`]: the minting arena's id and the slot's
/// generation at mint time. Absent (zero-sized) in release builds.
#[cfg(debug_assertions)]
#[derive(Clone, Copy)]
struct IdMeta {
    /// Slot generation at mint time; [`Arena`](crate::arena::Arena) bumps it on free.
    generation: u32,
    /// Identity of the minting arena (a process-global counter); catches cross-engine id misuse.
    arena: u32,
}

/// A stable handle to a `T` stored in an `Arena<T>`. Valid for the lifetime of that node
/// (the GC only frees unreachable nodes, so a live id never dangles).
pub struct Id<T> {
    raw: u32,
    // Debug-only provenance for stale/cross-arena detection; compiled out in release so `Id<T>`
    // is a bare `u32`.
    #[cfg(debug_assertions)]
    meta: IdMeta,
    // `fn() -> T` makes `Id<T>` unconditionally `Send`/`Sync`/`Copy` and covariant in `T`,
    // without implying ownership of a `T`.
    _t: PhantomData<fn() -> T>,
}

impl<T> Id<T> {
    /// Construct from a bare index, with no arena provenance (the debug `arena`/`generation` are the
    /// `0` sentinel). Used for indices that do not live in a GC'd [`Arena`](crate::arena::Arena)
    /// (e.g. sorts/kinds, which are never freed and are accessed by direct `Vec` indexing, not
    /// `Arena::get`). Arena handles are minted by `Arena::alloc` and then [`stamp`](Self::stamp)ed.
    #[inline]
    pub(crate) const fn from_raw(raw: u32) -> Self {
        Self {
            raw,
            #[cfg(debug_assertions)]
            meta: IdMeta {
                generation: 0,
                arena: 0,
            },
            _t: PhantomData,
        }
    }
    #[inline]
    pub(crate) const fn index(self) -> usize {
        self.raw as usize
    }

    /// Record the minting arena's id and the slot generation. Debug-only: the call site in
    /// `Arena::alloc` is itself `cfg(debug_assertions)`-gated, so release never references this.
    #[cfg(debug_assertions)]
    #[inline]
    pub(crate) fn stamp(mut self, generation: u32, arena: u32) -> Self {
        self.meta = IdMeta { generation, arena };
        self
    }

    /// `(generation, arena)` recorded at mint time (debug only).
    #[cfg(debug_assertions)]
    #[inline]
    pub(crate) fn meta(self) -> (u32, u32) {
        (self.meta.generation, self.meta.arena)
    }
}

// Hand-written impls so they hold for every `T` (deriving would add spurious `T: Trait` bounds).
impl<T> Clone for Id<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for Id<T> {}
impl<T> PartialEq for Id<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}
impl<T> Eq for Id<T> {}
impl<T> PartialOrd for Id<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl<T> Ord for Id<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.raw.cmp(&other.raw)
    }
}
impl<T> Hash for Id<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}
impl<T> fmt::Debug for Id<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Id({})", self.raw)
    }
}
