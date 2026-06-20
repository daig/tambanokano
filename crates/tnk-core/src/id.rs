//! Engine-relative typed indices (decision **D1**).
//!
//! An [`Id<T>`] indexes into an [`crate::arena::Arena<T>`] owned by a single `Engine`. Ids from
//! different engines must not be mixed; this is an invariant enforced by convention (we do not
//! expose arithmetic on ids). `Id<T>` is `Copy` and as small as a `u32` regardless of `T`.

use core::fmt;
use core::hash::{Hash, Hasher};
use core::marker::PhantomData;

/// A stable handle to a `T` stored in an `Arena<T>`. Valid for the lifetime of that node
/// (decision **D2**: the GC only frees unreachable nodes, so a live id never dangles).
pub struct Id<T> {
    raw: u32,
    // `fn() -> T` makes `Id<T>` unconditionally `Send`/`Sync`/`Copy` and covariant in `T`,
    // without implying ownership of a `T`.
    _t: PhantomData<fn() -> T>,
}

impl<T> Id<T> {
    #[inline]
    pub(crate) const fn from_raw(raw: u32) -> Self {
        Self { raw, _t: PhantomData }
    }
    #[inline]
    pub(crate) const fn index(self) -> usize {
        self.raw as usize
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
