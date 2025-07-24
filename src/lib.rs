#![allow(warnings)]
pub mod bitvec;
mod cdeque;
pub(crate) mod fl;
mod lhmap;
pub mod linkedlist;
mod stack;
mod tree;
mod vector;

pub use crate::linkedlist::list::LinkedList;

/// This module contains structs specific to the [`LinkedList`]
pub use crate::cdeque::cdeque::CircularDeque;

/// This module contains structs specific to the [`CircularDeque`]
pub mod deque {
    pub use crate::cdeque;
    pub use crate::cdeque::cdeque::ErrorCode;
    pub use crate::cdeque::cdeque::TryAllocError;
    pub use crate::cdeque::cdeque::TryReserveError;
    pub use crate::cdeque::iter::Drain;
    pub use crate::cdeque::iter::Iter;
    pub use crate::cdeque::iter::IterMut;
}

pub use crate::lhmap::lhmap::LinkedHashMap;
/// This module contains structs specific to the [`LinkedHashMap`]
pub mod map {
    pub use crate::lhmap::entry::Entry;
    pub use crate::lhmap::entry::Order;
}

pub use crate::bitvec::bitvec::BitVector;
