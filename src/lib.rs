//! A collection of data structures and algorithms designed for performance.

/// A collection of list data structures and algorithms designed for
/// performance
pub mod lists {
    pub use deepmesa_lists::linkedlist::list::LinkedList;
    /// This module contains structs specific to the [`LinkedList`]
    pub mod linkedlist {
        pub use deepmesa_lists::linkedlist::iter::Iter;
        pub use deepmesa_lists::linkedlist::iter::IterMut;
        pub use deepmesa_lists::linkedlist::node::Node;
    }
}

/// Data structures that implement various collections that are
/// designed for performance
pub mod collections {
    /// This module contains traits and structs specific to the [`BitVector`](BitVector)
    pub mod bitvec {
        /// A slice of bits backed by a [`BitVector`](../struct.BitVector.html).
        pub use deepmesa_collections::bitvec::bitslice::BitSlice;
        /// An immutable iterator over the bits of the
        /// [`BitVector`](../struct.BitVector.html) or [`BitSlice`](BitSlice).
        pub use deepmesa_collections::bitvec::iter::Iter;
        /// A mutable iterator over the bits of the
        /// [`BitVector`](../struct.BitVector.html) or [`BitSlice`](BitSlice).
        pub use deepmesa_collections::bitvec::iter::IterMut;
        /// An iterator that iterates over the bits of the
        /// [`BitVector`](../struct.BitVector.html) 128 bits at a time.
        pub use deepmesa_collections::bitvec::iter::IterU128;
        /// An iterator that iterates over the bits of the
        /// [`BitVector`](../struct.BitVector.html) 16 bits at a time.
        pub use deepmesa_collections::bitvec::iter::IterU16;
        /// An iterator that iterates over the bits of the
        /// [`BitVector`](../struct.BitVector.html) 32 bits at a time.
        pub use deepmesa_collections::bitvec::iter::IterU32;
        /// An iterator that iterates over the bits of the
        /// [`BitVector`](../struct.BitVector.html) 64 bits at a time.
        pub use deepmesa_collections::bitvec::iter::IterU64;
        /// An iterator that iterates over the bits of the
        /// [`BitVector`](../struct.BitVector.html) 8 bits at a time.
        pub use deepmesa_collections::bitvec::iter::IterU8;
        /// Trait that converts the bits to an `Lsb0` ordering.
        pub use deepmesa_collections::bitvec::traits::AsLsb0;
        /// Trait that converts the bits to an `Msb0` ordering.
        pub use deepmesa_collections::bitvec::traits::AsMsb0;
        /// Returns a value with some bits of self cleared.
        pub use deepmesa_collections::bitvec::traits::BitwiseClear;
        /// Clears some bits of self.
        pub use deepmesa_collections::bitvec::traits::BitwiseClearAssign;
        /// Bitwise `&` (and), `|` (or) and `^` (xor) operations on
        /// the Lsb bits of self.
        pub use deepmesa_collections::bitvec::traits::BitwiseLsb;
        /// Bitwise `&=` (and assign), `|=` (or assign) and `^=` (xor
        /// assign) operations on the Lsb bits of self.
        pub use deepmesa_collections::bitvec::traits::BitwiseLsbAssign;
        /// Bitwise `&` (and), `|` (or) and `^` (xor) operations on
        /// the Msb bits of self.
        pub use deepmesa_collections::bitvec::traits::BitwiseMsb;
        /// Bitwise `&=` (and assign), `|=` (or assign) and `^=` (xor
        /// assign) operations on the Msb bits of self.
        pub use deepmesa_collections::bitvec::traits::BitwiseMsbAssign;
        /// Bitwise `&` (and), `|` (or) and `^` (xor) operations on a
        /// subset of the bits of self.
        pub use deepmesa_collections::bitvec::traits::BitwisePartial;
        /// Bitwise `&=` (and assign), `|=` (or assign) and `^=` (xor
        /// assign) operations on a subset of bits of self.
        pub use deepmesa_collections::bitvec::traits::BitwisePartialAssign;
        /// Bitwise `!` (not) operation on the Lsb bits of self.
        pub use deepmesa_collections::bitvec::traits::NotLsb;
        /// Bitwise `!=` (not assign) operation on the Lsb bits of
        /// self.
        pub use deepmesa_collections::bitvec::traits::NotLsbAssign;
        /// Bitwise `!` (not) operation on the Msb bits of self.
        pub use deepmesa_collections::bitvec::traits::NotMsb;
        /// Bitwise `!=` (not assign) operation on the Msb bits of
        /// self.
        pub use deepmesa_collections::bitvec::traits::NotMsbAssign;
        /// Bitwise `!` (not) operation on a subset of the bits of
        /// self.
        pub use deepmesa_collections::bitvec::traits::NotPartial;
        /// Bitwise `!=` (not assign) operation on a subset of the
        /// bits of self.
        pub use deepmesa_collections::bitvec::traits::NotPartialAssign;
        /// This enum indicates the order in which bits are traversed
        /// and counted.
        pub use deepmesa_collections::bitvec::BitOrder;
    }

    pub use deepmesa_collections::bitvec::bitvec::BitVector;
    pub use deepmesa_collections::bitvector;
}
