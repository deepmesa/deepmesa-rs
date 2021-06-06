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
        pub use deepmesa_collections::bitvec::bitslice::BitSlice;
        pub use deepmesa_collections::bitvec::iter::Iter;
        pub use deepmesa_collections::bitvec::iter::IterMut;
        pub use deepmesa_collections::bitvec::iter::IterOnes;
        pub use deepmesa_collections::bitvec::iter::IterU128;
        pub use deepmesa_collections::bitvec::iter::IterU16;
        pub use deepmesa_collections::bitvec::iter::IterU32;
        pub use deepmesa_collections::bitvec::iter::IterU64;
        pub use deepmesa_collections::bitvec::iter::IterU8;
        pub use deepmesa_collections::bitvec::iter::IterZeros;
        pub use deepmesa_collections::bitvec::traits::AsLsb0;
        pub use deepmesa_collections::bitvec::traits::AsMsb0;
        pub use deepmesa_collections::bitvec::traits::BitwiseClear;
        pub use deepmesa_collections::bitvec::traits::BitwiseClearAssign;
        pub use deepmesa_collections::bitvec::traits::BitwiseLsb;
        pub use deepmesa_collections::bitvec::traits::BitwiseLsbAssign;
        pub use deepmesa_collections::bitvec::traits::BitwiseMsb;
        pub use deepmesa_collections::bitvec::traits::BitwiseMsbAssign;
        pub use deepmesa_collections::bitvec::traits::BitwisePartial;
        pub use deepmesa_collections::bitvec::traits::BitwisePartialAssign;
        pub use deepmesa_collections::bitvec::traits::NotLsb;
        pub use deepmesa_collections::bitvec::traits::NotLsbAssign;
        pub use deepmesa_collections::bitvec::traits::NotMsb;
        pub use deepmesa_collections::bitvec::traits::NotMsbAssign;
        pub use deepmesa_collections::bitvec::traits::NotPartial;
        pub use deepmesa_collections::bitvec::traits::NotPartialAssign;
        pub use deepmesa_collections::bitvec::BitOrder;
    }

    pub use deepmesa_collections::bitvec::bitvec::BitVector;
    pub use deepmesa_collections::bitvector;
}
