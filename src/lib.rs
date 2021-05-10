//! A collection of data structures and algorithms designed for performance.

/// A collection of list data structures and algorithms designed for
/// performance
pub mod lists {
    pub use deepmesa_lists::linkedlist::list::LinkedList;
    /// This module contains structs specific to the [`LinkedList`]
    pub mod linkedlist {
        pub use deepmesa_lists::linkedlist::node::Node;
    }
}

/// Data structures that implement various collections that are
/// designed for performance
pub mod collections {
    /// This module contains traits and structs specific to th ['BitVector']
    pub mod bitvec {
        pub use deepmesa_collections::bitvec::bitslice::BitSlice;
        pub use deepmesa_collections::bitvec::bitslice::Slice;
        pub use deepmesa_collections::bitvec::BitOrder;
    }
    pub use deepmesa_collections::bitvec::bitvec::BitVector;
}
