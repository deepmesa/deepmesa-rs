//! A collection of data structures and algorithms in Rust.

/// A collection of list data structures and algorithms designed for
/// performance
pub mod lists {
    pub use deepmesa_lists::linkedlist::list::FastLinkedList;
    /// This module contains structs specific to the [`FastLinkedList`]
    pub mod linkedlist {
        pub use deepmesa_lists::linkedlist::node::Node;
    }
}
