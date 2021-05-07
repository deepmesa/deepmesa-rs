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
