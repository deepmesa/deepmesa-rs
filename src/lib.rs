#![allow(warnings)]
pub mod bitvec;
pub mod cdeque;
pub(crate) mod fl;
pub mod lhmap;
pub mod linkedlist;
mod stack;
pub mod tree;
// mod vector; // Module removed

/// Error type returned when a memory allocation operation fails.
///
/// This error contains both an error code indicating the type of failure
/// and a descriptive message explaining what went wrong.
///
/// # Examples
///
/// ```
/// # use deepmesa_collections::{TryAllocError, ErrorCode};
/// // TryAllocError is typically created internally by the library
/// // when allocation operations fail
/// ```
pub struct TryAllocError {
    /// The error code indicating the type of failure
    code: ErrorCode,
    /// A descriptive message explaining the error
    msg: String,
}

impl TryAllocError {
    pub(crate) fn new(code: ErrorCode, msg: String) -> TryAllocError {
        return TryAllocError { code, msg };
    }
}

/// Error codes for memory allocation and capacity management operations.
///
/// These error codes are used to indicate various failure conditions
/// when attempting to allocate or manage memory for the circular deque.
///
/// # Examples
///
/// ```
/// # use deepmesa_collections::ErrorCode;
/// let error = ErrorCode::AllocError;
/// // Handle allocation error appropriately
/// ```
pub enum ErrorCode {
    /// Memory allocation failed
    AllocError,
    /// Memory layout computation failed
    MemLayoutError,
    /// Capacity overflow (requested capacity too large)
    CapacityOverflow,
}

/// Error type returned when a memory reservation operation fails.
///
/// This error contains both an error code indicating the type of failure
/// and a descriptive message explaining what went wrong.
///
/// # Examples
///
/// ```
/// # use deepmesa_collections::{CircularDeque, TryReserveError};
/// let mut deque = CircularDeque::<i32>::new();
///
/// // This might fail if we request too much memory
/// match deque.try_reserve(usize::MAX) {
///     Ok(()) => println!("Successfully reserved memory"),
///     Err(error) => println!("Failed to reserve memory: {}", error.msg),
/// }
/// ```
pub struct TryReserveError {
    /// The error code indicating the type of failure
    pub code: ErrorCode,
    /// A descriptive message explaining the error
    pub msg: String,
}

impl TryReserveError {
    pub(crate) fn new(code: ErrorCode, msg: String) -> TryReserveError {
        return TryReserveError { code, msg };
    }
}

pub use crate::bitvec::bitvec::BitVector;
pub use crate::cdeque::cdeque::CircularDeque;
pub use crate::lhmap::lhmap::LinkedHashMap;
pub use crate::linkedlist::list::LinkedList;
pub use crate::tree::rb::rbtree::RedBlackTree;
