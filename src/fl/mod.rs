pub mod cfl;
pub(crate) mod nfl;
pub mod sfl;
pub(crate) mod slfreelist;

use core::sync::atomic::{AtomicUsize, Ordering};

static NEXT_CID: AtomicUsize = AtomicUsize::new(1);

pub(crate) fn next_cid() -> usize {
    NEXT_CID.fetch_add(1, Ordering::Relaxed)
}

macro_rules! fl_node {
    ($name:ident, $next:ty) => {
        pub struct $name<T> {
            pub(crate) val: MaybeUninit<T>,
            pub(crate) next: $next,
            pub(crate) is_free: bool,
            pub(crate) gen_id: u32,
        }
    };
}

pub(crate) use fl_node;

const NONE: usize = usize::MAX;

pub trait FreeList<T> {
    type FlNode: FlNode;

    fn new(capacity: usize) -> Self;
    fn acquire(&mut self, val: T) -> *mut Self::FlNode;
    fn release(&mut self, ptr: *mut Self::FlNode) -> T;
    fn capacity(&self) -> usize;
    fn len(&self) -> usize;
    fn cid(&self) -> usize;

    /// Get pointer to inner value from node pointer
    fn val_ptr(node: *mut Self::FlNode) -> *mut T;

    /// Get node pointer from inner value pointer
    fn node_from_val_ptr(val_ptr: *mut T) -> *mut Self::FlNode;
}

/// Trait for freelist node types to expose gen_id for handle validation
pub trait FlNode {
    fn gen_id(&self) -> u32;
    fn is_free(&self) -> bool;
}

macro_rules! fn_capacity {
    () => {
        fn capacity(&self) -> usize {
            return self.capacity;
        }
    };
}

pub(crate) use fn_capacity;

macro_rules! fn_len {
    () => {
        fn len(&self) -> usize {
            return self.len;
        }
    };
}
pub(crate) use fn_len;

macro_rules! fn_cid {
    () => {
        fn cid(&self) -> usize {
            self.cid
        }
    };
}

pub(crate) use fn_cid;
