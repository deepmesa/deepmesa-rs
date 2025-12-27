use core::fmt;
use std::fmt::Debug;
use std::ptr;

//mod.rs
pub mod rbtree;
pub mod traits;

pub const RED: usize = 1;
pub const BLACK: usize = 0;

macro_rules! is_red {
    ($node:expr) => {
        if $node.is_null() {
            false
        } else {
            unsafe { ((*$node).parent as usize) & 1 == crate::tree::rb::RED }
        }
    };
}

macro_rules! is_black {
    ($node:expr) => {
        if $node.is_null() {
            true // NIL nodes are black
        } else {
            unsafe {
                // Extract color bit from parent pointer
                // Note: if parent is null, this still works correctly
                // because null (0) & 1 == 0 == BLACK
                ((*$node).parent as usize) & 1 == crate::tree::rb::BLACK
            }
        }
    };
}

macro_rules! set_red {
    ($node:expr) => {
        if !$node.is_null() {
            unsafe {
                let parent_addr = (*$node).parent as usize;
                (*$node).parent = (parent_addr | crate::tree::rb::RED) as *mut TreeNode<_>;
            }
        }
    };
}

macro_rules! set_black {
    ($node:expr) => {
        if !$node.is_null() {
            unsafe {
                let parent_addr = (*$node).parent as usize;
                (*$node).parent = (parent_addr & !crate::tree::rb::RED) as *mut TreeNode<_>;
            }
        }
    };
}

macro_rules! get_parent {
    ($node:expr) => {
        if $node.is_null() {
            std::ptr::null_mut()
        } else {
            unsafe {
                let parent_addr = (*$node).parent as usize;
                (parent_addr & !1) as *mut _
            }
        }
    };
}

macro_rules! set_parent {
    ($node:expr, $parent:expr) => {
        if !$node.is_null() {
            unsafe {
                let color = ((*$node).parent as usize) & 1;
                (*$node).parent = (($parent as usize) | color) as *mut TreeNode<_>;
            }
        }
    };
}

macro_rules! color_str {
    ($node:expr) => {
        if is_red!($node) {
            "RED"
        } else {
            "BLACK"
        }
    };
}

// Export macros for use within the crate
pub(crate) use color_str;
pub(crate) use get_parent;
pub(crate) use is_black;
pub(crate) use is_red;
pub(crate) use set_black;
pub(crate) use set_parent;
pub(crate) use set_red;

pub struct TreeNode<T> {
    pub(crate) val: T,
    pub(crate) parent: *mut TreeNode<T>,
    pub(crate) left: *mut TreeNode<T>,
    pub(crate) right: *mut TreeNode<T>,
}

#[derive(Debug, PartialEq)]
pub struct NodeHandle<T> {
    pub(super) cid: usize,
    pub(super) gen_id: u32,
    pub(super) ptr: *mut TreeNode<T>,
}

impl<T> TreeNode<T> {
    pub(super) fn new(val: T) -> TreeNode<T> {
        TreeNode {
            val,
            parent: ptr::null_mut(),
            left: ptr::null_mut(),
            right: ptr::null_mut(),
        }
    }
}

impl<T> NodeHandle<T> {
    pub(super) fn new(cid: usize, gen_id: u32, ptr: *mut TreeNode<T>) -> NodeHandle<T> {
        NodeHandle { cid, gen_id, ptr }
    }
}

impl<T> Debug for TreeNode<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:?}:[{:?}] -> [{:?}, {:?}]",
            self.val, self.parent, self.left, self.right
        )
    }
}

