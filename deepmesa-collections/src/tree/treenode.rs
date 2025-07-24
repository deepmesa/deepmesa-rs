use core::ptr;
use std::fmt;
use std::fmt::Debug;

pub struct TreeNodeHandle<T> {
    pub(super) cid: usize,
    pub(super) nid: usize,
    pub(super) ptr: *mut TreeNode<T>,
}

impl<T> TreeNodeHandle<T> {
    pub(super) fn new(cid: usize, nid: usize, ptr: *mut TreeNode<T>) -> TreeNodeHandle<T> {
        return TreeNodeHandle { cid, nid, ptr };
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

pub struct TreeNode<T> {
    pub(super) val: T,
    pub(super) nid: usize,
    pub(super) fl_node: bool,
    pub(super) parent: *mut TreeNode<T>,
    pub(super) left: *mut TreeNode<T>,
    pub(super) right: *mut TreeNode<T>,
}

impl<T> TreeNode<T> {
    pub(super) fn new(val: T, nid: usize) -> TreeNode<T> {
        TreeNode {
            val,
            fl_node: false,
            nid,
            parent: ptr::null_mut(),
            left: ptr::null_mut(),
            right: ptr::null_mut(),
        }
    }
}
