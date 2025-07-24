// Binary Search Tree

use crate::tree::treenode::TreeNode;
use crate::tree::treenode::TreeNodeHandle;
use crate::tree::SLFreeList;
use std::fmt;
use std::fmt::Debug;

use core::ptr;

macro_rules! nid_inc {
    ($nid: expr) => {{
        let nid = $nid;
        $nid += 1;
        nid
    }};
}

pub struct BinarySearchTree<T> {
    cid: usize,
    nid: usize,
    fl: SLFreeList<T>,
    capacity: usize,
    root: *mut TreeNode<T>,
    len: usize,
}

fn inc_cid() -> usize {
    unsafe {
        static mut TREE_COUNTER: usize = 0;
        TREE_COUNTER += 1;
        return TREE_COUNTER;
    }
}

impl<T> Debug for BinarySearchTree<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.root.is_null() {
            write!(f, "root: [null]")?;
            return Ok(());
        }
        unsafe {
            write!(f, "root -> {:?}\n", (*self.root))?;
            self.write_node(f, (*self.root).left)?;
            self.write_node(f, (*self.root).right)?;
        }
        Ok(())
    }
}

impl<T> BinarySearchTree<T>
where
    T: Debug,
{
    unsafe fn write_node(&self, f: &mut fmt::Formatter<'_>, ptr: *mut TreeNode<T>) -> fmt::Result {
        if ptr.is_null() {
            return Ok(());
        }
        write!(f, "{:?} -> {:?}\n", ptr, *ptr)?;
        self.write_node(f, (*ptr).left)?;
        self.write_node(f, (*ptr).right)?;
        return Ok(());
    }
}

impl<T> BinarySearchTree<T> {
    pub fn new(capacity: usize) -> BinarySearchTree<T> {
        return BinarySearchTree {
            cid: inc_cid(),
            nid: 0,
            capacity,
            root: ptr::null_mut(),
            fl: SLFreeList::new(8),
            len: 0,
        };
    }

    pub fn capacity(&self) -> usize {
        return self.capacity;
    }
}
impl<T> BinarySearchTree<T>
where
    T: Ord,
{
    pub fn insert(&mut self, val: T) -> TreeNodeHandle<T> {
        let nid = nid_inc!(self.nid);
        let t_node = self.fl.acquire(val, nid);
        if self.root.is_null() {
            self.root = t_node;
        } else {
            let mut cur = self.root;
            unsafe {
                loop {
                    if (*t_node).val <= (*cur).val {
                        if (*cur).left.is_null() {
                            (*cur).left = t_node;
                            (*t_node).parent = cur;
                            break;
                        } else {
                            cur = (*cur).left;
                        }
                    } else {
                        if (*cur).right.is_null() {
                            (*cur).right = t_node;
                            (*t_node).parent = cur;
                            break;
                        } else {
                            cur = (*cur).right;
                        }
                    }
                }
            }
        }

        self.len += 1;
        return TreeNodeHandle::new(self.cid, nid, t_node);
    }

    pub fn len(&self) -> usize {
        return self.len;
    }

    pub fn parent_node(&self, node: &TreeNodeHandle<T>) -> Option<TreeNodeHandle<T>> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).parent.is_null() {
                    return None;
                }
                Some(TreeNodeHandle::new(
                    self.cid,
                    (*(*n_ptr).parent).nid,
                    (*n_ptr).parent,
                ))
            },
        }
    }

    pub fn left_node(&self, node: &TreeNodeHandle<T>) -> Option<TreeNodeHandle<T>> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).left.is_null() {
                    return None;
                }
                Some(TreeNodeHandle::new(
                    self.cid,
                    (*(*n_ptr).left).nid,
                    (*n_ptr).left,
                ))
            },
        }
    }

    pub fn left(&self, node: &TreeNodeHandle<T>) -> Option<&T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).left.is_null() {
                    return None;
                }
                Some(&(*(*n_ptr).left).val)
            },
        }
    }

    pub fn left_mut(&mut self, node: &TreeNodeHandle<T>) -> Option<&mut T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).left.is_null() {
                    return None;
                }
                Some(&mut (*(*n_ptr).left).val)
            },
        }
    }

    pub fn remove_left(&mut self, node: &TreeNodeHandle<T>) -> Option<T> {
        None
    }

    pub fn right_node(&self, node: &TreeNodeHandle<T>) -> Option<TreeNodeHandle<T>> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).right.is_null() {
                    return None;
                }
                Some(TreeNodeHandle::new(
                    self.cid,
                    (*(*n_ptr).right).nid,
                    (*n_ptr).right,
                ))
            },
        }
    }

    pub fn right(&self, node: &TreeNodeHandle<T>) -> Option<&T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).right.is_null() {
                    return None;
                }
                Some(&(*(*n_ptr).right).val)
            },
        }
    }

    pub fn right_mut(&mut self, node: &TreeNodeHandle<T>) -> Option<&mut T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).right.is_null() {
                    return None;
                }
                Some(&mut (*(*n_ptr).right).val)
            },
        }
    }

    pub fn get(&self, val: &T) -> Option<TreeNodeHandle<T>> {
        None
    }

    pub fn root(&self) -> Option<&T> {
        if self.root.is_null() {
            return None;
        }

        unsafe { Some(&(*self.root).val) }
    }

    pub fn root_node(&self) -> Option<TreeNodeHandle<T>> {
        if self.root.is_null() {
            return None;
        }

        unsafe {
            return Some(TreeNodeHandle::new(self.cid, (*self.root).nid, self.root));
        }
    }

    pub fn remove(&self, node: &TreeNodeHandle<T>) -> Option<T> {
        None
    }

    pub fn node(&self, node: &TreeNodeHandle<T>) -> Option<&T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe { Some(&(*n_ptr).val) },
        }
    }

    pub fn node_mut(&mut self, node: &TreeNodeHandle<T>) -> Option<&mut T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe { Some(&mut (*n_ptr).val) },
        }
    }

    // Iteration in sorted order
    pub fn iter() {}

    // Pre Order, In Order, Post Order
    pub fn iter_bf() {}

    // Pre Order, In Order, Post Order
    pub fn iter_df() {}

    fn node_ptr(&self, node: &TreeNodeHandle<T>) -> Option<*mut TreeNode<T>> {
        if node.cid != self.cid {
            return None;
        }
        unsafe {
            if (*node.ptr).fl_node {
                return None;
            }
            if (*node.ptr).nid != node.nid {
                return None;
            }
        }

        return Some((*node).ptr);
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_simple() {
        let mut bst = BinarySearchTree::<u8>::new(8);
        bst.insert(5);
        bst.insert(4);
        bst.insert(6);
        bst.insert(3);
        bst.insert(7);
        println!("{:?}", &bst);
    }
}
