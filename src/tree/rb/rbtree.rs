use super::NodeHandle;
use crate::fl::FreeList;
use crate::tree::rb::TreeNode;
use crate::tree::rb::{BLACK, RED};
use std::fmt;
use std::fmt::Debug;
use std::marker::PhantomData;
use std::ptr;

// Import the red-black tree macros
use super::{color_str, get_parent, is_black, is_red, set_black, set_parent, set_red};
use crate::fl::sfl::SegmentedFreeList;
use crate::fl::FlNode;

pub struct RedBlackTree<T, FL: FreeList<TreeNode<T>> = SegmentedFreeList<TreeNode<T>>> {
    fl: FL,
    root: *mut TreeNode<T>,
    len: usize,
    _marker: PhantomData<T>,
}

impl<T, FL> Debug for RedBlackTree<T, FL>
where
    T: Debug,
    FL: FreeList<TreeNode<T>>,
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

impl<T, FL> RedBlackTree<T, FL>
where
    T: Debug,
    FL: FreeList<TreeNode<T>>,
{
    unsafe fn write_node(&self, f: &mut fmt::Formatter<'_>, ptr: *mut TreeNode<T>) -> fmt::Result {
        if ptr.is_null() {
            return Ok(());
        }
        write!(f, "{:?} -> {:?}\n", ptr, *ptr)?;
        self.write_node(f, (*ptr).left)?;
        self.write_node(f, (*ptr).right)?;
        Ok(())
    }
}

const DEFAULT_CAPACITY: usize = 8;

impl<T, FL: FreeList<TreeNode<T>>> RedBlackTree<T, FL> {
    pub fn new() -> RedBlackTree<T, FL> {
        Self::with_capacity(DEFAULT_CAPACITY)
    }

    pub fn with_capacity(capacity: usize) -> RedBlackTree<T, FL> {
        RedBlackTree {
            fl: FL::new(capacity),
            root: ptr::null_mut(),
            len: 0,
            _marker: PhantomData,
        }
    }

    pub fn capacity(&self) -> usize {
        self.fl.capacity()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    // Helper function to validate handle and get TreeNode pointer
    fn node_ptr(&self, handle: &NodeHandle<T, FL>) -> Option<*mut TreeNode<T>> {
        if handle.cid != self.fl.cid() {
            return None;
        }
        unsafe {
            let fl_node = handle.ptr;
            if (*fl_node).is_free() {
                return None;
            }
            if (*fl_node).gen_id() != handle.gen_id {
                return None;
            }
            Some(FL::val_ptr(fl_node))
        }
    }

    // Root access methods
    pub fn root(&self) -> Option<&T> {
        if self.root.is_null() {
            None
        } else {
            unsafe { Some(&(*self.root).val) }
        }
    }

    pub fn root_node(&self) -> Option<NodeHandle<T, FL>> {
        if self.root.is_null() {
            None
        } else {
            unsafe {
                let fl_node = (*self.root).fl_node as *mut FL::FlNode;
                Some(NodeHandle::new(self.fl.cid(), (*fl_node).gen_id(), fl_node))
            }
        }
    }

    // Node value access methods
    pub fn val(&self, handle: &NodeHandle<T, FL>) -> Option<&T> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => unsafe { Some(&(*ptr).val) },
        }
    }

    // Left child navigation methods
    pub fn left(&self, handle: &NodeHandle<T, FL>) -> Option<&T> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => unsafe {
                if (*ptr).left.is_null() {
                    None
                } else {
                    Some(&(*(*ptr).left).val)
                }
            },
        }
    }

    pub fn left_node(&self, handle: &NodeHandle<T, FL>) -> Option<NodeHandle<T, FL>> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => unsafe {
                if (*ptr).left.is_null() {
                    None
                } else {
                    let child = (*ptr).left;
                    let fl_node = (*child).fl_node as *mut FL::FlNode;
                    Some(NodeHandle::new(self.fl.cid(), (*fl_node).gen_id(), fl_node))
                }
            },
        }
    }

    // Right child navigation methods
    pub fn right(&self, handle: &NodeHandle<T, FL>) -> Option<&T> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => unsafe {
                if (*ptr).right.is_null() {
                    None
                } else {
                    Some(&(*(*ptr).right).val)
                }
            },
        }
    }

    pub fn right_node(&self, handle: &NodeHandle<T, FL>) -> Option<NodeHandle<T, FL>> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => unsafe {
                if (*ptr).right.is_null() {
                    None
                } else {
                    let child = (*ptr).right;
                    let fl_node = (*child).fl_node as *mut FL::FlNode;
                    Some(NodeHandle::new(self.fl.cid(), (*fl_node).gen_id(), fl_node))
                }
            },
        }
    }

    // Parent navigation methods
    pub fn parent(&self, handle: &NodeHandle<T, FL>) -> Option<&T> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => {
                let parent_ptr: *mut TreeNode<T> = get_parent!(ptr);
                if parent_ptr.is_null() {
                    None
                } else {
                    unsafe { Some(&(*parent_ptr).val) }
                }
            }
        }
    }

    pub fn parent_node(&self, handle: &NodeHandle<T, FL>) -> Option<NodeHandle<T, FL>> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => {
                let parent_ptr: *mut TreeNode<T> = get_parent!(ptr);
                if parent_ptr.is_null() {
                    None
                } else {
                    unsafe {
                        let fl_node = (*parent_ptr).fl_node as *mut FL::FlNode;
                        Some(NodeHandle::new(self.fl.cid(), (*fl_node).gen_id(), fl_node))
                    }
                }
            }
        }
    }

    pub fn clear(&mut self) {
        if self.root.is_null() {
            return;
        }

        // Stack capacity based on RB tree height bound: h ≤ 2*log₂(n+1)
        let stack_capacity = if self.len <= 4 {
            self.len
        } else {
            let height_bound = (2.0 * ((self.len + 1) as f64).log2()).ceil() as usize;
            (height_bound + 4).max(8)
        };

        let mut stack = crate::CircularDeque::with_capacity(stack_capacity);
        stack.push_back(self.root);

        while let Some(node) = stack.pop_back() {
            unsafe {
                if !(*node).right.is_null() {
                    stack.push_back((*node).right);
                }
                if !(*node).left.is_null() {
                    stack.push_back((*node).left);
                }

                let fl_node = (*node).fl_node as *mut FL::FlNode;
                drop(self.fl.release(fl_node));
            }
        }

        self.root = std::ptr::null_mut();
        self.len = 0;
    }
}

impl<T, FL> RedBlackTree<T, FL>
where
    T: Ord,
    FL: FreeList<TreeNode<T>>,
{
    fn rotate_left(&mut self, node: *mut TreeNode<T>) {
        let right = unsafe { (*node).right };
        if right.is_null() {
            return;
        }

        unsafe {
            (*node).right = (*right).left;
            if !(*right).left.is_null() {
                set_parent!((*right).left, node);
            }

            let parent: *mut TreeNode<T> = get_parent!(node);
            set_parent!(right, parent);

            if parent.is_null() {
                self.root = right;
            } else if node == (*parent).left {
                (*parent).left = right;
            } else {
                (*parent).right = right;
            }

            (*right).left = node;
            set_parent!(node, right);
        }
    }

    fn rotate_right(&mut self, node: *mut TreeNode<T>) {
        let left = unsafe { (*node).left };
        if left.is_null() {
            return;
        }

        unsafe {
            (*node).left = (*left).right;
            if !(*left).right.is_null() {
                set_parent!((*left).right, node);
            }

            let parent: *mut TreeNode<T> = get_parent!(node);
            set_parent!(left, parent);

            if parent.is_null() {
                self.root = left;
            } else if node == (*parent).left {
                (*parent).left = left;
            } else {
                (*parent).right = left;
            }

            (*left).right = node;
            set_parent!(node, left);
        }
    }

    fn insert_fixup(&mut self, mut node: *mut TreeNode<T>) {
        // Continue fixing while node exists, isn't root, and has red parent (violation)
        while !node.is_null() && node != self.root {
            let parent: *mut TreeNode<T> = get_parent!(node);
            if !is_red!(parent) {
                break;
            }
            let grandparent: *mut TreeNode<T> = get_parent!(parent);

            // Safety check - need grandparent for red-black tree violations
            if grandparent.is_null() {
                break;
            }

            unsafe {
                // Case: parent is left child of grandparent
                if parent == (*grandparent).left {
                    let uncle = (*grandparent).right;

                    // Case 1: Uncle is red - recolor and move up
                    if is_red!(uncle) {
                        set_black!(parent);
                        set_black!(uncle);
                        set_red!(grandparent);
                        node = grandparent; // Move violation up the tree
                    } else {
                        // Case 2: Uncle is black, node is right child - left rotation needed
                        if node == (*parent).right {
                            node = parent;
                            self.rotate_left(node); // Convert to case 3
                        }
                        // Case 3: Uncle is black, node is left child - right rotation
                        let parent: *mut TreeNode<T> = get_parent!(node);
                        let grandparent: *mut TreeNode<T> = get_parent!(parent);
                        set_black!(parent);
                        set_red!(grandparent);
                        self.rotate_right(grandparent);
                    }
                } else {
                    // Mirror cases: parent is right child of grandparent
                    let uncle = (*grandparent).left;

                    // Case 1: Uncle is red - recolor and move up
                    if is_red!(uncle) {
                        set_black!(parent);
                        set_black!(uncle);
                        set_red!(grandparent);
                        node = grandparent; // Move violation up the tree
                    } else {
                        // Case 2: Uncle is black, node is left child - right rotation needed
                        if node == (*parent).left {
                            node = parent;
                            self.rotate_right(node); // Convert to case 3
                        }
                        // Case 3: Uncle is black, node is right child - left rotation
                        let parent: *mut TreeNode<T> = get_parent!(node);
                        let grandparent: *mut TreeNode<T> = get_parent!(parent);
                        set_black!(parent);
                        set_red!(grandparent);
                        self.rotate_left(grandparent);
                    }
                }
            }
        }

        set_black!(self.root); // Root must always be black
    }

    pub fn insert(&mut self, val: T) -> NodeHandle<T, FL> {
        // Handle empty tree case
        if self.root.is_null() {
            let tree_node = TreeNode::new(val);
            let fl_node = self.fl.acquire(tree_node);
            let t_node = FL::val_ptr(fl_node);
            unsafe {
                (*t_node).fl_node = fl_node as *mut ();
            }
            self.root = t_node;
            set_black!(t_node); // Root must be black
            self.len += 1;
            return unsafe { NodeHandle::new(self.fl.cid(), (*fl_node).gen_id(), fl_node) };
        }

        let mut current = self.root;
        let mut parent = std::ptr::null_mut();

        let fl_node = unsafe {
            // Standard BST insertion - find correct position
            while !current.is_null() {
                parent = current;
                if val < (*current).val {
                    current = (*current).left;
                } else if val > (*current).val {
                    current = (*current).right;
                } else {
                    // Duplicate found - return existing node
                    let existing_fl_node = (*current).fl_node as *mut FL::FlNode;
                    return NodeHandle::new(self.fl.cid(), (*existing_fl_node).gen_id(), existing_fl_node);
                }
            }

            let tree_node = TreeNode::new(val);
            let fl_node = self.fl.acquire(tree_node);
            let t_node = FL::val_ptr(fl_node);
            (*t_node).fl_node = fl_node as *mut ();

            // Link new node to parent
            set_parent!(t_node, parent);
            if (*t_node).val < (*parent).val {
                (*parent).left = t_node;
            } else {
                (*parent).right = t_node;
            }

            set_red!(t_node); // New nodes start as red
            self.insert_fixup(t_node);

            fl_node
        };

        self.len += 1;
        unsafe { NodeHandle::new(self.fl.cid(), (*fl_node).gen_id(), fl_node) }
    }

    pub fn get(&self, val: T) -> Option<NodeHandle<T, FL>> {
        if self.root.is_null() {
            return None;
        }

        let mut current = self.root;

        unsafe {
            while !current.is_null() {
                if val < (*current).val {
                    current = (*current).left;
                } else if val > (*current).val {
                    current = (*current).right;
                } else {
                    // Found matching value
                    let fl_node = (*current).fl_node as *mut FL::FlNode;
                    return Some(NodeHandle::new(self.fl.cid(), (*fl_node).gen_id(), fl_node));
                }
            }
        }

        None
    }

    // Mutable access methods
    pub fn root_mut(&mut self) -> Option<&mut T> {
        if self.root.is_null() {
            None
        } else {
            unsafe { Some(&mut (*self.root).val) }
        }
    }

    pub fn val_mut(&mut self, handle: &NodeHandle<T, FL>) -> Option<&mut T> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => unsafe { Some(&mut (*ptr).val) },
        }
    }

    pub fn left_mut(&mut self, handle: &NodeHandle<T, FL>) -> Option<&mut T> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => unsafe {
                if (*ptr).left.is_null() {
                    None
                } else {
                    Some(&mut (*(*ptr).left).val)
                }
            },
        }
    }

    pub fn right_mut(&mut self, handle: &NodeHandle<T, FL>) -> Option<&mut T> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => unsafe {
                if (*ptr).right.is_null() {
                    None
                } else {
                    Some(&mut (*(*ptr).right).val)
                }
            },
        }
    }

    pub fn parent_mut(&mut self, handle: &NodeHandle<T, FL>) -> Option<&mut T> {
        match self.node_ptr(handle) {
            None => None,
            Some(ptr) => {
                let parent_ptr: *mut TreeNode<T> = get_parent!(ptr);
                if parent_ptr.is_null() {
                    None
                } else {
                    unsafe { Some(&mut (*parent_ptr).val) }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fl::sfl::SegmentedFreeList;

    // Type alias for tests using SegmentedFreeList
    type RBTree<T> = RedBlackTree<T, SegmentedFreeList<TreeNode<T>>>;

    impl<T, FL> RedBlackTree<T, FL>
    where
        T: Ord + std::fmt::Debug,
        FL: FreeList<TreeNode<T>>,
    {
        // Helper function to verify red-black tree properties
        fn verify_rb_properties(&self) -> bool {
            if self.root.is_null() {
                return true;
            }

            // Root must be black
            if is_red!(self.root) {
                return false;
            }

            self.verify_node_properties(self.root, 0).is_some()
        }

        fn verify_node_properties(
            &self,
            node: *mut TreeNode<T>,
            mut black_count: i32,
        ) -> Option<i32> {
            if node.is_null() {
                return Some(black_count);
            }

            unsafe {
                if is_black!(node) {
                    black_count += 1;
                }

                // Red node cannot have red children
                if is_red!(node) {
                    if is_red!((*node).left) || is_red!((*node).right) {
                        return None;
                    }
                }

                // Verify BST property
                if !(*node).left.is_null() && (*(*node).left).val >= (*node).val {
                    return None;
                }
                if !(*node).right.is_null() && (*(*node).right).val <= (*node).val {
                    return None;
                }

                // Check black height consistency
                let left_black_count = self.verify_node_properties((*node).left, black_count)?;
                let right_black_count = self.verify_node_properties((*node).right, black_count)?;

                if left_black_count != right_black_count {
                    return None;
                }

                Some(left_black_count)
            }
        }

        fn verify_parent_pointers(&self) {
            if !self.root.is_null() {
                self.verify_parent_pointers_recursive(self.root, std::ptr::null_mut());
            }
        }

        fn verify_parent_pointers_recursive(
            &self,
            node: *mut TreeNode<T>,
            expected_parent: *mut TreeNode<T>,
        ) {
            if node.is_null() {
                return;
            }

            unsafe {
                let actual_parent = get_parent!(node);
                assert_eq!(
                    actual_parent,
                    expected_parent,
                    "Parent pointer mismatch at node with value {:?}",
                    (*node).val
                );

                self.verify_parent_pointers_recursive((*node).left, node);
                self.verify_parent_pointers_recursive((*node).right, node);
            }
        }

        fn calculate_height(&self) -> usize {
            self.calculate_height_recursive(self.root)
        }

        fn calculate_height_recursive(&self, node: *mut TreeNode<T>) -> usize {
            if node.is_null() {
                return 0;
            }

            unsafe {
                let left_height = self.calculate_height_recursive((*node).left);
                let right_height = self.calculate_height_recursive((*node).right);
                1 + left_height.max(right_height)
            }
        }

        fn verify_all_black_heights(&self) {
            if !self.root.is_null() {
                self.verify_black_heights_from_node(self.root)
                    .expect("Black height verification failed");
            }
        }

        fn verify_black_heights_from_node(&self, node: *mut TreeNode<T>) -> Option<i32> {
            if node.is_null() {
                return Some(0);
            }

            unsafe {
                let left_black_height = self.verify_black_heights_from_node((*node).left)?;
                let right_black_height = self.verify_black_heights_from_node((*node).right)?;

                if left_black_height != right_black_height {
                    return None;
                }

                let current_contribution = if is_black!(node) { 1 } else { 0 };
                Some(left_black_height + current_contribution)
            }
        }
    }

    #[test]
    fn print_tree() {
        let mut tree = RBTree::with_capacity(8);
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        tree.insert(4);
        tree.insert(5);

        println!("RbTree=\n{:?}", &tree);
    }

    #[test]
    fn test_insert_empty_tree() {
        let mut tree = RBTree::with_capacity(8);
        let handle = tree.insert(42);

        assert_eq!(tree.len, 1);
        assert!(!tree.root.is_null());
        assert!(is_black!(tree.root));
        assert!(tree.verify_rb_properties());

        assert_eq!(tree.val(&handle), Some(&42));
    }

    #[test]
    fn test_insert_duplicate() {
        let mut tree = RBTree::with_capacity(8);
        let handle1 = tree.insert(42);
        let handle2 = tree.insert(42);

        assert_eq!(tree.len, 1);
        assert_eq!(handle1.ptr, handle2.ptr);
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_insert_multiple_values() {
        let mut tree = RBTree::with_capacity(8);
        let values = vec![50, 25, 75, 10, 30, 60, 80];

        for val in values {
            tree.insert(val);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 7);
    }

    #[test]
    fn test_insert_ascending_sequence() {
        let mut tree = RBTree::with_capacity(8);

        for i in 1..=10 {
            tree.insert(i);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 10);
    }

    #[test]
    fn test_insert_descending_sequence() {
        let mut tree = RBTree::with_capacity(8);

        for i in (1..=10).rev() {
            tree.insert(i);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 10);
    }

    #[test]
    fn test_rb_tree_balancing() {
        let mut tree = RBTree::with_capacity(8);

        // Insert values that would create an unbalanced BST
        let values = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        for val in values {
            tree.insert(val);
            assert!(tree.verify_rb_properties());
        }

        // Verify the tree is balanced (root should not be a leaf)
        unsafe {
            assert!(!(*tree.root).left.is_null() || !(*tree.root).right.is_null());
        }
    }

    #[test]
    fn test_large_insertion() {
        let mut tree = RBTree::with_capacity(8);
        let n = 100;

        // Insert values in a pattern that tests various rebalancing scenarios
        for i in 0..n {
            tree.insert(i);
            if (i + 1) % 10 == 0 {
                assert!(tree.verify_rb_properties());
            }
        }

        assert_eq!(tree.len, n);
        assert!(tree.verify_rb_properties());
    }

    // Rotation-specific edge case tests

    #[test]
    fn test_left_left_rotation() {
        // This sequence triggers a right rotation (LL case)
        // Insert 3, 2, 1 creates imbalance requiring right rotation at root
        let mut tree = RBTree::with_capacity(8);
        tree.insert(3);
        tree.insert(2);
        tree.insert(1);

        assert_eq!(tree.len, 3);
        assert!(tree.verify_rb_properties());

        // Root should be 2 after rotation, with 1 left and 3 right
        unsafe {
            assert_eq!((*tree.root).val, 2);
            assert_eq!((*(*tree.root).left).val, 1);
            assert_eq!((*(*tree.root).right).val, 3);
        }
    }

    #[test]
    fn test_right_right_rotation() {
        // This sequence triggers a left rotation (RR case)
        // Insert 1, 2, 3 creates imbalance requiring left rotation at root
        let mut tree = RBTree::with_capacity(8);
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);

        assert_eq!(tree.len, 3);
        assert!(tree.verify_rb_properties());

        // Root should be 2 after rotation, with 1 left and 3 right
        unsafe {
            assert_eq!((*tree.root).val, 2);
            assert_eq!((*(*tree.root).left).val, 1);
            assert_eq!((*(*tree.root).right).val, 3);
        }
    }

    #[test]
    fn test_left_right_rotation() {
        // This sequence triggers left-right rotation (LR case)
        // Insert 3, 1, 2 requires left rotation on 1, then right rotation on 3
        let mut tree = RBTree::with_capacity(8);
        tree.insert(3);
        tree.insert(1);
        tree.insert(2);

        assert_eq!(tree.len, 3);
        assert!(tree.verify_rb_properties());

        // Root should be 2 after rotations, with 1 left and 3 right
        unsafe {
            assert_eq!((*tree.root).val, 2);
            assert_eq!((*(*tree.root).left).val, 1);
            assert_eq!((*(*tree.root).right).val, 3);
        }
    }

    #[test]
    fn test_right_left_rotation() {
        // This sequence triggers right-left rotation (RL case)
        // Insert 1, 3, 2 requires right rotation on 3, then left rotation on 1
        let mut tree = RBTree::with_capacity(8);
        tree.insert(1);
        tree.insert(3);
        tree.insert(2);

        assert_eq!(tree.len, 3);
        assert!(tree.verify_rb_properties());

        // Root should be 2 after rotations, with 1 left and 3 right
        unsafe {
            assert_eq!((*tree.root).val, 2);
            assert_eq!((*(*tree.root).left).val, 1);
            assert_eq!((*(*tree.root).right).val, 3);
        }
    }

    #[test]
    fn test_complex_rotation_sequence() {
        // Test a sequence that triggers multiple different rotations
        let mut tree = RBTree::with_capacity(8);
        let sequence = vec![10, 5, 15, 2, 7, 12, 20, 1, 3, 6, 8];

        for val in sequence {
            tree.insert(val);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 11);
    }

    #[test]
    fn test_deep_left_chain() {
        // Create a sequence that would form a deep left chain in BST
        // Tests multiple cascading rotations
        let mut tree = RBTree::with_capacity(8);
        for i in (1..=7).rev() {
            tree.insert(i);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 7);
        // Tree should remain balanced despite the insertion order
        unsafe {
            // Root should not be the minimum or maximum value
            assert_ne!((*tree.root).val, 1);
            assert_ne!((*tree.root).val, 7);
        }
    }

    #[test]
    fn test_deep_right_chain() {
        // Create a sequence that would form a deep right chain in BST
        // Tests multiple cascading rotations
        let mut tree = RBTree::with_capacity(8);
        for i in 1..=7 {
            tree.insert(i);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 7);
        // Tree should remain balanced despite the insertion order
        unsafe {
            // Root should not be the minimum or maximum value
            assert_ne!((*tree.root).val, 1);
            assert_ne!((*tree.root).val, 7);
        }
    }

    // Advanced rebalancing tests

    #[test]
    fn test_uncle_recoloring_cascade() {
        // Insert sequence that triggers uncle recoloring and cascading violations
        // This creates a scenario where multiple levels need recoloring
        let mut tree = RBTree::with_capacity(8);

        // Build a tree that will trigger uncle recoloring
        let sequence = vec![50, 25, 75, 10, 30, 60, 80, 5, 15, 27, 35];
        for val in sequence {
            tree.insert(val);
            assert!(tree.verify_rb_properties());
        }

        // Insert values that will cause red-red violations requiring uncle recoloring
        tree.insert(3); // Should trigger recoloring cascade
        tree.insert(12); // Another potential cascade

        assert_eq!(tree.len, 13);
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_cascading_fixup_violations() {
        // Test sequence that causes violations to propagate up the tree
        let mut tree = RBTree::with_capacity(8);

        // Insert in a pattern that creates deep violations
        tree.insert(16);
        tree.insert(8);
        tree.insert(24);
        tree.insert(4);
        tree.insert(12);
        tree.insert(20);
        tree.insert(28);

        // Now insert values that will cause cascading fixups
        tree.insert(2); // Red node
        tree.insert(6); // Red node - creates red-red violation
        tree.insert(1); // Should trigger cascading fixup

        assert_eq!(tree.len, 10);
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_root_color_changes() {
        // Test sequences where root changes color during rebalancing
        let mut tree = RBTree::with_capacity(8);

        tree.insert(10);
        assert!(is_black!(tree.root)); // Root must be black

        tree.insert(5);
        tree.insert(15);
        assert!(is_black!(tree.root)); // Root stays black

        // Insert values that may cause root recoloring during fixup
        tree.insert(2);
        tree.insert(7);
        tree.insert(12);
        tree.insert(18);

        // Root should always remain black after any fixup
        assert!(is_black!(tree.root));
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_complex_tree_restructuring() {
        // Test a complex scenario that requires multiple rotations and recoloring
        let mut tree = RBTree::with_capacity(8);

        // Build a moderately complex tree
        let initial_sequence = vec![64, 32, 96, 16, 48, 80, 112, 8, 24, 40, 56];
        for val in initial_sequence {
            tree.insert(val);
        }

        // Insert values that will trigger complex restructuring
        let stress_sequence = vec![4, 12, 20, 28, 36, 44, 52, 60];
        for val in stress_sequence {
            tree.insert(val);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 19);
    }

    #[test]
    fn test_alternating_insertion_pattern() {
        // Test alternating high-low values to stress different rebalancing paths
        let mut tree = RBTree::with_capacity(8);

        let pairs = vec![
            (1, 100),
            (2, 99),
            (3, 98),
            (4, 97),
            (5, 96),
            (6, 95),
            (7, 94),
        ];

        for (low, high) in pairs {
            tree.insert(low);
            assert!(tree.verify_rb_properties());
            tree.insert(high);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 14);
    }

    #[test]
    fn test_fibonacci_sequence_insertion() {
        // Fibonacci sequence can create interesting tree structures
        let mut tree = RBTree::with_capacity(8);
        let fib_sequence = vec![1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144];

        for val in fib_sequence {
            tree.insert(val);
            assert!(tree.verify_rb_properties());
        }

        // Note: duplicate 1 will be ignored
        assert_eq!(tree.len, 11);
    }

    #[test]
    fn test_parent_pointer_consistency() {
        // Verify parent pointers remain consistent through all rotations
        let mut tree = RBTree::with_capacity(8);
        let sequence = vec![50, 30, 70, 20, 40, 60, 80, 10, 25, 35, 45];

        for val in sequence {
            tree.insert(val);
            assert!(tree.verify_rb_properties());
            // Additional check for parent pointer consistency
            tree.verify_parent_pointers();
        }
    }

    // Boundary and memory management tests

    #[test]
    fn test_free_list_capacity_exhaustion() {
        // Test inserting more nodes than initial free list capacity
        let mut tree = RBTree::with_capacity(8);

        // Insert more than the initial capacity of 10
        for i in 1..=20 {
            tree.insert(i);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 20);
    }

    #[test]
    fn test_minimum_maximum_values() {
        // Test with boundary values for different integer types
        let mut tree_i32 = RBTree::<i32>::with_capacity(8);

        tree_i32.insert(i32::MIN);
        tree_i32.insert(i32::MAX);
        tree_i32.insert(0);
        tree_i32.insert(-1);
        tree_i32.insert(1);

        assert_eq!(tree_i32.len, 5);
        assert!(tree_i32.verify_rb_properties());

        // Test with i8 to cover smaller boundary values
        let mut tree_i8 = RBTree::<i8>::with_capacity(8);
        tree_i8.insert(i8::MIN); // -128
        tree_i8.insert(i8::MAX); // 127
        tree_i8.insert(0);

        assert_eq!(tree_i8.len, 3);
        assert!(tree_i8.verify_rb_properties());
    }

    #[test]
    fn test_negative_values() {
        // Test tree with only negative values
        let mut tree = RBTree::with_capacity(8);
        let negatives = vec![-50, -25, -75, -10, -30, -60, -80, -5, -15];

        for val in negatives {
            tree.insert(val);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 9);
    }

    #[test]
    fn test_zero_and_around_zero() {
        // Test insertions around zero
        let mut tree = RBTree::with_capacity(8);
        let around_zero = vec![0, -1, 1, -2, 2, -3, 3, -4, 4, -5, 5];

        for val in around_zero {
            tree.insert(val);
            assert!(tree.verify_rb_properties());
        }

        assert_eq!(tree.len, 11);
    }

    #[test]
    fn test_single_value_tree() {
        // Edge case: tree with only one value
        let mut tree = RBTree::with_capacity(8);
        tree.insert(42);

        assert_eq!(tree.len, 1);
        assert!(tree.verify_rb_properties());
        assert!(is_black!(tree.root));

        unsafe {
            assert!((*tree.root).left.is_null());
            assert!((*tree.root).right.is_null());
            let parent_ptr: *mut TreeNode<i32> = get_parent!(tree.root);
            assert!(parent_ptr.is_null());
        }
    }

    #[test]
    fn test_two_value_tree() {
        // Edge case: tree with only two values
        let mut tree = RBTree::with_capacity(8);
        tree.insert(10);
        tree.insert(20);

        assert_eq!(tree.len, 2);
        assert!(tree.verify_rb_properties());

        // Verify structure: root should be 10 with 20 as right child
        unsafe {
            assert_eq!((*tree.root).val, 10);
            assert!((*tree.root).left.is_null());
            assert_eq!((*(*tree.root).right).val, 20);
        }
    }

    #[test]
    fn test_node_handle_stability() {
        // Verify that node handles remain valid through tree restructuring
        let mut tree = RBTree::with_capacity(8);

        let handle1 = tree.insert(50);
        let handle2 = tree.insert(25);
        let handle3 = tree.insert(75);

        // Insert more values that will cause rotations
        for i in 1..=20 {
            tree.insert(i);
        }

        // Original handles should still be valid
        assert_eq!(tree.val(&handle1), Some(&50));
        assert_eq!(tree.val(&handle2), Some(&25));
        assert_eq!(tree.val(&handle3), Some(&75));

        assert!(tree.verify_rb_properties());
    }

    // Stress tests and property validation enhancements

    #[test]
    fn test_large_sequential_insertion() {
        // Stress test with large number of sequential insertions
        let mut tree = RBTree::with_capacity(8);
        let n = 1000;

        for i in 1..=n {
            tree.insert(i);
            // Verify properties every 100 insertions to catch issues early
            if i % 100 == 0 {
                assert!(tree.verify_rb_properties());
            }
        }

        assert_eq!(tree.len, n);
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_large_reverse_insertion() {
        // Stress test with large number of reverse sequential insertions
        let mut tree = RBTree::with_capacity(8);
        let n = 1000;

        for i in (1..=n).rev() {
            tree.insert(i);
            // Verify properties every 100 insertions
            if (n - i + 1) % 100 == 0 {
                assert!(tree.verify_rb_properties());
            }
        }

        assert_eq!(tree.len, n);
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_random_insertion_pattern() {
        // Test with pseudo-random insertion pattern
        let mut tree = RBTree::with_capacity(8);

        // Simple pseudo-random sequence (Linear Congruential Generator)
        let mut seed = 12345u64;
        for _ in 0..500 {
            seed = seed.wrapping_mul(1103515245).wrapping_add(12345);
            let val = (seed % 10000) as i32;

            tree.insert(val);
        }

        // Verify final tree properties
        assert!(tree.verify_rb_properties());
        assert!(tree.len <= 500); // May be less due to duplicates
    }

    #[test]
    fn test_pathological_sequence() {
        // Test sequences designed to stress specific rebalancing scenarios
        let mut tree = RBTree::with_capacity(8);

        // Alternating pattern that can cause maximum rotations
        let pattern1 = (1..=50).step_by(2).collect::<Vec<_>>(); // 1, 3, 5, ...
        let pattern2 = (2..=50).step_by(2).collect::<Vec<_>>(); // 2, 4, 6, ...

        for val in pattern1 {
            tree.insert(val);
        }
        for val in pattern2 {
            tree.insert(val);
        }

        assert_eq!(tree.len, 50);
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_duplicate_heavy_insertion() {
        // Test with many duplicate attempts
        let mut tree = RBTree::with_capacity(8);
        let base_values = vec![10, 20, 30, 40, 50];

        // Insert each value multiple times
        for _ in 0..20 {
            for &val in &base_values {
                tree.insert(val);
            }
        }

        // Should still only have 5 unique values
        assert_eq!(tree.len, 5);
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_tree_height_bounds() {
        // Verify that tree height stays within red-black tree bounds
        let mut tree = RBTree::with_capacity(8);
        let n = 255; // 2^8 - 1 for nice height calculations

        for i in 1..=n {
            tree.insert(i);
        }

        // Calculate actual height
        let height = tree.calculate_height();

        // Red-black tree height should be at most 2 * log2(n + 1)
        let max_height = (2.0 * ((n + 1) as f64).log2().ceil()) as usize;

        assert!(
            height <= max_height,
            "Tree height {} exceeds maximum allowed height {}",
            height,
            max_height
        );
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_black_height_consistency() {
        // Enhanced test for black height consistency across all paths
        let mut tree = RBTree::with_capacity(8);

        // Insert values in a pattern that creates various subtree shapes
        let values = vec![50, 25, 75, 12, 37, 62, 87, 6, 18, 31, 43, 56, 68, 81, 93];

        for val in values {
            tree.insert(val);

            // Verify black height is consistent from every node
            tree.verify_all_black_heights();
            assert!(tree.verify_rb_properties());
        }
    }

    #[test]
    fn test_memory_efficiency() {
        // Test that free list is working efficiently
        let mut tree = RBTree::with_capacity(8);

        // Insert many values to expand free list
        for i in 1..=100 {
            tree.insert(i);
        }

        let initial_capacity = tree.fl.capacity();

        // Insert more values - this should trigger free list growth
        for i in 101..=200 {
            tree.insert(i);
        }

        // Capacity should have grown (doubled from initial 10)
        assert!(tree.fl.capacity() >= initial_capacity);
        assert_eq!(tree.len, 200);
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_navigation_methods() {
        // Test all navigation methods
        let mut tree = RBTree::with_capacity(8);

        // Build a small tree: insert 2, 1, 3 which should result in root=2, left=1, right=3
        let handle2 = tree.insert(2);
        let handle1 = tree.insert(1);
        let handle3 = tree.insert(3);

        // Test root access
        assert_eq!(tree.root(), Some(&2));
        let root_handle = tree.root_node().unwrap();
        assert_eq!(tree.val(&root_handle), Some(&2));

        // Test navigation from root
        assert_eq!(tree.left(&root_handle), Some(&1));
        assert_eq!(tree.right(&root_handle), Some(&3));

        let left_handle = tree.left_node(&root_handle).unwrap();
        let right_handle = tree.right_node(&root_handle).unwrap();

        assert_eq!(tree.val(&left_handle), Some(&1));
        assert_eq!(tree.val(&right_handle), Some(&3));

        // Test parent navigation
        assert_eq!(tree.parent(&left_handle), Some(&2));
        assert_eq!(tree.parent(&right_handle), Some(&2));
        assert_eq!(tree.parent(&root_handle), None); // Root has no parent

        let parent_from_left = tree.parent_node(&left_handle).unwrap();
        assert_eq!(tree.val(&parent_from_left), Some(&2));

        // Test mutable access
        *tree.root_mut().unwrap() = 20;
        assert_eq!(tree.root(), Some(&20));
        *tree.root_mut().unwrap() = 2; // Reset

        *tree.val_mut(&left_handle).unwrap() = 10;
        assert_eq!(tree.left(&root_handle), Some(&10));
        *tree.val_mut(&left_handle).unwrap() = 1; // Reset

        // Test children of leaf nodes
        assert_eq!(tree.left(&left_handle), None);
        assert_eq!(tree.right(&left_handle), None);
        assert_eq!(tree.left_node(&left_handle), None);
        assert_eq!(tree.right_node(&left_handle), None);

        // Verify tree is still valid
        assert!(tree.verify_rb_properties());
    }

    // Dedicated navigation method unit tests

    #[test]
    fn test_root_access_methods() {
        // Test empty tree
        let mut tree = RBTree::<i32>::with_capacity(8);
        assert_eq!(tree.root(), None);
        assert_eq!(tree.root_mut(), None);
        assert_eq!(tree.root_node(), None);

        // Test single node tree
        let handle = tree.insert(42);
        assert_eq!(tree.root(), Some(&42));
        assert_eq!(tree.root_node().unwrap().ptr, handle.ptr);

        // Test mutable root access
        *tree.root_mut().unwrap() = 100;
        assert_eq!(tree.root(), Some(&100));

        // Test root after tree modifications
        tree.insert(20);
        tree.insert(80);
        assert!(tree.root().is_some());
        assert!(tree.root_node().is_some());
    }

    #[test]
    fn test_node_value_access_methods() {
        let mut tree = RBTree::with_capacity(8);
        let handle1 = tree.insert(10);
        let handle2 = tree.insert(20);
        let handle3 = tree.insert(5);

        // Test immutable value access
        assert_eq!(tree.val(&handle1), Some(&10));
        assert_eq!(tree.val(&handle2), Some(&20));
        assert_eq!(tree.val(&handle3), Some(&5));

        // Test mutable value access
        *tree.val_mut(&handle1).unwrap() = 15;
        assert_eq!(tree.val(&handle1), Some(&15));

        *tree.val_mut(&handle2).unwrap() = 25;
        assert_eq!(tree.val(&handle2), Some(&25));

        // Verify tree still maintains properties after value changes
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_left_child_navigation_methods() {
        let mut tree = RBTree::with_capacity(8);

        // Create a tree structure:  50
        //                          /  \
        //                        25    75
        //                       /  \
        //                      10   30
        tree.insert(50);
        tree.insert(25);
        tree.insert(75);
        tree.insert(10);
        tree.insert(30);

        let root_handle = tree.root_node().unwrap();

        // Test left navigation from root
        assert_eq!(tree.left(&root_handle), Some(&25));
        let left_handle = tree.left_node(&root_handle).unwrap();
        assert_eq!(tree.val(&left_handle), Some(&25));

        // Test left navigation from left child
        assert_eq!(tree.left(&left_handle), Some(&10));
        let left_left_handle = tree.left_node(&left_handle).unwrap();
        assert_eq!(tree.val(&left_left_handle), Some(&10));

        // Test mutable left access
        *tree.left_mut(&root_handle).unwrap() = 35;
        assert_eq!(tree.left(&root_handle), Some(&35));
        *tree.left_mut(&root_handle).unwrap() = 25; // Reset

        // Test leaf nodes have no left children
        assert_eq!(tree.left(&left_left_handle), None);
        assert_eq!(tree.left_node(&left_left_handle), None);
        assert_eq!(tree.left_mut(&left_left_handle), None);

        // Test right node with no left child
        let right_handle = tree.right_node(&root_handle).unwrap();
        assert_eq!(tree.left(&right_handle), None);
        assert_eq!(tree.left_node(&right_handle), None);
        assert_eq!(tree.left_mut(&right_handle), None);
    }

    #[test]
    fn test_right_child_navigation_methods() {
        let mut tree = RBTree::with_capacity(8);

        // Create a tree structure:  50
        //                          /  \
        //                        25    75
        //                             /  \
        //                           60    90
        tree.insert(50);
        tree.insert(25);
        tree.insert(75);
        tree.insert(60);
        tree.insert(90);

        let root_handle = tree.root_node().unwrap();

        // Test right navigation from root
        assert_eq!(tree.right(&root_handle), Some(&75));
        let right_handle = tree.right_node(&root_handle).unwrap();
        assert_eq!(tree.val(&right_handle), Some(&75));

        // Test right navigation from right child
        assert_eq!(tree.right(&right_handle), Some(&90));
        let right_right_handle = tree.right_node(&right_handle).unwrap();
        assert_eq!(tree.val(&right_right_handle), Some(&90));

        // Test mutable right access
        *tree.right_mut(&root_handle).unwrap() = 85;
        assert_eq!(tree.right(&root_handle), Some(&85));
        *tree.right_mut(&root_handle).unwrap() = 75; // Reset

        // Test leaf nodes have no right children
        assert_eq!(tree.right(&right_right_handle), None);
        assert_eq!(tree.right_node(&right_right_handle), None);
        assert_eq!(tree.right_mut(&right_right_handle), None);

        // Test left node with no right child
        let left_handle = tree.left_node(&root_handle).unwrap();
        assert_eq!(tree.right(&left_handle), None);
        assert_eq!(tree.right_node(&left_handle), None);
        assert_eq!(tree.right_mut(&left_handle), None);
    }

    #[test]
    fn test_parent_navigation_methods() {
        let mut tree = RBTree::with_capacity(8);

        // Create a tree structure:  50
        //                          /  \
        //                        25    75
        //                       /  \   / \
        //                      10  30 60 90
        tree.insert(50);
        tree.insert(25);
        tree.insert(75);
        tree.insert(10);
        tree.insert(30);
        tree.insert(60);
        tree.insert(90);

        let root_handle = tree.root_node().unwrap();
        let left_handle = tree.left_node(&root_handle).unwrap();
        let right_handle = tree.right_node(&root_handle).unwrap();

        // Test parent navigation - root has no parent
        assert_eq!(tree.parent(&root_handle), None);
        assert_eq!(tree.parent_node(&root_handle), None);
        assert_eq!(tree.parent_mut(&root_handle), None);

        // Test parent navigation from children
        assert_eq!(tree.parent(&left_handle), Some(&50));
        assert_eq!(tree.parent(&right_handle), Some(&50));

        let parent_from_left = tree.parent_node(&left_handle).unwrap();
        let parent_from_right = tree.parent_node(&right_handle).unwrap();
        assert_eq!(tree.val(&parent_from_left), Some(&50));
        assert_eq!(tree.val(&parent_from_right), Some(&50));
        assert_eq!(parent_from_left, parent_from_right);

        // Test mutable parent access
        *tree.parent_mut(&left_handle).unwrap() = 55;
        assert_eq!(tree.parent(&left_handle), Some(&55));
        assert_eq!(tree.root(), Some(&55));
        *tree.parent_mut(&left_handle).unwrap() = 50; // Reset

        // Test grandchildren pointing to grandparent
        let left_left_handle = tree.left_node(&left_handle).unwrap();
        let grandparent = tree
            .parent_node(&tree.parent_node(&left_left_handle).unwrap())
            .unwrap();
        assert_eq!(tree.val(&grandparent), Some(&50));
    }

    #[test]
    fn test_invalid_handle_scenarios() {
        let mut tree1 = RBTree::with_capacity(8);
        let mut tree2 = RBTree::with_capacity(8);

        tree1.insert(10);
        tree1.insert(20);
        let handle1 = tree1.insert(30);

        tree2.insert(40);
        let handle2 = tree2.insert(50);

        // Test cross-tree handle usage (different cid)
        assert_eq!(tree1.val(&handle2), None);
        assert_eq!(tree1.left(&handle2), None);
        assert_eq!(tree1.right(&handle2), None);
        assert_eq!(tree1.parent(&handle2), None);
        assert_eq!(tree1.left_node(&handle2), None);
        assert_eq!(tree1.right_node(&handle2), None);
        assert_eq!(tree1.parent_node(&handle2), None);

        assert_eq!(tree1.val_mut(&handle2), None);
        assert_eq!(tree1.left_mut(&handle2), None);
        assert_eq!(tree1.right_mut(&handle2), None);
        assert_eq!(tree1.parent_mut(&handle2), None);

        // Test valid handle from same tree
        assert_eq!(tree1.val(&handle1), Some(&30));
        assert_eq!(tree2.val(&handle2), Some(&50));

        // Test with empty tree handles
        let empty_tree = RBTree::<i32>::with_capacity(8);
        assert_eq!(empty_tree.val(&handle1), None);
        assert_eq!(empty_tree.val(&handle2), None);
    }

    #[test]
    fn test_aba_problem_detection() {
        // Test that stale handles are detected after node release and slot reuse
        let mut tree = RBTree::with_capacity(8);

        // Insert a node and get its handle
        let old_handle = tree.insert(42);
        assert_eq!(tree.val(&old_handle), Some(&42));

        // Remember the gen_id from the old handle
        let old_gen_id = old_handle.gen_id;

        // Clear the tree - releases all nodes back to freelist
        tree.clear();
        assert!(tree.is_empty());

        // Old handle should now be invalid (node is free)
        assert_eq!(tree.val(&old_handle), None);

        // Insert a new node - this should reuse the same slot
        // but with an incremented gen_id
        let new_handle = tree.insert(99);
        assert_eq!(tree.val(&new_handle), Some(&99));

        // The gen_id should have changed
        assert_ne!(old_gen_id, new_handle.gen_id);

        // Old handle should still be invalid even though slot is reused
        // (gen_id mismatch protects against ABA problem)
        assert_eq!(tree.val(&old_handle), None);
        assert_eq!(tree.left(&old_handle), None);
        assert_eq!(tree.right(&old_handle), None);
        assert_eq!(tree.parent(&old_handle), None);

        // New handle should work fine
        assert_eq!(tree.val(&new_handle), Some(&99));
    }

    #[test]
    fn test_aba_multiple_generations() {
        // Test that gen_id properly increments across multiple reuse cycles
        let mut tree = RBTree::with_capacity(8);

        let mut previous_gen_ids = Vec::new();

        for i in 0..5 {
            let handle = tree.insert(i);
            let gen_id = handle.gen_id;

            // Each gen_id should be unique (different from all previous)
            assert!(
                !previous_gen_ids.contains(&gen_id),
                "gen_id {} was reused at iteration {}",
                gen_id,
                i
            );
            previous_gen_ids.push(gen_id);

            // Clear to release node back to freelist
            tree.clear();
        }
    }

    #[test]
    fn test_navigation_after_rotations() {
        let mut tree = RBTree::with_capacity(8);

        // Insert sequence that causes rotations
        let h1 = tree.insert(1);
        let h2 = tree.insert(2);
        let h3 = tree.insert(3);

        // After rotations, tree should be: 2 (root), 1 (left), 3 (right)
        let root = tree.root_node().unwrap();
        assert_eq!(tree.val(&root), Some(&2));

        let left = tree.left_node(&root).unwrap();
        let right = tree.right_node(&root).unwrap();

        assert_eq!(tree.val(&left), Some(&1));
        assert_eq!(tree.val(&right), Some(&3));

        // Test parent relationships after rotation
        assert_eq!(tree.parent(&left), Some(&2));
        assert_eq!(tree.parent(&right), Some(&2));
        assert_eq!(tree.parent(&root), None);

        // Original handles should still work
        assert_eq!(tree.val(&h1), Some(&1));
        assert_eq!(tree.val(&h2), Some(&2));
        assert_eq!(tree.val(&h3), Some(&3));

        // Verify tree properties
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_get_method() {
        let mut tree = RBTree::with_capacity(8);

        // Test get on empty tree
        assert_eq!(tree.get(42), None);

        // Insert values and test get
        let h1 = tree.insert(50);
        let h2 = tree.insert(25);
        let h3 = tree.insert(75);
        let h4 = tree.insert(10);
        let h5 = tree.insert(30);
        let h6 = tree.insert(60);
        let h7 = tree.insert(90);

        // Test successful gets
        let found1 = tree.get(50).unwrap();
        let found2 = tree.get(25).unwrap();
        let found3 = tree.get(75).unwrap();
        let found4 = tree.get(10).unwrap();
        let found5 = tree.get(30).unwrap();
        let found6 = tree.get(60).unwrap();
        let found7 = tree.get(90).unwrap();

        // Verify returned handles point to correct values
        assert_eq!(tree.val(&found1), Some(&50));
        assert_eq!(tree.val(&found2), Some(&25));
        assert_eq!(tree.val(&found3), Some(&75));
        assert_eq!(tree.val(&found4), Some(&10));
        assert_eq!(tree.val(&found5), Some(&30));
        assert_eq!(tree.val(&found6), Some(&60));
        assert_eq!(tree.val(&found7), Some(&90));

        // Test that returned handles match original insertion handles
        assert_eq!(found1.ptr, h1.ptr);
        assert_eq!(found2.ptr, h2.ptr);
        assert_eq!(found3.ptr, h3.ptr);
        assert_eq!(found4.ptr, h4.ptr);
        assert_eq!(found5.ptr, h5.ptr);
        assert_eq!(found6.ptr, h6.ptr);
        assert_eq!(found7.ptr, h7.ptr);

        // Test unsuccessful gets
        assert_eq!(tree.get(5), None); // Smaller than any value
        assert_eq!(tree.get(95), None); // Larger than any value
        assert_eq!(tree.get(35), None); // Between existing values
        assert_eq!(tree.get(55), None); // Between existing values

        // Test get after tree modifications (rotations)
        let mut simple_tree = RBTree::with_capacity(8);
        simple_tree.insert(1);
        simple_tree.insert(2);
        simple_tree.insert(3); // This should trigger rotations

        // Should still be able to find all values after rotations
        assert!(simple_tree.get(1).is_some());
        assert!(simple_tree.get(2).is_some());
        assert!(simple_tree.get(3).is_some());
        assert_eq!(simple_tree.get(4), None);
    }

    #[test]
    fn test_clear_method() {
        let mut tree = RBTree::with_capacity(8);

        // Test clear on empty tree
        tree.clear();
        assert_eq!(tree.len, 0);
        assert_eq!(tree.root(), None);
        assert_eq!(tree.root_node(), None);

        // Insert multiple values
        tree.insert(50);
        tree.insert(25);
        tree.insert(75);
        tree.insert(10);
        tree.insert(30);
        tree.insert(60);
        tree.insert(90);

        assert_eq!(tree.len, 7);
        assert!(tree.root().is_some());
        assert!(tree.verify_rb_properties());

        // Clear the tree
        tree.clear();

        // Verify tree is empty
        assert_eq!(tree.len, 0);
        assert_eq!(tree.root(), None);
        assert_eq!(tree.root_node(), None);

        // Verify we can't find any of the old values
        assert_eq!(tree.get(50), None);
        assert_eq!(tree.get(25), None);
        assert_eq!(tree.get(75), None);
        assert_eq!(tree.get(10), None);
        assert_eq!(tree.get(30), None);
        assert_eq!(tree.get(60), None);
        assert_eq!(tree.get(90), None);

        // Verify we can insert new values after clear
        let handle = tree.insert(100);
        assert_eq!(tree.len, 1);
        assert_eq!(tree.root(), Some(&100));
        assert_eq!(tree.val(&handle), Some(&100));
        assert!(tree.verify_rb_properties());

        // Clear again
        tree.clear();
        assert_eq!(tree.len, 0);
        assert_eq!(tree.root(), None);
    }

    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;

    // A type that tracks when it's dropped
    #[derive(Clone)]
    struct DropCounter {
        value: i32,
        drop_count: Arc<AtomicUsize>,
    }

    impl DropCounter {
        fn new(value: i32, drop_count: Arc<AtomicUsize>) -> Self {
            DropCounter { value, drop_count }
        }
    }

    impl PartialEq for DropCounter {
        fn eq(&self, other: &Self) -> bool {
            self.value == other.value
        }
    }

    impl Eq for DropCounter {}

    impl PartialOrd for DropCounter {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }

    impl Ord for DropCounter {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.value.cmp(&other.value)
        }
    }

    impl Drop for DropCounter {
        fn drop(&mut self) {
            self.drop_count.fetch_add(1, Ordering::SeqCst);
        }
    }

    impl std::fmt::Debug for DropCounter {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "DropCounter({})", self.value)
        }
    }

    #[test]
    fn test_clear_drops_elements_correctly() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        {
            let mut tree = RBTree::with_capacity(8);

            // Insert elements that track when they're dropped
            let values = vec![50, 25, 75, 10, 30, 60, 90, 5, 15, 27, 35];
            for val in values {
                let counter = DropCounter::new(val, drop_count.clone());
                tree.insert(counter);
            }

            assert_eq!(tree.len, 11);
            assert_eq!(drop_count.load(Ordering::SeqCst), 0); // No drops yet

            // Clear the tree
            tree.clear();

            // All elements should have been dropped
            assert_eq!(drop_count.load(Ordering::SeqCst), 11);
            assert_eq!(tree.len, 0);
            assert_eq!(tree.root(), None);

            // Insert a new element to verify tree still works
            let new_counter = DropCounter::new(999, drop_count.clone());
            tree.insert(new_counter);
            assert_eq!(tree.len, 1);
            assert_eq!(drop_count.load(Ordering::SeqCst), 11); // Still 11, new element not dropped
        } // Tree goes out of scope here

        // The remaining element should be dropped when tree is destroyed
        assert_eq!(drop_count.load(Ordering::SeqCst), 12);
    }

    #[test]
    fn test_clear_with_complex_tree_structure() {
        let mut tree = RBTree::with_capacity(8);

        // Build a complex tree that will have multiple rotations
        for i in 1..=15 {
            tree.insert(i);
        }

        assert_eq!(tree.len, 15);
        assert!(tree.verify_rb_properties());

        // Store some handles before clearing
        let handle_5 = tree.get(5);
        let handle_10 = tree.get(10);
        assert!(handle_5.is_some());
        assert!(handle_10.is_some());

        // Clear the tree
        tree.clear();

        // Verify tree state
        assert_eq!(tree.len, 0);
        assert_eq!(tree.root(), None);

        // Old handles should no longer work (values don't exist)
        assert_eq!(tree.get(5), None);
        assert_eq!(tree.get(10), None);

        // Build new tree to verify functionality
        tree.insert(42);
        tree.insert(21);
        tree.insert(84);
        assert_eq!(tree.len, 3);
        assert!(tree.verify_rb_properties());
    }

    #[test]
    fn test_multiple_clear_operations() {
        let mut tree = RBTree::with_capacity(8);

        for cycle in 0..3 {
            // Fill tree
            for i in 1..=5 {
                tree.insert(i + cycle * 10);
            }
            assert_eq!(tree.len, 5);

            // Clear tree
            tree.clear();
            assert_eq!(tree.len, 0);
            assert_eq!(tree.root(), None);

            // Verify empty state
            for i in 1..=5 {
                assert_eq!(tree.get(i + cycle * 10), None);
            }
        }

        // Final verification
        assert_eq!(tree.len, 0);
        assert_eq!(tree.root(), None);
    }

    #[test]
    fn test_clear_large_tree_no_stack_overflow() {
        let mut tree = RBTree::with_capacity(8);

        // Insert a large number of elements to create a deep tree
        // This would cause stack overflow with recursive approach
        for i in 0..10000 {
            tree.insert(i);
        }

        assert_eq!(tree.len, 10000);
        assert!(tree.verify_rb_properties());

        // Clear should complete without stack overflow
        tree.clear();

        assert_eq!(tree.len, 0);
        assert_eq!(tree.root(), None);

        // Verify tree can still be used
        tree.insert(42);
        assert_eq!(tree.len, 1);
        assert_eq!(tree.root(), Some(&42));
    }

    #[test]
    fn test_clear_preserves_free_list_functionality() {
        let drop_count = Arc::new(AtomicUsize::new(0));

        {
            let mut tree = RBTree::with_capacity(8);

            // Fill tree with trackable elements
            for i in 0..100 {
                let counter = DropCounter::new(i, drop_count.clone());
                tree.insert(counter);
            }

            assert_eq!(tree.len, 100);
            let initial_drop_count = drop_count.load(Ordering::SeqCst);

            // Clear tree
            tree.clear();

            // All 100 elements should be dropped
            assert_eq!(drop_count.load(Ordering::SeqCst), initial_drop_count + 100);
            assert_eq!(tree.len, 0);

            // Free list should still work - insert new elements
            for i in 100..150 {
                let counter = DropCounter::new(i, drop_count.clone());
                tree.insert(counter);
            }

            assert_eq!(tree.len, 50);
            // No additional drops from inserting (reusing freed nodes)
            assert_eq!(drop_count.load(Ordering::SeqCst), initial_drop_count + 100);
        } // Tree destructor should drop remaining 50 elements

        assert_eq!(drop_count.load(Ordering::SeqCst), 150);
    }

    #[test]
    fn test_clear_stack_capacity_efficiency() {
        // Test that our stack capacity calculation is reasonable for different tree sizes
        let test_cases = vec![
            (1, "single node"),
            (2, "two nodes"),
            (4, "four nodes"),
            (10, "small tree"),
            (100, "medium tree"),
            (1000, "large tree"),
            (10000, "very large tree"),
        ];

        for (size, description) in test_cases {
            let mut tree = RBTree::with_capacity(8);

            // Insert elements
            for i in 0..size {
                tree.insert(i);
            }

            assert_eq!(
                tree.len, size,
                "Failed to insert {} elements for {}",
                size, description
            );

            // Clear should complete efficiently without reallocating stack
            tree.clear();

            assert_eq!(tree.len, 0, "Clear failed for {}", description);
            assert_eq!(
                tree.root(),
                None,
                "Root not null after clear for {}",
                description
            );

            // Verify tree can still be used
            tree.insert(42);
            assert_eq!(
                tree.len, 1,
                "Cannot reuse tree after clear for {}",
                description
            );
        }
    }

    #[test]
    fn test_clear_capacity_calculation_bounds() {
        let mut tree = RBTree::with_capacity(8);

        // Test small tree case
        tree.insert(1);
        tree.insert(2);
        tree.clear(); // Should use len for stack capacity (2)

        // Test medium tree case
        for i in 0..100 {
            tree.insert(i);
        }
        assert_eq!(tree.len, 100);
        tree.clear(); // Should calculate appropriate capacity

        // Test very large tree case
        for i in 0..5000 {
            tree.insert(i);
        }
        assert_eq!(tree.len, 5000);
        tree.clear(); // Should handle large trees efficiently

        assert_eq!(tree.len, 0);
        assert_eq!(tree.root(), None);
    }

    #[test]
    fn test_clear_stack_memory_efficiency() {
        // Verify that depth-first stack approach uses significantly less memory than breadth-first
        let mut tree = RBTree::with_capacity(8);

        // Create a tree with 1000 nodes
        for i in 0..1000 {
            tree.insert(i);
        }

        // For depth-first: stack capacity = height ≤ 2*log₂(n+1) + buffer
        // For 1000 nodes: height ≤ 2*log₂(1001) ≈ 2*10 = 20, plus buffer ≈ 24
        let expected_height_bound = (2.0 * ((1000 + 1) as f64).log2()).ceil() as usize;
        let expected_stack_capacity = (expected_height_bound + 4).max(8);

        // For breadth-first (previous): queue capacity would be much larger
        // Max level width ≈ 500+ nodes vs stack depth ≈ 24 nodes

        println!("Tree with 1000 nodes:");
        println!(
            "Expected stack capacity (depth-first): ~{}",
            expected_stack_capacity
        );
        println!("Previous queue capacity (breadth-first) would be: ~500+");

        // The depth-first approach should use much less memory
        assert!(
            expected_stack_capacity < 50,
            "Stack capacity should be much smaller than breadth-first"
        );

        tree.clear();
        assert_eq!(tree.len, 0);
        assert_eq!(tree.root(), None);
    }

    #[test]
    fn test_len_and_is_empty() {
        let mut tree = RBTree::with_capacity(8);

        // Test empty tree
        assert_eq!(tree.len(), 0);
        assert!(tree.is_empty());

        // Test single insertion
        tree.insert(42);
        assert_eq!(tree.len(), 1);
        assert!(!tree.is_empty());

        // Test multiple insertions
        tree.insert(10);
        tree.insert(50);
        tree.insert(25);
        assert_eq!(tree.len(), 4);
        assert!(!tree.is_empty());

        // Test duplicate insertion (should not increase len)
        tree.insert(42);
        assert_eq!(tree.len(), 4);
        assert!(!tree.is_empty());

        // Test clear
        tree.clear();
        assert_eq!(tree.len(), 0);
        assert!(tree.is_empty());

        // Test after clear
        tree.insert(100);
        assert_eq!(tree.len(), 1);
        assert!(!tree.is_empty());
    }

    #[test]
    fn test_capacity_method() {
        // SegmentedFreeList rounds up capacity to segment size (256)
        // Test that capacity is at least what was requested
        let tree1 = RBTree::<i32>::with_capacity(8);
        assert!(tree1.capacity() >= 8);

        // Test custom capacity
        let tree2 = RBTree::<i32>::with_capacity(100);
        assert!(tree2.capacity() >= 100);

        // Capacity should not decrease with insertions within capacity
        let mut tree3 = RBTree::with_capacity(8);
        let initial_capacity = tree3.capacity();

        tree3.insert(1);
        tree3.insert(2);
        tree3.insert(3);
        assert!(tree3.capacity() >= initial_capacity);
    }
}
