use super::rbtree::RedBlackTree;
use super::TreeNode;
use crate::fl::FreeList;

impl<T, FL: FreeList<TreeNode<T>>> Drop for RedBlackTree<T, FL> {
    fn drop(&mut self) {
        self.clear();
    }
}