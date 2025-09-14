use super::rbtree::RedBlackTree;

impl<T> Drop for RedBlackTree<T> {
    fn drop(&mut self) {
        self.clear();
    }
}