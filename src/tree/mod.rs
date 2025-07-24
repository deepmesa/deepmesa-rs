pub mod bstree;
//pub mod slfreelist;
pub mod treenode;

use crate::tree::treenode::TreeNode;

crate::fl::slfreelist::fl_struct!(SLFreeList, TreeNode);
crate::fl::slfreelist::fl_impl!(SLFreeList, TreeNode, right, val);
