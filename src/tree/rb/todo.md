# Red-Black Tree Traits TODO

## Currently Implemented Traits:
- `Debug` (in rbtree.rs:37)
- `Drop` (in traits.rs:3)

## Missing Traits That Would Be Beneficial:

### **Essential Collection Traits:**
1. **`Default`** - Create an empty tree
2. **`Clone`** - Deep copy of the entire tree
3. **`PartialEq`** - Compare two trees for equality
4. **`Eq`** - Marker trait for full equality

### **Iterator Traits:**
5. **`IntoIterator`** - Convert tree into an iterator (consuming)
6. **`IntoIterator for &RedBlackTree`** - Immutable iteration
7. **`IntoIterator for &mut RedBlackTree`** - Mutable iteration
8. **`FromIterator`** - Create tree from an iterator
9. **`Extend`** - Add items from an iterator to existing tree
10. **`Extend<&T>`** - Add items from iterator of references

### **Conversion Traits:**
11. **`From<Vec<T>>`** - Create tree from vector
12. **`From<[T; N]>`** - Create tree from array

### **Hash and Ordering (if T supports them):**
13. **`Hash`** - Hash the entire tree contents
14. **`PartialOrd`** - Compare trees by some ordering (lexicographic)
15. **`Ord`** - Total ordering for trees

### **Indexing (potentially useful):**
16. **`Index<usize>`** - Access nth element in sorted order
17. **`IndexMut<usize>`** - Mutable access to nth element

### **Thread Safety (if appropriate):**
18. **`Send`** - Safe to transfer between threads
19. **`Sync`** - Safe to share between threads

## Priority Implementation Order:

### **Tier 1 (Essential):**
- `Default` - Very common, easy to implement
- `Clone` - Important for copying trees
- `PartialEq`/`Eq` - Essential for comparisons
- `IntoIterator` (all variants) - Critical for Rust idioms

### **Tier 2 (Very Useful):**
- `FromIterator` - Enables `collect()` operations
- `Extend` - Enables extending from iterators
- `From<Vec<T>>` - Common conversion need

### **Tier 3 (Nice to Have):**
- `Hash`, `PartialOrd`, `Ord` - For using trees as keys/values
- `Index`/`IndexMut` - If nth element access is desired
- `Send`/`Sync` - For concurrent usage

## Implementation Notes:

The Red-Black Tree would benefit most from implementing the iterator traits since trees are naturally iterable in sorted order, and the standard collection traits like `Default`, `Clone`, and equality comparison.

For iterators, we should implement in-order traversal which leverages the BST property to yield elements in sorted order.

All implementations should go in `src/tree/rb/traits.rs` to keep the code organized.