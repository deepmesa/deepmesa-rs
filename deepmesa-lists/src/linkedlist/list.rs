/*
   Fast Linked List: A fast and flexible doubly linked list that
   allows for O(1) inserts and removes from the middle of the
   list. This list preallocates memory and doesn't have to allocate
   and deallocate memory on every insert / remove operation

   Copyright 2021 "Rahul Singh <rsingh@arrsingh.com>"

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

use crate::linkedlist::{fl, iter::Iter, iter::IterMut, node::InternalNode, node::Node};
use std::ptr;

macro_rules! nid_inc {
    ($nid: expr) => {{
        let nid = $nid;
        $nid += 1;
        nid
    }};
}

/// A doubly linked list that owns the nodes and can pre-allocate
/// memory for performance. This linked list allows pushing and
/// popping elements at either end or in the middle in constant time.
///
/// The API is the same as [`std::collections::LinkedList`] however
/// this list also allows pushing and popping elements from the middle
/// of the list in constant time.
///
/// This list also vends handles to its nodes that can be used to
/// mutate the list in constant time.
///
/// # Getting Started

/// To get started add the deepmesa dependency to Cargo.toml and the
/// use declaration in your source.
///
/// ```text
/// [dependencies]
/// deepmesa = "0.1.0"
/// ```
///
/// ```
/// use deepmesa::lists::FastLinkedList;
///
/// let mut list = FastLinkedList::<u8>::with_capacity(10);
/// for i in 0..10 {
///     list.push_front(i);
/// }
///
/// for e in list.iter() {
///     println!("{}", e);
/// }
/// ```
/// # Memory Management

/// This list manages memory via an internal freelist of nodes. When a
/// new element is added to the list, a preallocated node is acquired
/// from the freelist. When an element is removed from the list, the
/// node is returned to the freelist. This ensures that memory is not
/// allocated and deallocated on every push and pop which makes the
/// list fast.
///
/// All memory for the list is allocated on the heap using the default
/// allocator. Additional memory is allocated by the freelist when a
/// new elememt is added to the list and the capacity is filled.
///
/// When the list is dropped, all memory is deallocated and any
/// elements stored in the list are dropped. If the [`Drop`] trait on
/// an element panics the list will deallocate all allocated memory
/// because elements are removed from the list and dropped only after
/// all memory is deallocated.

/// # Capacity & Reallocation

/// The capacity of the list is the number of elements it can hold
/// before allocating new memory. The length of the list is the number
/// of elements it holds. When the length equals the capacity, and a
/// new element is added to the list, the list will allocate
/// additional memory.
///
/// The amount of memory allocated when the capacity is exhausted
/// depends on how the list is constructed. If the list is constructed
/// using [`new()`](#method.new) or
/// [`with_capacity()`](#method.with_capacity) with a non-zero capacity
/// then the capacity is doubled on every allocation.
///
/// If the list is constructed using
/// [`with_capacity()`](#method.with_capacity) with a capacity of
/// zero, then the list will not preallocate any memory on
/// construction. In this case, when a new element is added to the
/// list, additional memory will be allocated for the new elememt
/// unless the freelist has available memory from previous remove
/// operations.
/// ### Example
/// ```
/// use deepmesa::lists::FastLinkedList;
/// // create a list with capacity 0
/// let mut list = FastLinkedList::<u8>::with_capacity(0);
/// assert_eq!(list.len(), 0);
/// assert_eq!(list.capacity(), 0);
/// // Pushing elements will cause an allocation every time
/// for i in 0..10 {
///     assert_eq!(list.len(), i);
///     assert_eq!(list.capacity(), i);
///     list.push_head(1);
/// }
///
/// // Removing an element will not cause a deallocation
/// list.pop_head();
/// assert_eq!(list.len(), 9);
/// assert_eq!(list.capacity(), 10);
///
/// // Now that capacity exceeds the length of the list no memory will
/// // be allocated unless existing capacity is exhausted
/// list.push_head(1);
/// assert_eq!(list.len(), 10);
/// assert_eq!(list.capacity(), 10);
/// // any further additions to the list will again allocate new
/// // memory for each element added.
/// list.push_head(1);
/// assert_eq!(list.len(), 11);
/// assert_eq!(list.capacity(), 11);
/// ```
/// It is recommended to use
/// [`with_capacity()`](#method.with_capacity)
/// whenever possible and specify how big the list is expected to get.
/// # Handles
/// The [`push_head()`](#method.push_head),
/// [`push_tail()`](#method.push_tail),
/// [`push_next()`](#method.push_next) and
/// [`push_prev()`](#method.push_prev) methods return handles to the
/// nodes pushed to the linked list. The handles are implemented as
/// structs of type [`Node<T>`] that wrap a raw pointer to
/// node. However since [`Node<T>`] does not implement the [`Deref`]
/// trait, these raw pointers cannot be dereferenced directly. Handles
/// can only be used by passing them as arguments to the
/// [`next()`](#method.next), [`next_mut()`](#method.next_mut),
/// [`prev()`](#method.prev), [`prev_mut()`](#method.prev_mut),
/// [`prev_node()`](#method.prev_node),
/// [`next_node()`](#method.next_node),[`node()`](#method.node),[`node_mut()`](#method.node_mut),
/// [`has_next()`](#method.has_next),
/// [`has_prev()`](#method.has_prev),
/// [`pop_next()`](#method.pop_next),
/// [`pop_prev()`](#method.pop_prev),
/// [`pop_node()`](#method.pop_node),
/// [`push_next()`](#method.push_next),
/// [`push_prev()`](#method.push_prev), methods of the list. This
/// allows adding, removing and mutating elements in the middle of the
/// list in O(1) time.
///
/// Handles can be copied, cloned and passed around by value or
/// reference without regard to the lifetime of the list. When an
/// element is removed from the list, the handle associated with that
/// node becomes invalid forever. Passing an invalid handle to the
/// list is safe since all methods that accept a reference to a handle
/// return None if the handle is invalid.
///
/// ### Example
/// ```
/// use deepmesa::lists::FastLinkedList;
/// let mut list = FastLinkedList::<u8>::with_capacity(10);
/// list.push_head(1);
/// let middle = list.push_head(100);
/// list.push_head(2);
///
/// // get the value of the node in the middle of the list in O(1)
/// // time.
/// assert_eq!(list.node(&middle), Some(&100));
/// // remove the middle node in O(1) time
/// list.pop_node(&middle);
/// // once the middle node is removed, the handle is invalid
/// assert_eq!(list.node(&middle), None);
/// assert_eq!(list.len(), 2);
/// ```
///
/// [`Node<T>`] implements the [`Default`] trait so you can store
/// default (invalid) handles in a struct and assign them later.
/// ### Example
/// ```
/// use deepmesa::lists::FastLinkedList;
/// use deepmesa::lists::linkedlist::Node;
///
/// struct MyStruct<T> {
///    handle: Node<T>
/// };
///
/// let mut s = MyStruct::<u8>{
///     handle: Node::<u8>::default()
/// };
///
/// let mut list = FastLinkedList::<u8>::with_capacity(10);
/// // The default handle is invalid
/// assert_eq!(list.node(&s.handle), None);
/// // push a new element and store the handle
/// s.handle = list.push_head(1);
/// assert_eq!(list.node(&s.handle), Some(&1));
/// ```
/// # Iterators

/// The list supports iterators that can traverse the list in either
/// direction by reversing the iterator at any time.
/// ### Examples
/// ```
/// use deepmesa::lists::FastLinkedList;
/// let mut list = FastLinkedList::<u8>::with_capacity(10);
/// for i in 0..10 {
///     list.push_head(i);
/// }
///
/// let mut iter = list.iter();
/// assert_eq!(iter.next(), Some(&9));
/// assert_eq!(iter.next(), Some(&8));
/// assert_eq!(iter.next(), Some(&7));
/// // now reverse the iterator
/// iter = iter.reverse();
/// assert_eq!(iter.next(), Some(&8));
/// assert_eq!(iter.next(), Some(&9));
/// assert_eq!(iter.next(), None);
/// ```

#[derive(Debug)]
pub struct FastLinkedList<T> {
    cid: usize,
    nid: usize,
    pub(super) head: *mut InternalNode<T>,
    pub(super) tail: *mut InternalNode<T>,
    len: usize,
    fl: fl::FreeList<T>,
}

impl<T> Drop for FastLinkedList<T> {
    fn drop(&mut self) {
        let mut cur: *mut InternalNode<T> = self.head;
        let mut node_vec = Vec::with_capacity(self.len());
        while !cur.is_null() {
            let node = self.pop_ptr(cur);
            node_vec.push(node);
            cur = self.head;
        }
    }
}

impl<'a, T> IntoIterator for &'a FastLinkedList<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut FastLinkedList<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

static mut LL_COUNTER: usize = 0;

impl<T> FastLinkedList<T> {
    /// Creates an empty linked list with a
    /// default capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let list = FastLinkedList::<u8>::new();
    /// ```
    pub fn new() -> FastLinkedList<T> {
        unsafe {
            LL_COUNTER += 1;

            FastLinkedList {
                cid: LL_COUNTER,
                nid: 0,
                len: 0,
                head: ptr::null_mut(),
                tail: ptr::null_mut(),
                fl: fl::FreeList::new(8),
            }
        }
    }

    /// Creates an empty linked list with the specified capacity. The
    /// list will continue to reallocate additional memory by doubling
    /// the capacity everytime the capacity is exceeded.
    ///
    /// However the list will not deallocate memory when elements are
    /// removed.
    ///
    /// If the capacity is set to 0, and the list is full, then new
    /// memory will be allocated for one new element everytime an
    /// element is added to the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// for i in 0..10 {
    ///     // All these are pushed without any allocations
    ///     list.push_front(i);
    /// }
    ///
    /// assert_eq!(list.len(), 10);
    /// assert_eq!(list.capacity(), 10);
    ///
    /// // This will result in an allocation and the capacity will be doubled
    /// list.push_front(1);
    /// assert_eq!(list.len(), 11);
    /// assert_eq!(list.capacity(), 20);
    ///
    /// // A list with a capacity of 0 will allocate on every push
    /// let mut list = FastLinkedList::<u8>::with_capacity(0);
    /// list.push_front(1);
    /// assert_eq!(list.len(), 1);
    /// assert_eq!(list.capacity(), 1);
    ///
    /// list.push_front(1);
    /// assert_eq!(list.len(), 2);
    /// assert_eq!(list.capacity(), 2);
    /// ```
    pub fn with_capacity(capacity: usize) -> FastLinkedList<T> {
        unsafe {
            LL_COUNTER += 1;

            FastLinkedList {
                cid: LL_COUNTER,
                nid: 0,
                len: 0,
                head: ptr::null_mut(),
                tail: ptr::null_mut(),
                fl: fl::FreeList::new(capacity),
            }
        }
    }

    /// Returns a bidirectional iterator over the list
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::new();
    /// list.push_front(1);
    /// list.push_front(2);
    /// list.push_front(3);
    /// list.push_front(4);
    /// list.push_front(5);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&5));
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), Some(&3));
    /// iter = iter.reverse();
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), Some(&5));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter::new(self)
    }

    /// Returns a bidirectional iterator over the list with mutable
    /// references that allows the value to be modified
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::new();
    /// list.push_front(1);
    /// list.push_front(2);
    /// list.push_front(3);
    ///
    /// for e in list.iter_mut() {
    ///     *e += 100;
    /// }
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&103));
    /// assert_eq!(iter.next(), Some(&102));
    /// assert_eq!(iter.next(), Some(&101));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut::new(self)
    }

    /// Removes and drops all the elements from this list. This has no
    /// effect on the allocated capacity of the list. This method
    /// should complete in *O*(*n*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// list.push_front(1);
    /// list.push_front(2);
    /// list.push_front(3);
    ///
    /// assert_eq!(list.len(), 3);
    /// assert_eq!(list.capacity(), 10);
    ///
    /// list.clear();
    /// assert_eq!(list.len(), 0);
    /// assert_eq!(list.capacity(), 10);
    /// ```
    pub fn clear(&mut self) {
        let mut cur: *mut InternalNode<T> = self.head;
        while !cur.is_null() {
            let node = self.pop_ptr(cur);
            drop(node);
            cur = self.head;
        }
    }

    /// Returns a reference to the front (head) of the list or `None`
    /// if the list is empty. This method should complete in *O*(*1*)
    /// time.
    ///
    /// This method simply calls [`self.head()`](#method.head)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.front(), None);
    ///
    /// list.push_front(1);
    /// assert_eq!(list.front(), Some(&1));
    /// ```
    pub fn front(&self) -> Option<&T> {
        self.head()
    }

    /// Returns a reference to the back (tail) of the list or `None`
    /// if the list is empty. This method should complete in *O*(*1*)
    /// time.
    ///
    /// This method simply calls [`self.tail()`](#method.tail)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.back(), None);
    ///
    /// list.push_back(1);
    /// assert_eq!(list.back(), Some(&1));
    /// ```
    pub fn back(&self) -> Option<&T> {
        self.tail()
    }

    /// Returns a mutable reference to the front (head) of the list or `None`
    /// if the list is empty. This method should complete in *O*(*1*)
    /// time.
    ///
    /// This method simply calls [`self.head_mut()`](#method.head_mut)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.front(), None);
    ///
    /// list.push_front(1);
    /// assert_eq!(list.front(), Some(&1));
    /// match list.front_mut() {
    ///     None => {},
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(list.front(), Some(&5));
    /// ```
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.head_mut()
    }

    /// Returns a mutable reference to the back (tail) of the list or `None`
    /// if the list is empty. This method should complete in *O*(*1*)
    /// time.
    ///
    /// This method simply calls [`self.tail_mut()`](#method.tail_mut)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.back(), None);
    ///
    /// list.push_back(1);
    /// assert_eq!(list.back(), Some(&1));
    /// match list.back_mut() {
    ///     None => {},
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(list.back(), Some(&5));
    /// ```
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.tail_mut()
    }

    /// Returns a reference to the back (tail) of the list or `None`
    /// if the list is empty. This method should complete in *O*(*1*)
    /// time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.tail(), None);
    ///
    /// list.push_tail(1);
    /// assert_eq!(list.tail(), Some(&1));
    /// ```
    pub fn tail(&self) -> Option<&T> {
        if self.head.is_null() {
            return None;
        }

        unsafe { Some(&(*self.tail).val) }
    }

    /// Returns a mutable reference to the back (tail) of the list or `None`
    /// if the list is empty. This method should complete in *O*(*1*)
    /// time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.tail(), None);
    ///
    /// list.push_tail(1);
    /// assert_eq!(list.tail(), Some(&1));
    /// match list.tail_mut() {
    ///     None => {},
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(list.tail(), Some(&5));
    /// ```
    pub fn tail_mut(&mut self) -> Option<&mut T> {
        if self.tail.is_null() {
            return None;
        }
        unsafe { Some(&mut (*self.tail).val) }
    }

    /// Returns a reference to the front (head) of the list or `None`
    /// if the list is empty. This method should complete in *O*(*1*)
    /// time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.head(), None);
    ///
    /// list.push_head(1);
    /// assert_eq!(list.head(), Some(&1));
    /// ```
    pub fn head(&self) -> Option<&T> {
        if self.head.is_null() {
            return None;
        }

        unsafe { Some(&(*self.head).val) }
    }

    /// Returns a mutable reference to the front (head) of the list or `None`
    /// if the list is empty. This method should complete in *O*(*1*)
    /// time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.head(), None);
    ///
    /// list.push_head(1);
    /// assert_eq!(list.head(), Some(&1));
    /// match list.head_mut() {
    ///     None => {},
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(list.head(), Some(&5));
    /// ```
    pub fn head_mut(&mut self) -> Option<&mut T> {
        if self.head.is_null() {
            return None;
        }

        unsafe { Some(&mut (*self.head).val) }
    }

    /// Returns a valid raw pointer to the specified Handle or None if
    /// the handle is invalid.  This method checks the container Id
    /// (cid) of the handle against the list itself so that handles
    /// cannot be used across lists. If the container Id matches then
    /// the node Id is checked against the node Id stored at that
    /// memory locatiom. If the container Id and the Node Id are a
    /// match then a flag indicating whether this node is part of the
    /// freelist is checked.

    /// If the container Id and the node Id match and the node is not
    /// part of the free list then the raw pointer to the Node is
    /// returned. If the conditions don't return true this method
    /// returns None indicating that the raw pointer does not point to
    /// the node that the handle originally referred to.
    ///
    /// It should be noted that the raw pointer returned will always
    /// point to a valid memory location since that memory is
    /// allocated and managed by the freelist. However the contents of
    /// that memory location can change as nodes are pushed and popped
    /// off the list. When the contents change the handle becomes
    /// invalid and this method returns None.
    fn node_ptr(&self, node: &Node<T>) -> Option<*mut InternalNode<T>> {
        if node.cid != self.cid {
            return None;
        }
        unsafe {
            if (*node.ptr).nid != node.nid {
                return None;
            }
            if (*node.ptr).fl_node {
                return None;
            }
        }

        Some((*node).ptr)
    }

    /// Returns a reference to the value of the node immediately after
    /// the node associated with the specified handle. If the
    /// specified handle is invalid or there is no next node, this
    /// method returns None. This method should complete in *O*(*1*)
    /// time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// list.push_head(1);
    /// let node = list.push_head(2);
    ///
    /// assert_eq!(list.next(&node), Some(&1));
    ///
    /// list.pop_tail();
    /// // once the tail is popped, there is no next
    /// assert_eq!(list.next(&node), None);
    /// ```
    pub fn next(&self, node: &Node<T>) -> Option<&T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).next.is_null() {
                    return None;
                }

                Some(&(*(*n_ptr).next).val)
            },
        }
    }

    /// Returns a mutable reference to the value of the node
    /// immediately after the node associated with the specified
    /// handle. If the specified handle is invalid or if there is no
    /// next node, this method returns None. This method should
    /// complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// list.push_head(1);
    /// let node = list.push_head(2);
    /// assert_eq!(list.next(&node), Some(&1));
    ///
    /// match list.next_mut(&node) {
    ///     None => {},
    ///     Some(x) => *x = 100,
    /// }
    ///
    /// assert_eq!(list.next(&node), Some(&100));
    /// ```
    pub fn next_mut(&mut self, node: &Node<T>) -> Option<&mut T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).next.is_null() {
                    return None;
                }

                Some(&mut (*(*n_ptr).next).val)
            },
        }
    }

    /// Returns a reference to the value of the node immediately
    /// preceeding the node associated with the specified handle.  If
    /// the specified handle is invalid or if there is no preceeding
    /// node, this method returns None. This method should
    /// complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    /// list.push_head(2);
    ///
    /// assert_eq!(list.prev(&node), Some(&2));
    ///
    /// list.pop_head();
    /// // once the head is popped, there is no prev
    /// assert_eq!(list.prev(&node), None);
    /// ```
    pub fn prev(&self, node: &Node<T>) -> Option<&T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).prev.is_null() {
                    return None;
                }

                Some(&(*(*n_ptr).prev).val)
            },
        }
    }

    /// Returns a mutable reference to the value of the node
    /// immediately preceeding the node associated with the specified
    /// handle. If the specified handle is invalid or there is no
    /// preceeding node, this method returns None. This method should
    /// complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    /// list.push_head(2);
    /// assert_eq!(list.prev(&node), Some(&2));
    ///
    /// match list.prev_mut(&node) {
    ///     None => {},
    ///     Some(x) => *x = 100,
    /// }
    ///
    /// assert_eq!(list.prev(&node), Some(&100));
    /// ```
    pub fn prev_mut(&mut self, node: &Node<T>) -> Option<&mut T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).prev.is_null() {
                    return None;
                }

                Some(&mut (*(*n_ptr).prev).val)
            },
        }
    }

    /// Returns a handle to the node immediately preceeding the node
    /// associated with the specified handle. If the specified handle
    /// is invalid or if there is no preceeding node, this method
    /// returns None. This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    /// list.push_head(2);
    ///
    /// assert_eq!(list.prev(&node), Some(&2));
    ///
    /// list.pop_head();
    /// //once the head is popped there is no prev node
    /// assert_eq!(list.prev(&node), None);
    /// ```
    pub fn prev_node(&self, node: &Node<T>) -> Option<Node<T>> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).prev.is_null() {
                    return None;
                }

                Some(Node::new(self.cid, (*(*n_ptr).prev).nid, (*n_ptr).prev))
            },
        }
    }

    /// Returns a handle to the node immediately preceeding the node
    /// associated with the specified handle. If the handle is invalid
    /// or if there is no preceeding node, this method returns
    /// None. This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// list.push_head(1);
    /// let node = list.push_head(2);
    ///
    /// match list.next_node(&node) {
    ///     None => {},
    ///     Some(n) => assert_eq!(list.node(&n), Some(&1)),
    /// }
    ///
    /// list.pop_tail();
    /// // Once the tail node is popped, there is no next node
    /// assert_eq!(list.next_node(&node), None);
    /// ```
    pub fn next_node(&self, node: &Node<T>) -> Option<Node<T>> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).next.is_null() {
                    return None;
                }

                Some(Node::new(self.cid, (*(*n_ptr).next).nid, (*n_ptr).next))
            },
        }
    }

    /// Returns a reference to the value of the node associated with
    /// the specified handle.  If the specified handle is invalid this
    /// method returns None. This method should complete in *O*(*1*)
    /// time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    ///
    /// assert_eq!(list.node(&node), Some(&1));
    ///
    /// list.pop_head();
    /// // once the node is popped the handle becomes invalid
    /// assert_eq!(list.node(&node), None);
    /// ```
    pub fn node(&self, node: &Node<T>) -> Option<&T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe { Some(&(*n_ptr).val) },
        }
    }

    /// Returns a mutable reference to the value of the node associated with
    /// the specified handle.  If the specified handle is invalid this
    /// method returns None. This method should complete in *O*(*1*)
    /// time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    ///
    /// assert_eq!(list.node(&node), Some(&1));
    ///
    /// match list.node_mut(&node) {
    ///     None => {},
    ///     Some(x) => *x = 100,
    /// }
    ///
    /// assert_eq!(list.node(&node), Some(&100));
    /// ```
    pub fn node_mut(&mut self, node: &Node<T>) -> Option<&mut T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe { Some(&mut (*n_ptr).val) },
        }
    }

    /// Returns a handle to the head (front) of the list or None if
    /// the list is empty. This method should complete in *O*(*1*)
    /// time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    ///
    /// match list.head_node() {
    ///     None => {},
    ///     Some(x) => assert_eq!(list.node(&x), Some(&1)),
    /// }
    ///
    /// list.pop_head();
    /// assert_eq!(list.head_node(), None);
    /// ```
    pub fn head_node(&self) -> Option<Node<T>> {
        if self.head.is_null() {
            return None;
        }

        unsafe { Some(Node::new(self.cid, (*self.head).nid, self.head)) }
    }

    /// Returns a handle to the tail (back) of the list or None if the
    /// list is empty. This method should complete in *O*(*1*)
    /// time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node = list.push_tail(1);
    ///
    /// match list.tail_node() {
    ///     None => {},
    ///     Some(x) => assert_eq!(list.node(&x), Some(&1)),
    /// }
    ///
    /// list.pop_tail();
    /// assert_eq!(list.tail_node(), None);
    /// ```
    pub fn tail_node(&self) -> Option<Node<T>> {
        if self.tail.is_null() {
            return None;
        }
        unsafe { Some(Node::new(self.cid, (*self.tail).nid, self.tail)) }
    }

    /// Returns true if the node associated with the specified handle
    /// has a next node and false if it does not. If the specified
    /// handle is invalid this method returns None. This method should
    /// complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node1 = list.push_head(1);
    /// let node2 = list.push_head(2);
    ///
    /// assert_eq!(list.has_next(&node1), Some(false));
    /// assert_eq!(list.has_next(&node2), Some(true));
    ///
    /// list.pop_head();
    /// assert_eq!(list.has_next(&node1), Some(false));
    /// // once the head is popped node2 becomes an invalid handle
    /// assert_eq!(list.has_next(&node2), None);
    /// ```
    pub fn has_next(&self, node: &Node<T>) -> Option<bool> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).next.is_null() {
                    Some(false)
                } else {
                    Some(true)
                }
            },
        }
    }

    /// Returns true if the node associated with the specified handle
    /// has a previous node and false if it does not. If the specified
    /// handle is invalid this method returns None. This method should
    /// complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node1 = list.push_head(1);
    /// let node2 = list.push_head(2);
    ///
    /// assert_eq!(list.has_prev(&node1), Some(true));
    /// assert_eq!(list.has_prev(&node2), Some(false));
    ///
    /// list.pop_head();
    /// assert_eq!(list.has_prev(&node1), Some(false));
    /// // once the head is popped node2 becomes an invalid handle
    /// assert_eq!(list.has_next(&node2), None);
    /// ```
    pub fn has_prev(&self, node: &Node<T>) -> Option<bool> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).prev.is_null() {
                    Some(false)
                } else {
                    Some(true)
                }
            },
        }
    }

    /// Returns true if the list is empty. This method should
    /// complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.is_empty(), true);
    ///
    /// list.push_head(1);
    /// assert_eq!(list.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns true if the list has a head node and false if the list
    /// is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.has_head(), false);
    /// list.push_head(1);
    /// assert_eq!(list.has_head(), true);
    /// list.pop_head();
    /// assert_eq!(list.has_head(), false);
    /// ```
    pub fn has_head(&self) -> bool {
        !self.head.is_null()
    }

    /// Returns true if the list has a tail node and false if the list
    /// is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.has_tail(), false);
    /// list.push_tail(1);
    /// assert_eq!(list.has_tail(), true);
    /// list.pop_tail();
    /// assert_eq!(list.has_tail(), false);
    /// ```
    pub fn has_tail(&self) -> bool {
        !self.tail.is_null()
    }

    /// Returns the number of elements the list can hold without
    /// before new memory is allocated.
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.len() + self.fl.len()
    }

    /// Returns the number of elements in the list
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.len(), 0);
    ///
    /// list.push_head(1);
    /// assert_eq!(list.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Adds an element to the front (head) of the list. This
    /// operation should complete in O(1) time.
    ///
    /// This method simply calls
    /// [`self.push_head()`](#method.push_head)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// list.push_front(1);
    /// assert_eq!(list.front(), Some(&1));
    ///
    /// list.push_front(2);
    /// assert_eq!(list.front(), Some(&2));
    /// ```
    pub fn push_front(&mut self, elem: T) {
        self.push_head(elem);
    }

    /// Adds an element to the back (tail) of the list. This
    /// operation should complete in O(1) time.
    ///
    /// This method simply calls
    /// [`self.push_tail()`](#method.push_tail)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// list.push_back(1);
    /// assert_eq!(list.back(), Some(&1));
    ///
    /// list.push_back(2);
    /// assert_eq!(list.back(), Some(&2));
    /// ```
    pub fn push_back(&mut self, elem: T) {
        self.push_tail(elem);
    }

    /// Removes and returns the node pointed to by the specified raw pointer. This
    /// method will panic if the specified pointer is null.
    /// The memory is returned to the free list.
    fn pop_ptr(&mut self, ptr: *mut InternalNode<T>) -> T {
        if ptr.is_null() {
            panic!("cannot pop null pointer");
        }

        unsafe {
            if !(*ptr).next.is_null() {
                (*(*ptr).next).prev = (*ptr).prev;
            }

            if !(*ptr).prev.is_null() {
                (*(*ptr).prev).next = (*ptr).next;
            }

            if self.head == ptr {
                self.head = (*ptr).next;
            }

            if self.tail == ptr {
                self.tail = (*ptr).prev;
            }
            self.len -= 1;
            self.fl.release(ptr)
        }
    }

    /// Removes and returns the value at the head (front) of the
    /// list or None if the list is empty. This operation should
    /// complete in O(1) time
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.pop_head(), None);
    ///
    /// list.push_head(1);
    /// list.push_head(2);
    /// assert_eq!(list.pop_head(), Some(2));
    /// assert_eq!(list.pop_head(), Some(1));
    /// assert_eq!(list.pop_head(), None);
    /// ```
    pub fn pop_head(&mut self) -> Option<T> {
        if self.head.is_null() {
            return None;
        }
        Some(self.pop_ptr(self.head))
    }

    /// Removes and returns the value at the tail (back) of the
    /// list or None if the list is empty. This operation should
    /// complete in O(1) time
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.pop_tail(), None);
    ///
    /// list.push_tail(1);
    /// list.push_tail(2);
    /// assert_eq!(list.pop_tail(), Some(2));
    /// assert_eq!(list.pop_tail(), Some(1));
    /// assert_eq!(list.pop_tail(), None);
    /// ```
    pub fn pop_tail(&mut self) -> Option<T> {
        if self.tail.is_null() {
            return None;
        }

        Some(self.pop_ptr(self.tail))
    }

    /// Removes and returns the value at the front (head) of the list
    /// or None if the list is empty. This operation should complete
    /// in O(1) time.
    ///
    /// This method simply calls [`self.pop_head()`](#method.pop_head)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.pop_front(), None);
    ///
    /// list.push_front(1);
    /// list.push_front(2);
    /// assert_eq!(list.pop_front(), Some(2));
    /// assert_eq!(list.pop_front(), Some(1));
    /// assert_eq!(list.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        self.pop_head()
    }

    /// Removes and returns the value at the back (tail) of the list
    /// or None if the list is empty. This operation should complete
    /// in O(1) time
    ///
    /// This method simply calls [`self.pop_tail()`](#method.pop_tail)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// assert_eq!(list.pop_back(), None);
    ///
    /// list.push_back(1);
    /// list.push_back(2);
    /// assert_eq!(list.pop_back(), Some(2));
    /// assert_eq!(list.pop_back(), Some(1));
    /// assert_eq!(list.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        self.pop_tail()
    }

    /// Removes and returns the value of the node immediately after
    /// the node associated with the specified handle. If the
    /// specified handle is invalid or there is no next node, then
    /// this method returns None.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    ///
    /// list.push_head(1);
    /// list.push_head(2);
    /// let node = list.push_head(3);
    /// assert_eq!(list.pop_next(&node), Some(2));
    /// assert_eq!(list.pop_next(&node), Some(1));
    /// assert_eq!(list.pop_next(&node), None);
    /// ```
    pub fn pop_next(&mut self, node: &Node<T>) -> Option<T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).next.is_null() {
                    return None;
                }
                Some(self.pop_ptr((*n_ptr).next))
            },
        }
    }

    /// Removes and returns the value of the node immediately
    /// preceeding the node associated with the specified handle. If
    /// the specified handle is invalid or there is no previous node,
    /// then this method returns None.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    ///
    /// let node = list.push_head(1);
    /// list.push_head(2);
    /// list.push_head(3);
    /// assert_eq!(list.pop_prev(&node), Some(2));
    /// assert_eq!(list.pop_prev(&node), Some(3));
    /// assert_eq!(list.pop_prev(&node), None);
    /// ```
    pub fn pop_prev(&mut self, node: &Node<T>) -> Option<T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => unsafe {
                if (*n_ptr).prev.is_null() {
                    return None;
                }

                Some(self.pop_ptr((*n_ptr).prev))
            },
        }
    }

    /// Removes and returns the value of the node associated with the
    /// specified handle. If the specified handle is invalid then this
    /// method returns None.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    ///
    /// let node = list.push_head(1);
    /// assert_eq!(list.pop_node(&node), Some(1));
    /// assert_eq!(list.pop_node(&node), None);
    /// ```
    pub fn pop_node(&mut self, node: &Node<T>) -> Option<T> {
        match self.node_ptr(node) {
            None => None,
            Some(n_ptr) => Some(self.pop_ptr(n_ptr)),
        }
    }

    /// Adds an element to the head (front) of the list and returns a
    /// handle to it. This operation should complete in O(1) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    /// assert_eq!(list.node(&node), Some(&1));
    /// ```
    pub fn push_head(&mut self, elem: T) -> Node<T> {
        let nid = nid_inc!(self.nid);
        let raw_n = self.fl.acquire(elem, nid);

        unsafe {
            if self.head.is_null() {
                (*raw_n).next = ptr::null_mut();
            } else {
                (*self.head).prev = raw_n;
                (*raw_n).next = self.head;
            }

            if self.tail.is_null() {
                self.tail = raw_n;
            }
            self.head = raw_n;
        }

        self.len += 1;
        Node::new(self.cid, nid, raw_n)
    }

    /// Adds an element to the tail (back) of the list and returns a
    /// handle to it. This operation should complete in O(1) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// let node = list.push_tail(1);
    /// assert_eq!(list.node(&node), Some(&1));
    /// ```
    pub fn push_tail(&mut self, elem: T) -> Node<T> {
        let nid = nid_inc!(self.nid);
        let raw_n = self.fl.acquire(elem, nid);

        unsafe {
            if self.tail.is_null() {
                (*raw_n).prev = ptr::null_mut();
            } else {
                (*self.tail).next = raw_n;
                (*raw_n).prev = self.tail;
            }
            if self.head.is_null() {
                self.head = raw_n;
            }
            self.tail = raw_n;
        }
        self.len += 1;
        Node::new(self.cid, nid, raw_n)
    }

    /// Returns `true` if the `LinkedList` contains an element equal to the
    /// given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    ///
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    ///
    /// assert_eq!(list.contains(&0), true);
    /// assert_eq!(list.contains(&10), false);
    /// ```
    pub fn contains(&self, x: &T) -> bool
    where
        T: PartialEq<T>,
    {
        self.iter().any(|e| e == x)
    }

    /// Adds an element immediately after the node associated with the
    /// specified handle. Returns the handle to the node thats been
    /// added or None if the specified handle is invalid. This
    /// operation should complete in O(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    ///
    /// list.push_head(0);
    /// let middle = list.push_head(1);
    /// list.push_head(2);
    /// list.push_next(&middle, 100);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&100));
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn push_next(&mut self, node: &Node<T>, elem: T) -> Option<Node<T>> {
        match self.node_ptr(node) {
            None => None,
            Some(c_ptr) => unsafe {
                let nid = nid_inc!(self.nid);
                let raw_n = self.fl.acquire(elem, nid);

                if !(*c_ptr).next.is_null() {
                    (*(*c_ptr).next).prev = raw_n;
                    (*raw_n).next = (*c_ptr).next;
                }

                (*c_ptr).next = raw_n;
                (*raw_n).prev = c_ptr;

                if self.tail == c_ptr {
                    self.tail = raw_n;
                }

                self.len += 1;
                Some(Node::new(self.cid, nid, raw_n))
            },
        }
    }

    /// Adds an element immediately preceedeing the node associated with the
    /// specified handle. Returns the handle to the node thats been
    /// added or None if the specified handle is invalid. This
    /// operation should complete in O(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    ///
    /// list.push_head(0);
    /// let middle = list.push_head(1);
    /// list.push_head(2);
    /// list.push_prev(&middle, 100);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&100));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn push_prev(&mut self, node: &Node<T>, elem: T) -> Option<Node<T>> {
        match self.node_ptr(node) {
            None => None,
            Some(c_ptr) => unsafe {
                let nid = nid_inc!(self.nid);
                let raw_n = self.fl.acquire(elem, nid);

                if !(*c_ptr).prev.is_null() {
                    (*(*c_ptr).prev).next = raw_n;
                    (*raw_n).prev = (*c_ptr).prev;
                }

                (*c_ptr).prev = raw_n;
                (*raw_n).next = c_ptr;

                if self.head == c_ptr {
                    self.head = raw_n;
                }

                self.len += 1;
                Some(Node::new(self.cid, nid, raw_n))
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const FIRST: u8 = 0;
    const LAST: u8 = 1;
    const ONLY: u8 = 2;
    const MIDDLE: u8 = 3;

    macro_rules! assert_is_head {
        ($ll:ident, $node:ident) => {
            match $ll.node_ptr(&$node) {
                None => panic!("Node: {:?} not found. ", $node),
                Some(n_ptr) => {
                    assert_eq!($ll.head, n_ptr);
                }
            }
        };
    }

    macro_rules! assert_is_not_head {
        ($ll:ident, $node:ident) => {
            match $ll.node_ptr(&$node) {
                None => panic!("Node: {:?} not found", $node),
                Some(n_ptr) => {
                    assert_ne!($ll.head, n_ptr);
                }
            }
        };
    }

    macro_rules! assert_is_tail {
        ($ll:ident, $node:ident) => {
            match $ll.node_ptr(&$node) {
                None => panic!("Node: {:?} not found. ", $node),
                Some(n_ptr) => {
                    assert_eq!($ll.tail, n_ptr);
                }
            }
        };
    }

    macro_rules! assert_is_not_tail {
        ($ll:ident, $node:ident) => {
            match $ll.node_ptr(&$node) {
                None => panic!("Node: {:?} not found", $node),
                Some(n_ptr) => {
                    assert_ne!($ll.tail, n_ptr);
                }
            }
        };
    }

    macro_rules! assert_node {
        ($ll:ident, $node: ident, $pos: ident, $val: literal, $len: literal) => {
            assert_eq!($node.cid, $ll.cid);

            if $pos == FIRST || $pos == ONLY {
                assert_is_head!($ll, $node);
                assert_eq!($ll.head(), Some(&$val));
                assert_eq!($ll.has_prev(&$node), Some(false));
            }

            if $pos == LAST || $pos == ONLY {
                assert_is_tail!($ll, $node);
                assert_eq!($ll.tail(), Some(&$val));
                assert_eq!($ll.has_next(&$node), Some(false));
            }

            if $pos == MIDDLE {
                assert_is_not_tail!($ll, $node);
                assert_is_not_head!($ll, $node);
                assert_eq!($ll.has_next(&$node), Some(true));
                assert_eq!($ll.has_prev(&$node), Some(true));
            }

            assert_eq!($ll.has_tail(), true);
            assert_eq!($ll.has_head(), true);

            assert_eq!($ll.node(&$node), Some(&$val));
            assert_eq!($ll.len(), $len);
        };
    }

    macro_rules! assert_order {
        ($ll: ident, $x: ident, $x_val: literal, $y: ident, $y_val: literal) => {
            let x_ptr;
            let y_ptr;

            match $ll.node_ptr(&$x) {
                None => panic!("Node: {:?} not found", $x),
                Some(n_ptr) => x_ptr = n_ptr,
            }

            match $ll.node_ptr(&$y) {
                None => panic!("Node y: {:?} not found", $y),
                Some(n_ptr) => y_ptr = n_ptr,
            }

            unsafe {
                assert_eq!((*x_ptr).next, y_ptr);
                assert_eq!((*y_ptr).prev, x_ptr);
            }
            assert_eq!($ll.next(&$x), Some(&$y_val));
            assert_eq!($ll.prev(&$y), Some(&$x_val));
            assert_eq!($ll.next_node(&$x).as_ref(), Some(&$y));
            assert_eq!($ll.prev_node(&$y).as_ref(), Some(&$x));
            assert_eq!($ll.has_next(&$x), Some(true));
            assert_eq!($ll.has_prev(&$y), Some(true));
        };
    }

    macro_rules! assert_empty {
        ($ll:ident) => {
            assert!($ll.head.is_null());
            assert!($ll.tail.is_null());
            assert_eq!($ll.len(), 0);
        };
    }

    #[test]
    fn test_new() {
        let ll1 = FastLinkedList::<u8>::new();
        let ll2 = FastLinkedList::<u8>::new();
        assert!(ll1.cid < ll2.cid);
    }

    #[test]
    fn test_push_head() {
        let mut ll = FastLinkedList::<u8>::new();
        let node = ll.push_head(11);
        assert_node!(ll, node, ONLY, 11, 1);
        //now push a second head
        let second = ll.push_head(12);
        assert_node!(ll, second, FIRST, 12, 2);
        assert_node!(ll, node, LAST, 11, 2);
        assert_order!(ll, second, 12, node, 11);
        //now push a third node
        let third = ll.push_head(13);
        assert_node!(ll, third, FIRST, 13, 3);
        assert_node!(ll, second, MIDDLE, 12, 3);
        assert_node!(ll, node, LAST, 11, 3);

        assert_order!(ll, third, 13, second, 12);
        assert_order!(ll, second, 12, node, 11);

        ll.clear();
        assert_empty!(ll);
    }

    #[test]
    fn test_push_tail() {
        let mut ll = FastLinkedList::<u8>::new();
        let node = ll.push_tail(33);
        assert_node!(ll, node, ONLY, 33, 1);
        //now push a second head
        let second = ll.push_tail(44);
        assert_node!(ll, node, FIRST, 33, 2);
        assert_node!(ll, second, LAST, 44, 2);

        assert_order!(ll, node, 33, second, 44);
        //now push a third node
        let third = ll.push_tail(55);
        assert_node!(ll, node, FIRST, 33, 3);
        assert_node!(ll, second, MIDDLE, 44, 3);
        assert_node!(ll, third, LAST, 55, 3);

        assert_order!(ll, node, 33, second, 44);
        assert_order!(ll, second, 44, third, 55);

        ll.clear();
        assert_empty!(ll);
    }

    #[test]
    fn test_pop_head() {
        let mut ll = FastLinkedList::<u8>::new();
        let node = ll.push_head(11);
        assert_node!(ll, node, ONLY, 11, 1);
        //now pop the head
        assert_eq!(ll.pop_head(), Some(11));
        assert_empty!(ll);

        //now push two nodes
        let node = ll.push_head(11);
        ll.push_head(12);
        //now pop the head
        assert_eq!(ll.len(), 2);
        assert_eq!(ll.pop_head(), Some(12));
        assert_node!(ll, node, ONLY, 11, 1);
        //now pop the head again
        assert_eq!(ll.pop_head(), Some(11));
        assert_empty!(ll);

        //now push 3 nodes node
        let node = ll.push_head(11);
        let second = ll.push_head(12);
        ll.push_head(13);
        assert_eq!(ll.len(), 3);
        //pop the head
        assert_eq!(ll.pop_head(), Some(13));
        assert_node!(ll, node, LAST, 11, 2);
        assert_node!(ll, second, FIRST, 12, 2);
        //pop the head again
        assert_eq!(ll.pop_head(), Some(12));
        assert_node!(ll, node, ONLY, 11, 1);
        //pop the head for the last time
        assert_eq!(ll.pop_head(), Some(11));
        assert_empty!(ll);
    }

    #[test]
    fn test_pop_tail() {
        let mut ll = FastLinkedList::<u8>::new();
        let node = ll.push_tail(11);
        assert_node!(ll, node, ONLY, 11, 1);
        //now pop the tail
        assert_eq!(ll.pop_tail(), Some(11));
        assert_empty!(ll);

        //now push two nodes
        ll.push_head(11);
        let second = ll.push_head(12);
        assert_eq!(ll.len(), 2);
        //now pop the tail
        assert_eq!(ll.pop_tail(), Some(11));
        assert_node!(ll, second, ONLY, 12, 1);
        //now pop the head again
        assert_eq!(ll.pop_tail(), Some(12));
        assert_empty!(ll);

        //now push 3 nodes node
        ll.push_head(11);
        let second = ll.push_head(12);
        let third = ll.push_head(13);
        assert_eq!(ll.len(), 3);
        //pop the tail
        assert_eq!(ll.pop_tail(), Some(11));
        assert_node!(ll, second, LAST, 12, 2);
        assert_node!(ll, third, FIRST, 13, 2);
        //pop the head again
        assert_eq!(ll.pop_tail(), Some(12));
        assert_node!(ll, third, ONLY, 13, 1);
        //pop the head for the last time
        assert_eq!(ll.pop_tail(), Some(13));
        assert_empty!(ll);
    }

    #[test]
    fn test_capacity_zero() {
        let mut ll = FastLinkedList::<u8>::with_capacity(0);
        assert_eq!(ll.len(), 0);
        assert_eq!(ll.capacity(), 0);
        for _ in 0..5 {
            ll.push_head(11);
        }
        assert_eq!(ll.len(), 5);
        assert_eq!(ll.capacity(), 5);

        for _ in 0..3 {
            ll.pop_tail();
        }
        assert_eq!(ll.len(), 2);
        assert_eq!(ll.capacity(), 5);
    }

    #[test]
    fn test_capacity() {
        let mut ll = FastLinkedList::<u8>::with_capacity(2);
        assert_eq!(ll.len(), 0);
        assert_eq!(ll.capacity(), 2);
        for _ in 0..5 {
            ll.push_head(11);
        }
        assert_eq!(ll.len(), 5);
        assert_eq!(ll.capacity(), 8);
        //now add another 3
        for _ in 0..3 {
            ll.push_head(11);
        }
        assert_eq!(ll.len(), 8);
        assert_eq!(ll.capacity(), 8);
        //add one more
        ll.push_head(11);
        assert_eq!(ll.len(), 9);
        assert_eq!(ll.capacity(), 16);
        //now add another 8
        for _ in 0..8 {
            ll.push_head(11);
        }
        assert_eq!(ll.len(), 17);
        assert_eq!(ll.capacity(), 32);
        let mut ll = FastLinkedList::<u8>::with_capacity(17);
        for _ in 0..18 {
            ll.push_head(11);
        }
        assert_eq!(ll.len(), 18);
        assert_eq!(ll.capacity(), 34);
    }

    #[test]
    fn test_node_reuse() {
        let mut ll = FastLinkedList::<u8>::with_capacity(8);
        //first push one node
        let mut node = ll.push_head(1);
        for i in 0..7 {
            node = ll.push_head(i);
        }

        //now pop the head
        ll.pop_head();

        //now push it again
        let node2 = ll.push_head(200);
        assert_eq!(ll.node(&node2), Some(&200));
        assert_eq!(ll.node(&node), None);
    }

    #[test]
    fn test_iter() {
        let mut ll = FastLinkedList::<u8>::with_capacity(10);
        for i in 0..10 {
            ll.push_head(i);
        }

        let mut iter = ll.iter();
        let mut count = 9;
        while let Some(val) = iter.next() {
            assert_eq!(*val, count);
            if count > 0 {
                count -= 1;
            }
        }

        let mut iter_mut = ll.iter_mut();
        while let Some(val) = iter_mut.next() {
            *val += 1;
        }

        let iter = ll.iter();
        let mut count = 9;
        for val in iter {
            assert_eq!(*val, count + 1);
            if count > 0 {
                count -= 1;
            }
        }
        for val in &mut ll {
            *val -= 1;
        }

        let mut count = 9;
        for val in &ll {
            assert_eq!(*val, count);
            if count > 0 {
                count -= 1;
            }
        }
    }

    #[test]
    fn test_iter_reverse() {
        let mut ll = FastLinkedList::<u8>::with_capacity(10);
        for i in 0..10 {
            ll.push_head(i);
        }

        let mut iter = ll.iter().reverse();
        let mut count = 0;
        while let Some(val) = iter.next() {
            assert_eq!(*val, count);
            count += 1;
        }

        iter = iter.reverse();
        let mut count = 9;
        while let Some(val) = iter.next() {
            assert_eq!(*val, count);
            if count > 0 {
                count -= 1;
            }
        }

        iter = iter.reverse();
        let mut count = 0;
        while let Some(val) = iter.next() {
            assert_eq!(*val, count);
            count += 1;
        }
    }

    #[test]
    fn test_iter_reverse2() {
        let mut ll = FastLinkedList::<u8>::with_capacity(10);
        for i in 0..10 {
            ll.push_head(i);
        }

        let mut iter = ll.iter();
        assert_eq!(iter.next(), Some(&9));
        assert_eq!(iter.next(), Some(&8));
        assert_eq!(iter.next(), Some(&7));
        assert_eq!(iter.next(), Some(&6));
        assert_eq!(iter.next(), Some(&5));
        iter = iter.reverse();
        assert_eq!(iter.next(), Some(&6));
        assert_eq!(iter.next(), Some(&7));
        iter = iter.reverse();
        assert_eq!(iter.next(), Some(&6));
        assert_eq!(iter.next(), Some(&5));
        assert_eq!(iter.next(), Some(&4));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_invalid_node() {
        let mut ll = FastLinkedList::<u8>::with_capacity(10);
        let headnode = ll.push_head(12);
        let headval = ll.pop_head();
        assert_eq!(headval, Some(12));
        //Attempting to get the value at headnode should now return
        // None
        assert_eq!(ll.node(&headnode), None);
    }

    #[test]
    fn test_clear() {
        let mut ll = FastLinkedList::<u8>::with_capacity(10);
        ll.push_head(0);
        ll.push_head(1);
        ll.push_head(2);
        assert_eq!(ll.len(), 3);
        assert_eq!(ll.capacity(), 10);
        ll.clear();
        assert_eq!(ll.len(), 0);
        assert_eq!(ll.capacity(), 10);
    }

    #[test]
    fn test_push_next() {
        let mut ll = FastLinkedList::<u8>::new();
        let node1 = ll.push_head(1);
        let node2 = ll.push_head(2);
        let node3 = ll.push_head(3);

        let n_node1 = ll.push_next(&node1, 11).unwrap();
        assert_node!(ll, n_node1, LAST, 11, 4);
        assert_order!(ll, node1, 1, n_node1, 11);
        assert_order!(ll, node2, 2, node1, 1);
        assert_order!(ll, node3, 3, node2, 2);

        let n_node2 = ll.push_next(&node2, 22).unwrap();
        assert_node!(ll, n_node2, MIDDLE, 22, 5);
        assert_order!(ll, node1, 1, n_node1, 11);
        assert_order!(ll, n_node2, 22, node1, 1);
        assert_order!(ll, node2, 2, n_node2, 22);
        assert_order!(ll, node3, 3, node2, 2);

        let n_node3 = ll.push_next(&node3, 33).unwrap();
        assert_node!(ll, n_node3, MIDDLE, 33, 6);

        assert_order!(ll, node1, 1, n_node1, 11);
        assert_order!(ll, n_node2, 22, node1, 1);
        assert_order!(ll, node2, 2, n_node2, 22);
        assert_order!(ll, n_node3, 33, node2, 2);
        assert_order!(ll, node3, 3, n_node3, 33);
    }

    #[test]
    fn test_push_prev() {
        let mut ll = FastLinkedList::<u8>::new();
        let node1 = ll.push_head(1);
        let node2 = ll.push_head(2);
        let node3 = ll.push_head(3);

        let n_node1 = ll.push_prev(&node1, 11).unwrap();
        assert_node!(ll, node1, LAST, 1, 4);
        assert_node!(ll, n_node1, MIDDLE, 11, 4);
        assert_order!(ll, n_node1, 11, node1, 1);
        assert_order!(ll, node2, 2, n_node1, 11);
        assert_order!(ll, node3, 3, node2, 2);

        let n_node2 = ll.push_prev(&node2, 22).unwrap();
        assert_node!(ll, n_node2, MIDDLE, 22, 5);

        assert_order!(ll, n_node1, 11, node1, 1);
        assert_order!(ll, node2, 2, n_node1, 11);
        assert_order!(ll, n_node2, 22, node2, 2);
        assert_order!(ll, node3, 3, n_node2, 22);

        let n_node3 = ll.push_prev(&node3, 33).unwrap();
        assert_node!(ll, n_node3, FIRST, 33, 6);
        assert_order!(ll, n_node1, 11, node1, 1);
        assert_order!(ll, node2, 2, n_node1, 11);
        assert_order!(ll, n_node2, 22, node2, 2);
        assert_order!(ll, node3, 3, n_node2, 22);
        assert_order!(ll, n_node3, 33, node3, 3);
    }
}
