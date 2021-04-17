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
use core::ptr;

macro_rules! nid_inc {
    ($nid: expr) => {{
        let nid = $nid;
        $nid += 1;
        nid
    }};
}

/// A [fast doubly linked list](https://www.deepmesa.com/data-structures/fastlinkedlist/) that owns the nodes and can pre-allocate
/// memory for performance. This linked list allows pushing and
/// popping elements at either end or in the middle in constant time.
///
/// The API is the same as [`std::collections::LinkedList`] however
/// this list also allows pushing and popping elements from the middle
/// of the list in constant time.
///
/// This list [manages
/// memory](https://www.deepmesa.com/data-structures/fastlinkedlist/#mem_mgmt)
/// via an internal freelist of nodes and [capacity is
/// allocated](https://www.deepmesa.com/data-structures/fastlinkedlist/#cap_realloc)
/// when the list is full. Capacity is deallocated when the list is
/// dropped. This list also [vends
/// handles](https://www.deepmesa.com/data-structures/fastlinkedlist/#handles)
/// to its nodes that can be used to mutate the list at any node in
/// constant time. The list provides
/// [iterators](https://www.deepmesa.com/data-structures/fastlinkedlist/#iterators)
/// that can use used to traverse the list in either direction by
/// reversing the iterator at any time.
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

fn inc_cid() -> usize {
    unsafe {
        static mut LL_COUNTER: usize = 0;
        LL_COUNTER += 1;
        return LL_COUNTER;
    }
}

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
        FastLinkedList {
            cid: inc_cid(),
            nid: 0,
            len: 0,
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
            fl: fl::FreeList::new(8),
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
        FastLinkedList {
            cid: inc_cid(),
            nid: 0,
            len: 0,
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
            fl: fl::FreeList::new(capacity),
        }
    }

    /// Returns a bidirectional iterator over the list
    ///
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
    ///
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
    /// effect on the allocated capacity of the list.
    ///
    /// This method should complete in *O*(*n*) time.
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
    /// if the list is empty. This method simply calls
    /// [`self.head()`](#method.head)
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// if the list is empty. This method simply calls
    /// [`self.tail()`](#method.tail)
    ///
    /// This method should complete in *O*(*1*) time.
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

    /// Returns a mutable reference to the front (head) of the list or
    /// `None` if the list is empty. This method simply calls
    /// [`self.head_mut()`](#method.head_mut)
    ///
    /// This method should complete in *O*(*1*) time.
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

    /// Returns a mutable reference to the back (tail) of the list or
    /// `None` if the list is empty. This method simply calls
    /// [`self.tail_mut()`](#method.tail_mut)
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// if the list is empty.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// if the list is empty.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// if the list is empty.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// if the list is empty.
    ///
    /// This method should complete in *O*(*1*) time.
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

    /// Returns a reference to the value of the node immediately after
    /// the node associated with the specified handle. If the
    /// specified handle is invalid or there is no next node, this
    /// method returns None.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// next node, this method returns None.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// node, this method returns None.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// returns None.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// None.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// method returns None.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// method returns None.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// the list is empty.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// list is empty.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// handle is invalid this method returns None.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// handle is invalid this method returns None.
    ///
    /// This method should complete in *O*(*1*) time.
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

    /// Returns true if the list is empty and false otherwise.
    ///
    /// This method should complete in *O*(*1*) time.
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
    /// This method should complete in *O*(*1*) time.
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
    /// This method should complete in *O*(*1*) time.
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
    ///
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
    ///
    /// This method should complete in *O*(*1*) time.
    ///
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

    /// Adds an element to the front (head) of the list. This method
    /// simply calls [`self.push_head()`](#method.push_head)
    ///
    /// This operation should complete in *O*(*1*) time.
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

    /// Adds an element to the back (tail) of the list. This method
    /// simply calls [`self.push_tail()`](#method.push_tail)
    ///
    /// This operation should complete in *O*(*1*) time.
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

    /// Removes and returns the value at the head (front) of the
    /// list or None if the list is empty.
    ///
    /// This operation should complete in *O*(*1*) time
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
    /// list or None if the list is empty.
    ///
    /// This operation should complete in *O*(*1*) time
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
    /// or None if the list is empty. This method simply calls
    /// [`self.pop_head()`](#method.pop_head)
    ///
    /// This operation should complete in *O*(*1*) time.
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
    /// or None if the list is empty. This method simply calls
    /// [`self.pop_tail()`](#method.pop_tail)
    ///
    /// This operation should complete in *O*(*1*) time
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
    /// This operation should complete in *O*(*1*) time
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
    /// This operation should complete in *O*(*1*) time
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
    /// This operation should complete in *O*(*1*) time
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
    /// handle to it.
    ///
    /// This operation should complete in *O*(*1*) time.
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
    /// handle to it.
    ///
    /// This operation should complete in *O*(*1*) time.
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
    /// This operation should complete in *O*(*n*) time
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
    /// added or None if the specified handle is invalid.
    ///
    /// This operation should complete in *O*(*1*) time.
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
    /// added or None if the specified handle is invalid.
    ///
    /// This operation should complete in *O*(*1*) time.
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

    /// Moves all nodes from the `other` list to the end of this
    /// list. After this operation completes, the `other` list is
    /// empty and all the nodes from that list have been moved into
    /// this one.
    ///
    /// All handles to nodes previously returned by other list will
    /// become invalid after this operation completes.
    ///
    /// This operation has no effect on the allocated capacity of
    /// either list.
    ///
    /// This operation should compute in *O*(*1*) time
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(10);
    /// list.push_back(0);
    ///
    /// let mut list2 = FastLinkedList::<u8>::with_capacity(10);
    /// list2.push_back(1);
    /// list2.push_back(2);
    ///
    /// list.append(&mut list2);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), None);
    ///
    /// assert_eq!(list.len(), 3);
    /// assert!(list2.is_empty());
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        if self.tail.is_null() {
            self.head = other.head;
        } else {
            unsafe {
                (*self.tail).next = other.head;
                if !other.head.is_null() {
                    (*other.head).prev = self.tail;
                }
            }
        }

        self.tail = other.tail;
        self.len += other.len;
        other.head = ptr::null_mut();
        other.tail = ptr::null_mut();
        other.len = 0;
        other.cid = inc_cid();
    }

    /// Moves the node associated with the specified handle to the
    /// front (head) of the list. If the node is already at the head
    /// of the list then this operation has no effect.
    ///
    /// Returns true if the node is successfully moved to the head of
    /// the list (or if it was already at the head) and false if the
    /// specified handle is invalid.
    ///
    /// This operation should complete in *O*(*1*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(3);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    ///
    /// assert_eq!(list.head(), Some(&0));
    /// list.make_head(&hnd2);
    /// assert_eq!(list.head(), Some(&2));
    /// ```
    pub fn make_head(&mut self, node: &Node<T>) -> bool {
        match self.node_ptr(node) {
            None => false,
            Some(n_ptr) => unsafe {
                if n_ptr == self.head {
                    return true;
                }

                if !(*n_ptr).prev.is_null() {
                    (*(*n_ptr).prev).next = (*n_ptr).next;
                }
                if !(*n_ptr).next.is_null() {
                    (*(*n_ptr).next).prev = (*n_ptr).prev;
                }

                if n_ptr == self.tail {
                    self.tail = (*n_ptr).prev;
                }

                (*n_ptr).prev = ptr::null_mut();
                (*n_ptr).next = self.head;
                (*self.head).prev = n_ptr;
                self.head = n_ptr;
                true
            },
        }
    }

    /// Moves the node associated with the specified handle to the
    /// back (tail) of the list. If the node is already at the tail of
    /// the list then this operation has no effect.
    ///
    /// Returns true if the node is successfully moved to the tail of
    /// the list (or if it was already at the tail) and false if the
    /// specified handle is invalid.
    ///
    /// This operation should complete in *O*(*1*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(3);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    ///
    /// assert_eq!(list.tail(), Some(&2));
    /// list.make_tail(&hnd0);
    /// assert_eq!(list.tail(), Some(&0));
    /// ```
    pub fn make_tail(&mut self, node: &Node<T>) -> bool {
        match self.node_ptr(node) {
            None => false,
            Some(n_ptr) => unsafe {
                if n_ptr == self.tail {
                    return true;
                }

                if !(*n_ptr).prev.is_null() {
                    (*(*n_ptr).prev).next = (*n_ptr).next;
                }
                if !(*n_ptr).next.is_null() {
                    (*(*n_ptr).next).prev = (*n_ptr).prev;
                }

                if n_ptr == self.head {
                    self.head = (*n_ptr).next;
                }

                (*n_ptr).next = ptr::null_mut();
                (*n_ptr).prev = self.tail;
                (*self.tail).next = n_ptr;
                self.tail = n_ptr;
                true
            },
        }
    }

    /// Returns `true` if the specified node is immediately previous
    /// to `other` and `false` otherwise. If either of the nodes is
    /// invalid, this method returns None.
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(4);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    /// list.pop_tail();
    /// assert_eq!(list.is_prev(&hnd0, &hnd1), Some(true));
    /// assert_eq!(list.is_prev(&hnd1, &hnd0), Some(false));
    /// assert_eq!(list.is_prev(&hnd1, &hnd2), None);
    /// ```
    pub fn is_prev(&self, node: &Node<T>, other: &Node<T>) -> Option<bool> {
        if let Some(n_ptr) = self.node_ptr(node) {
            if let Some(o_ptr) = self.node_ptr(other) {
                unsafe {
                    if (*n_ptr).next == o_ptr {
                        return Some(true);
                    } else {
                        return Some(false);
                    }
                }
            }
        }
        None
    }

    /// Returns `true` if the specified node is immediately after
    /// `other` and `false` otherwise. If either of the nodes is
    /// invalid, this method returns None.
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(4);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    /// list.pop_tail();
    /// assert_eq!(list.is_next(&hnd1, &hnd0), Some(true));
    /// assert_eq!(list.is_next(&hnd0, &hnd1), Some(false));
    /// assert_eq!(list.is_next(&hnd2, &hnd1), None);
    /// ```
    pub fn is_next(&self, node: &Node<T>, other: &Node<T>) -> Option<bool> {
        if let Some(n_ptr) = self.node_ptr(node) {
            if let Some(o_ptr) = self.node_ptr(other) {
                unsafe {
                    if (*n_ptr).prev == o_ptr {
                        return Some(true);
                    } else {
                        return Some(false);
                    }
                }
            }
        }
        None
    }

    /// Returns `true` if the specified node is the head of the list
    /// and `false` if its not. If the specified node is invalid, then
    /// this method returns `None`
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(4);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    /// list.pop_tail();
    /// assert_eq!(list.is_head(&hnd0), Some(true));
    /// assert_eq!(list.is_head(&hnd1), Some(false));
    /// assert_eq!(list.is_head(&hnd2), None);
    /// ```
    pub fn is_head(&self, node: &Node<T>) -> Option<bool> {
        if let Some(n_ptr) = self.node_ptr(node) {
            if n_ptr == self.head {
                return Some(true);
            } else {
                return Some(false);
            }
        }
        None
    }

    /// Returns `true` if the specified node is the tail of the list
    /// and `false` if its not. If the specified node is invalid, then
    /// this method returns `None`
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(4);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    /// list.pop_tail();
    /// assert_eq!(list.is_tail(&hnd0), Some(false));
    /// assert_eq!(list.is_tail(&hnd1), Some(true));
    /// assert_eq!(list.is_tail(&hnd2), None);
    /// ```
    pub fn is_tail(&self, node: &Node<T>) -> Option<bool> {
        if let Some(n_ptr) = self.node_ptr(node) {
            if n_ptr == self.tail {
                return Some(true);
            } else {
                return Some(false);
            }
        }
        None
    }

    /// Swaps the position in the list of the two nodes and returns
    /// true on success. If either node is invalid then this method
    /// returns false.
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::FastLinkedList;
    /// let mut list = FastLinkedList::<u8>::with_capacity(4);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    /// list.pop_tail();
    /// assert_eq!(list.swap_node(&hnd0, &hnd1), true);
    /// assert_eq!(list.swap_node(&hnd1, &hnd2), false);
    /// assert_eq!(list.is_head(&hnd1), Some(true));
    /// assert_eq!(list.is_tail(&hnd0), Some(true));
    /// ```
    pub fn swap_node(&mut self, node: &Node<T>, other: &Node<T>) -> bool {
        if let Some(n_ptr) = self.node_ptr(node) {
            if let Some(o_ptr) = self.node_ptr(other) {
                if n_ptr == o_ptr {
                    return true;
                }
                unsafe {
                    if (*n_ptr).next == o_ptr {
                        //n_ptr is after o_pter. Swap them
                        self.swap_node_adjacent(n_ptr, o_ptr);
                        return true;
                    }
                    if (*o_ptr).next == n_ptr {
                        //o_ptr is after n_ptr. Swap them
                        self.swap_node_adjacent(o_ptr, n_ptr);
                        return true;
                    }
                    // n_ptr & o_ptr at disjoint - i.e. have atleast one other node between them
                    let np_prev = (*n_ptr).prev;
                    let np_next = (*n_ptr).next;
                    let op_prev = (*o_ptr).prev;
                    let op_next = (*o_ptr).next;

                    (*o_ptr).prev = np_prev;
                    (*o_ptr).next = np_next;
                    (*n_ptr).prev = op_prev;
                    (*n_ptr).next = op_next;

                    if np_prev.is_null() {
                        //n_ptr is at the head. So make o_ptr the head
                        self.head = o_ptr;
                    } else {
                        (*np_prev).next = o_ptr;
                    }

                    if np_next.is_null() {
                        //n_ptr is at the tail. So make o_ptr the tail
                        self.tail = o_ptr;
                    } else {
                        (*np_next).prev = o_ptr;
                    }

                    if op_prev.is_null() {
                        //o_ptr is at the head. So make n_ptr the head
                        self.head = n_ptr;
                    } else {
                        (*op_prev).next = n_ptr;
                    }

                    if op_next.is_null() {
                        //o_ptr is the tail. So make n_ptr the tail
                        self.tail = n_ptr;
                    } else {
                        (*op_next).prev = n_ptr;
                    }

                    return true;
                }
            }
        }
        false
    }

    ////////////////////
    //Private Helpers
    ////////////////////

    /// Removes and returns the value pointed to by the specified raw
    /// pointer. This method will panic if the specified pointer is
    /// null. The memory is returned to the free list.
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
            // First check if this node is on the freelist. If it is
            // then we don't need to check the node id (nid)
            if (*node.ptr).fl_node {
                return None;
            }

            if (*node.ptr).nid != node.nid {
                return None;
            }
        }

        Some((*node).ptr)
    }

    unsafe fn swap_node_adjacent(
        &mut self,
        n_ptr: *mut InternalNode<T>,
        o_ptr: *mut InternalNode<T>,
    ) {
        // N -> O

        if (*n_ptr).prev.is_null() {
            //n_ptr is the head
            self.head = o_ptr;
        } else {
            (*(*n_ptr).prev).next = o_ptr;
        }

        if (*o_ptr).next.is_null() {
            //o_ptr is the tail
            self.tail = n_ptr;
        } else {
            (*(*o_ptr).next).prev = n_ptr;
        }

        (*n_ptr).next = (*o_ptr).next;
        (*o_ptr).prev = (*n_ptr).prev;
        (*o_ptr).next = n_ptr;
        (*n_ptr).prev = o_ptr;
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

    #[test]
    fn test_append() {
        let mut ll = FastLinkedList::<u8>::with_capacity(4);
        for i in 0..4 {
            ll.push_tail(i);
        }
        assert_eq!(ll.len(), 4);
        assert_eq!(ll.capacity(), 4);
        assert_eq!(ll.fl.len(), 0);

        let mut otherll = FastLinkedList::<u8>::with_capacity(10);
        for i in 0..10 {
            otherll.push_tail(i);
        }
        assert_eq!(otherll.len(), 10);
        assert_eq!(otherll.fl.len(), 0);
        assert_eq!(otherll.capacity(), 10);

        ll.append(&mut otherll);
        assert_eq!(otherll.len(), 0);
        assert_eq!(otherll.capacity(), 0);
        assert_eq!(otherll.fl.len(), 0);

        assert_eq!(ll.len(), 14);
        assert_eq!(ll.capacity(), 14);
        assert_eq!(ll.fl.len(), 0);
        for i in 0..4 {
            ll.push_tail(i + 100);
        }

        assert_eq!(ll.len(), 18);
        assert_eq!(ll.capacity(), 18);
        assert_eq!(ll.fl.len(), 0);
        ll.push_head(111);
        assert_eq!(ll.len(), 19);
        assert_eq!(ll.capacity(), 26);
        assert_eq!(ll.fl.len(), 7);
        //now clear the lists
        ll.clear();
        assert_eq!(ll.len(), 0);
        assert_eq!(ll.capacity(), 26);
        assert_eq!(ll.fl.len(), 26);
        otherll.clear();
        assert_eq!(otherll.len(), 0);
        assert_eq!(otherll.capacity(), 0);
        assert_eq!(otherll.fl.len(), 0);
    }

    #[test]
    fn test_append_handle() {
        let mut ll = FastLinkedList::<u8>::with_capacity(4);
        ll.push_tail(1);
        ll.push_tail(2);
        ll.push_tail(3);

        let hnd: Node<u8>;
        {
            let mut other = FastLinkedList::<u8>::with_capacity(4);
            other.push_tail(4);
            hnd = other.push_tail(5);
            other.push_tail(6);

            //its a valid handle
            assert_eq!(other.node(&hnd), Some(&5));
            ll.append(&mut other);
            //handle should now be invalid
            assert_eq!(other.node(&hnd), None);
            assert_eq!(other.len(), 0);
            assert!(other.is_empty());
        }
        assert_eq!(ll.node(&hnd), None);
        let mut count = 1;
        for val in ll.iter() {
            assert_eq!(val, &count);
            count += 1;
        }
    }

    #[test]
    fn test_make_head() {
        let mut ll = FastLinkedList::<u8>::with_capacity(4);
        let hnd1 = ll.push_tail(1);
        let hnd2 = ll.push_tail(2);
        let hnd3 = ll.push_tail(3);
        assert!(ll.make_head(&hnd1));
        assert_order!(ll, hnd1, 1, hnd2, 2);
        assert_order!(ll, hnd2, 2, hnd3, 3);

        assert_node!(ll, hnd1, FIRST, 1, 3);
        assert_node!(ll, hnd2, MIDDLE, 2, 3);
        assert_node!(ll, hnd3, LAST, 3, 3);

        assert!(ll.make_head(&hnd2));
        assert_order!(ll, hnd2, 2, hnd1, 1);
        assert_order!(ll, hnd1, 1, hnd3, 3);

        assert_node!(ll, hnd2, FIRST, 2, 3);
        assert_node!(ll, hnd1, MIDDLE, 1, 3);
        assert_node!(ll, hnd3, LAST, 3, 3);

        assert!(ll.make_head(&hnd3));
        assert_order!(ll, hnd3, 3, hnd2, 2);
        assert_order!(ll, hnd2, 2, hnd1, 1);

        assert_node!(ll, hnd3, FIRST, 3, 3);
        assert_node!(ll, hnd2, MIDDLE, 2, 3);
        assert_node!(ll, hnd1, LAST, 1, 3);
    }

    #[test]
    fn test_make_tail() {
        let mut ll = FastLinkedList::<u8>::with_capacity(4);
        let hnd1 = ll.push_tail(1);
        let hnd2 = ll.push_tail(2);
        let hnd3 = ll.push_tail(3);
        assert!(ll.make_tail(&hnd3));
        assert_order!(ll, hnd1, 1, hnd2, 2);
        assert_order!(ll, hnd2, 2, hnd3, 3);

        assert_node!(ll, hnd1, FIRST, 1, 3);
        assert_node!(ll, hnd2, MIDDLE, 2, 3);
        assert_node!(ll, hnd3, LAST, 3, 3);

        assert!(ll.make_tail(&hnd2));
        assert_order!(ll, hnd1, 1, hnd3, 3);
        assert_order!(ll, hnd3, 3, hnd2, 2);

        assert_node!(ll, hnd1, FIRST, 1, 3);
        assert_node!(ll, hnd3, MIDDLE, 3, 3);
        assert_node!(ll, hnd2, LAST, 2, 3);

        assert!(ll.make_tail(&hnd1));
        assert_order!(ll, hnd3, 3, hnd2, 2);
        assert_order!(ll, hnd2, 2, hnd1, 1);

        assert_node!(ll, hnd3, FIRST, 3, 3);
        assert_node!(ll, hnd2, MIDDLE, 2, 3);
        assert_node!(ll, hnd1, LAST, 1, 3);
    }

    #[test]
    fn test_is_next() {
        let mut ll = FastLinkedList::<u8>::with_capacity(4);
        let hnd1 = ll.push_tail(1);
        let hnd2 = ll.push_tail(2);
        let hnd3 = ll.push_tail(3);
        ll.pop_tail();
        assert_eq!(ll.is_next(&hnd1, &hnd1), Some(false));
        assert_eq!(ll.is_next(&hnd1, &hnd2), Some(false));
        assert_eq!(ll.is_next(&hnd2, &hnd1), Some(true));
        assert_eq!(ll.is_next(&hnd2, &hnd3), None);
        assert_eq!(ll.is_next(&hnd1, &hnd3), None);
        assert_eq!(ll.is_next(&hnd3, &hnd3), None);
    }

    #[test]
    fn test_is_prev() {
        let mut ll = FastLinkedList::<u8>::with_capacity(4);
        let hnd1 = ll.push_tail(1);
        let hnd2 = ll.push_tail(2);
        let hnd3 = ll.push_tail(3);
        ll.pop_tail();
        assert_eq!(ll.is_prev(&hnd1, &hnd1), Some(false));
        assert_eq!(ll.is_prev(&hnd1, &hnd2), Some(true));
        assert_eq!(ll.is_prev(&hnd2, &hnd1), Some(false));
        assert_eq!(ll.is_prev(&hnd2, &hnd3), None);
        assert_eq!(ll.is_prev(&hnd1, &hnd3), None);
        assert_eq!(ll.is_prev(&hnd3, &hnd3), None);
    }

    #[test]
    fn test_swap_node() {
        let mut ll = FastLinkedList::<u8>::with_capacity(4);
        let hnd0 = ll.push_tail(0);
        let hnd1 = ll.push_tail(1);
        let hnd2 = ll.push_tail(2);
        let hnd3 = ll.push_tail(3);

        ll.swap_node(&hnd0, &hnd3);
        assert_node!(ll, hnd3, FIRST, 3, 4);
        assert_node!(ll, hnd1, MIDDLE, 1, 4);
        assert_node!(ll, hnd2, MIDDLE, 2, 4);
        assert_node!(ll, hnd0, LAST, 0, 4);

        assert_order!(ll, hnd3, 3, hnd1, 1);
        assert_order!(ll, hnd1, 1, hnd2, 2);
        assert_order!(ll, hnd2, 2, hnd0, 0);

        ll.swap_node(&hnd1, &hnd2);
        assert_node!(ll, hnd3, FIRST, 3, 4);
        assert_node!(ll, hnd2, MIDDLE, 2, 4);
        assert_node!(ll, hnd1, MIDDLE, 1, 4);
        assert_node!(ll, hnd0, LAST, 0, 4);

        assert_order!(ll, hnd3, 3, hnd2, 2);
        assert_order!(ll, hnd2, 2, hnd1, 1);
        assert_order!(ll, hnd1, 1, hnd0, 0);

        ll.swap_node(&hnd3, &hnd2);
        assert_node!(ll, hnd2, FIRST, 2, 4);
        assert_node!(ll, hnd3, MIDDLE, 3, 4);
        assert_node!(ll, hnd1, MIDDLE, 1, 4);
        assert_node!(ll, hnd0, LAST, 0, 4);

        assert_order!(ll, hnd2, 2, hnd3, 3);
        assert_order!(ll, hnd3, 3, hnd1, 1);
        assert_order!(ll, hnd1, 1, hnd0, 0);

        ll.swap_node(&hnd1, &hnd0);
        assert_node!(ll, hnd2, FIRST, 2, 4);
        assert_node!(ll, hnd3, MIDDLE, 3, 4);
        assert_node!(ll, hnd0, MIDDLE, 0, 4);
        assert_node!(ll, hnd1, LAST, 1, 4);

        assert_order!(ll, hnd2, 2, hnd3, 3);
        assert_order!(ll, hnd3, 3, hnd0, 0);
        assert_order!(ll, hnd0, 0, hnd1, 1);

        ll.swap_node(&hnd3, &hnd2);
        assert_node!(ll, hnd3, FIRST, 3, 4);
        assert_node!(ll, hnd2, MIDDLE, 2, 4);
        assert_node!(ll, hnd0, MIDDLE, 0, 4);
        assert_node!(ll, hnd1, LAST, 1, 4);

        assert_order!(ll, hnd3, 3, hnd2, 2);
        assert_order!(ll, hnd2, 2, hnd0, 0);
        assert_order!(ll, hnd0, 0, hnd1, 1);

        ll.swap_node(&hnd1, &hnd0);
        assert_node!(ll, hnd3, FIRST, 3, 4);
        assert_node!(ll, hnd2, MIDDLE, 2, 4);
        assert_node!(ll, hnd1, MIDDLE, 1, 4);
        assert_node!(ll, hnd0, LAST, 0, 4);

        assert_order!(ll, hnd3, 3, hnd2, 2);
        assert_order!(ll, hnd2, 2, hnd1, 1);
        assert_order!(ll, hnd1, 1, hnd0, 0);
    }
}
