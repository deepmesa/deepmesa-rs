/*
   Linked List: A fast and flexible doubly linked list that
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

use crate::linkedlist::list::LinkedList;
use core::ptr;

#[derive(Debug, PartialEq, Eq)]
pub(super) struct InternalNode<T> {
    pub(super) val: T,
    pub(super) fl_node: bool,
    pub(super) nid: usize,
    pub(super) prev: *mut InternalNode<T>,
    pub(super) next: *mut InternalNode<T>,
}

/// A handle to a node in the [`LinkedList`](../struct.LinkedList.html).
///
/// This struct wraps a raw pointer to memory but does not implement
/// the [`Deref`](https://doc.rust-lang.org/std/ops/trait.Deref.html) trait so you cannot dereference that pointer directly.
/// Handles can be used only by methods of the linkedlist that they
/// were obtained from. They can be copied and passed around by value
/// regardless of the lifetime of the linkedlist. Once the element
/// that the handle refers to is removed from the linked list, the
/// handle then becomes invalid. Passing an invalid handle into the
/// linked list is safe since all methods that accept a reference to a
/// handle return `None` if the handle is invalid.
///

/// The
/// [`push_head()`](../struct.LinkedList.html#method.push_head),
/// [`push_tail()`](../struct.LinkedList.html#method.push_tail),
/// [`push_next()`](../struct.LinkedList.html#method.push_next)
/// and
/// [`push_prev()`](../struct.LinkedList.html#method.push_prev)
/// methods of [`LinkedList`](../struct.LinkedList.html)
/// return handles to the nodes pushed to the linked list. Handles can
/// only be used by passing them as arguments to the
/// [`next()`](../struct.LinkedList.html#method.next),
/// [`next_mut()`](../struct.LinkedList.html#method.next_mut),
/// [`prev()`](../struct.LinkedList.html#method.prev),
/// [`prev_mut()`](../struct.LinkedList.html#method.prev_mut),
/// [`prev_node()`](../struct.LinkedList.html#method.prev_node),
/// [`next_node()`](../struct.LinkedList.html#method.next_node),
/// [`node()`](../struct.LinkedList.html#method.node),
/// [`node_mut()`](../struct.LinkedList.html#method.node_mut),
/// [`has_next()`](../struct.LinkedList.html#method.has_next),
/// [`has_prev()`](../struct.LinkedList.html#method.has_prev),
/// [`pop_next()`](../struct.LinkedList.html#method.pop_next),
/// [`pop_prev()`](../struct.LinkedList.html#method.pop_prev),
/// [`pop_node()`](../struct.LinkedList.html#method.pop_node),
/// [`push_next()`](../struct.LinkedList.html#method.push_next),
/// [`push_prev()`](../struct.LinkedList.html#method.push_prev),
/// methods of the list. This allows adding, removing and mutating
/// elements in the middle of the list in *O*(*1*) time.

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
/// use deepmesa::lists::LinkedList;
/// let mut list = LinkedList::<u8>::with_capacity(10);
/// list.push_head(1);
/// let middle = list.push_head(100);
/// list.push_head(2);
///
/// // get the value of the node in the middle of the list in *O*(*1*)
/// // time.
/// assert_eq!(list.node(&middle), Some(&100));
/// // remove the middle node in *O*(*1*) time
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
/// use deepmesa::lists::LinkedList;
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
/// let mut list = LinkedList::<u8>::with_capacity(10);
/// // The default handle is invalid
/// assert_eq!(list.node(&s.handle), None);
/// // push a new element and store the handle
/// s.handle = list.push_head(1);
/// assert_eq!(list.node(&s.handle), Some(&1));
/// ```
#[derive(Debug, PartialEq, Eq, Copy)]
pub struct Node<T> {
    pub(super) cid: usize,
    pub(super) nid: usize,
    pub(super) ptr: *mut InternalNode<T>,
}

impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self { ..*self }
    }
}

impl<T> Default for Node<T> {
    fn default() -> Self {
        Self {
            cid: 0,
            nid: 0,
            ptr: ptr::null_mut(),
        }
    }
}

impl<T> InternalNode<T> {
    pub(super) fn new(val: T, nid: usize) -> InternalNode<T> {
        InternalNode {
            val,
            fl_node: false,
            nid,
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
        }
    }
}

impl<T> Node<T> {
    pub(super) fn new(cid: usize, nid: usize, ptr: *mut InternalNode<T>) -> Node<T> {
        Node { cid, nid, ptr }
    }

    /// Returns `Some(true)` if the specified node is the head of the
    /// list and `Some(false)` if its not. If the specified node is
    /// invalid then this method returns `None`. This method simply
    /// calls
    /// [`LinkedList::is_head()`](../struct.LinkedList.html#method.is_head)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(4);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    /// list.pop_tail();
    /// assert_eq!(hnd0.is_head(&list), Some(true));
    /// assert_eq!(hnd1.is_head(&list), Some(false));
    /// assert_eq!(hnd2.is_head(&list), None);
    /// ```
    pub fn is_head(&self, list: &LinkedList<T>) -> Option<bool> {
        list.is_head(self)
    }

    /// Returns `true` if the specified node is the tail of the list
    /// and `false` if its not. If the specified node is invalid, then
    /// this method returns `None`. This method simply calls
    /// [`LinkedList::is_tail()`](../struct.LinkedList.html#method.is_tail)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(4);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    /// list.pop_tail();
    /// assert_eq!(hnd0.is_tail(&list), Some(false));
    /// assert_eq!(hnd1.is_tail(&list), Some(true));
    /// assert_eq!(hnd2.is_tail(&list), None);
    /// ```
    pub fn is_tail(&self, list: &LinkedList<T>) -> Option<bool> {
        list.is_tail(self)
    }

    /// Returns `true` if the specified node is immediately previous
    /// to `other` and `false` otherwise. If either of the nodes is
    /// invalid this method returns None. This method simply calls
    /// [`LinkedList::is_prev()`](../struct.LinkedList.html#method.is_prev)
    ///
    /// This method should return in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(4);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    /// list.pop_tail();
    /// assert_eq!(hnd0.is_prev(&hnd1, &list), Some(true));
    /// assert_eq!(hnd1.is_prev(&hnd0, &list), Some(false));
    /// assert_eq!(hnd1.is_prev(&hnd2, &list), None);
    /// ```
    pub fn is_prev(&self, other: &Node<T>, list: &LinkedList<T>) -> Option<bool> {
        list.is_prev(self, other)
    }

    /// Returns `true` if the specified node is immediately after
    /// `other` and `false` otherwise. If either of the nodes is
    /// invalid, this method returns None. This method simply calls
    /// [`LinkedList::is_next()`](../struct.LinkedList.html#method.is_next)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(4);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    /// list.pop_tail();
    /// assert_eq!(hnd1.is_next(&hnd0, &list), Some(true));
    /// assert_eq!(hnd0.is_next(&hnd1, &list), Some(false));
    /// assert_eq!(hnd2.is_next(&hnd1, &list), None);
    /// ```
    pub fn is_next(&self, other: &Node<T>, list: &LinkedList<T>) -> Option<bool> {
        list.is_next(self, other)
    }

    /// Returns true if the node associated with the specified handle
    /// has a next node and false if it does not. If the specified
    /// handle is invalid this method returns None. This method simply
    /// calls
    /// [`LinkedList::has_next()`](../struct.LinkedList.html#method.has_next)
    ///
    ///This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    /// let node1 = list.push_head(1);
    /// let node2 = list.push_head(2);
    ///
    /// assert_eq!(node1.has_next(&list), Some(false));
    /// assert_eq!(node2.has_next(&list), Some(true));
    ///
    /// list.pop_head();
    /// assert_eq!(node1.has_next(&list), Some(false));
    /// // once the head is popped node2 becomes an invalid handle
    /// assert_eq!(node2.has_next(&list), None);
    /// ```
    pub fn has_next(&self, list: &LinkedList<T>) -> Option<bool> {
        list.has_next(self)
    }

    /// Returns true if the node associated with the specified handle
    /// has a previous node and false if it does not. If the specified
    /// handle is invalid this method returns None. This method simply
    /// calls
    /// [`LinkedList::has_prev()`](../struct.LinkedList.html#method.has_prev)
    ///
    ///This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    /// let node1 = list.push_head(1);
    /// let node2 = list.push_head(2);
    ///
    /// assert_eq!(node1.has_prev(&list), Some(true));
    /// assert_eq!(node2.has_prev(&list), Some(false));
    ///
    /// list.pop_head();
    /// assert_eq!(node1.has_prev(&list), Some(false));
    /// // once the head is popped node2 becomes an invalid handle
    /// assert_eq!(node2.has_next(&list), None);
    /// ```
    pub fn has_prev(&self, list: &LinkedList<T>) -> Option<bool> {
        list.has_prev(self)
    }

    /// Returns a reference to the value of the node immediately after
    /// the node associated with this handle. If this handle is
    /// invalid in the specified list or there is no next node, this
    /// method returns None. This method simply calls
    /// [`LinkedList::next()`](../struct.LinkedList.html#method.next)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    /// list.push_head(1);
    /// let node = list.push_head(2);
    ///
    /// assert_eq!(node.next(&list), Some(&1));
    ///
    /// list.pop_tail();
    /// // once the tail is popped, there is no next
    /// assert_eq!(node.next(&list), None);
    /// ```
    pub fn next<'a>(&self, list: &'a LinkedList<T>) -> Option<&'a T> {
        list.next(self)
    }

    /// Returns a mutable reference to the value of the node
    /// immediately after the node associated with this handle. If the
    /// this handle is invalid in the specified list or if there is no
    /// next node, this method returns None. This method simply calls
    /// [`LinkedList::next_mut()`](../struct.LinkedList.html#method.next_mut)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    /// list.push_head(1);
    /// let node = list.push_head(2);
    /// assert_eq!(node.next(&list), Some(&1));
    ///
    /// match node.next_mut(&mut list) {
    ///     None => {},
    ///     Some(x) => *x = 100,
    /// }
    ///
    /// assert_eq!(node.next(&list), Some(&100));
    /// ```
    pub fn next_mut<'a>(&self, list: &'a mut LinkedList<T>) -> Option<&'a mut T> {
        list.next_mut(self)
    }

    /// Returns a reference to the value of the node immediately
    /// preceeding the node associated with this handle.  If this
    /// handle is invalid in the specified list or if there is no
    /// preceeding node, this method returns None. This method simply
    /// calls
    /// [`LinkedList::prev()`](../struct.LinkedList.html#method.prev)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    /// list.push_head(2);
    ///
    /// assert_eq!(node.prev(&list), Some(&2));
    ///
    /// list.pop_head();
    /// // once the head is popped, there is no prev
    /// assert_eq!(node.prev(&list), None);
    /// ```
    pub fn prev<'a>(&self, list: &'a LinkedList<T>) -> Option<&'a T> {
        list.prev(self)
    }

    /// Returns a mutable reference to the value of the node
    /// immediately preceeding the node associated with this
    /// handle. If this handle is invalid in the specified list or
    /// there is no preceeding node, this method returns None. This
    /// method simply calls
    /// [`LinkedList::prev_mut()`](../struct.LinkedList.html#method.prev_mut)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    /// list.push_head(2);
    /// assert_eq!(node.prev(&list), Some(&2));
    ///
    /// match node.prev_mut(&mut list) {
    ///     None => {},
    ///     Some(x) => *x = 100,
    /// }
    ///
    /// assert_eq!(node.prev(&list), Some(&100));
    /// ```
    pub fn prev_mut<'a>(&self, list: &'a mut LinkedList<T>) -> Option<&'a mut T> {
        list.prev_mut(self)
    }

    /// Returns a handle to the node immediately preceeding the node
    /// associated with this handle. If this handle is invalid in the
    /// specified list or if there is no preceeding node, this method
    /// returns None. This method simply calls
    /// [`LinkedList::next_node()`](../struct.LinkedList.html#method.next_node)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    /// list.push_head(1);
    /// let node = list.push_head(2);
    ///
    /// match node.next_node(&list) {
    ///     None => {},
    ///     Some(n) => assert_eq!(n.val(&list), Some(&1)),
    /// }
    ///
    /// list.pop_tail();
    /// // Once the tail node is popped, there is no next node
    /// assert_eq!(node.next_node(&list), None);
    /// ```
    pub fn next_node(&self, list: &LinkedList<T>) -> Option<Node<T>> {
        list.next_node(self)
    }

    /// Returns a handle to the node immediately preceeding the node
    /// associated with this handle. If this handle is invalid in the
    /// specified list or if there is no preceeding node, this method
    /// returns None. This method simply calls
    /// [`LinkedList::prev_node()`](../struct.LinkedList.html#method.prev_node)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    /// list.push_head(2);
    ///
    /// assert_eq!(node.prev(&list), Some(&2));
    ///
    /// list.pop_head();
    /// //once the head is popped there is no prev node
    /// assert_eq!(node.prev(&list), None);
    /// ```
    pub fn prev_node(&self, list: &LinkedList<T>) -> Option<Node<T>> {
        list.prev_node(self)
    }

    /// Returns a reference to the value of the node associated with
    /// this handle.  If this handle is invalid in the specified list,
    /// this method returns None. This method simply calls
    /// [`LinkedList::node()`](../struct.LinkedList.html#method.node)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    ///
    /// assert_eq!(node.val(&list), Some(&1));
    ///
    /// list.pop_head();
    /// // once the node is popped the handle becomes invalid
    /// assert_eq!(node.val(&list), None);
    /// ```
    pub fn val<'a>(&self, list: &'a LinkedList<T>) -> Option<&'a T> {
        list.node(self)
    }

    /// Returns a mutable reference to the value of the node
    /// associated with this handle.  If this handle is invalid in the
    /// specified list, this method returns None. This method simply
    /// calls
    /// [`LinkedList::node_mut()`](../struct.LinkedList.html#method.node_mut)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    /// let node = list.push_head(1);
    ///
    /// assert_eq!(node.val(&list), Some(&1));
    ///
    /// match node.val_mut(&mut list) {
    ///     None => {},
    ///     Some(x) => *x = 100,
    /// }
    ///
    /// assert_eq!(node.val(&list), Some(&100));
    /// ```
    pub fn val_mut<'a>(&self, list: &'a mut LinkedList<T>) -> Option<&'a mut T> {
        list.node_mut(self)
    }

    /// Removes and returns the value of the node immediately after
    /// the node associated with this handle. If this handle is
    /// invalid in the specified list or there is no next node, then
    /// this method returns None. This method simply calls
    /// [`LinkedList::pop_next()`](../struct.LinkedList.html#method.pop_next)
    ///
    /// This operation should complete in *O*(*1*) time
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    ///
    /// list.push_head(1);
    /// list.push_head(2);
    /// let node = list.push_head(3);
    /// assert_eq!(node.pop_next(&mut list), Some(2));
    /// assert_eq!(node.pop_next(&mut list), Some(1));
    /// assert_eq!(node.pop_next(&mut list), None);
    /// ```
    pub fn pop_next(&self, list: &mut LinkedList<T>) -> Option<T> {
        list.pop_next(self)
    }

    /// Removes and returns the value of the node immediately
    /// preceeding the node associated with this handle. If this
    /// handle is invalid in the specified list or there is no
    /// previous node, then this method returns None. This method
    /// simply calls
    /// [`LinkedList::pop_next()`](../struct.LinkedList.html#method.pop_next)
    ///
    /// This operation should complete in *O*(*1*) time
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    ///
    /// let node = list.push_head(1);
    /// list.push_head(2);
    /// list.push_head(3);
    /// assert_eq!(node.pop_prev(&mut list), Some(2));
    /// assert_eq!(node.pop_prev(&mut list), Some(3));
    /// assert_eq!(node.pop_prev(&mut list), None);
    /// ```
    pub fn pop_prev(&self, list: &mut LinkedList<T>) -> Option<T> {
        list.pop_prev(self)
    }

    /// Removes and returns the value of the node associated with this
    /// handle. If this handle is invalid in the specified list then
    /// this method returns None. This method simply calls
    /// [`LinkedList::pop_node()`](../struct.LinkedList.html#method.pop_node)
    ///
    /// This operation should complete in *O*(*1*) time
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    ///
    /// let node = list.push_head(1);
    /// assert_eq!(node.pop(&mut list), Some(1));
    /// assert_eq!(node.pop(&mut list), None);
    /// ```
    pub fn pop(&self, list: &mut LinkedList<T>) -> Option<T> {
        list.pop_node(self)
    }

    /// Adds an element immediately after the node associated with
    /// this handle. Returns the handle to the node thats been added
    /// or None if this handle is invalid in the specified list. This
    /// method simply calls
    /// [`LinkedList::push_next_()`](../struct.LinkedList.html#method.push_next)
    ///
    /// This operation should complete in *O*(*1*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    ///
    /// list.push_head(0);
    /// let middle = list.push_head(1);
    /// list.push_head(2);
    /// middle.push_next(100, &mut list);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&100));
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn push_next(&self, elem: T, list: &mut LinkedList<T>) -> Option<Node<T>> {
        list.push_next(self, elem)
    }

    /// Adds an element immediately preceedeing the node associated
    /// with this handle. Returns the handle to the node thats been
    /// added or None if this handle is invalid in the specified
    /// list. This method simply calls
    /// [`LinkedList::push_prev_()`](../struct.LinkedList.html#method.push_prev)
    ///
    /// This operation should complete in *O*(*1*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(10);
    ///
    /// list.push_head(0);
    /// let middle = list.push_head(1);
    /// list.push_head(2);
    /// middle.push_prev(100, &mut list);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&100));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn push_prev(&self, elem: T, list: &mut LinkedList<T>) -> Option<Node<T>> {
        list.push_prev(self, elem)
    }

    /// Moves the node associated with this handle to the front (head)
    /// of the list. If the node is already at the head of the list
    /// then this operation has no effect.
    ///
    /// Returns true if the node is successfully moved to the head of
    /// the list (or if it was already at the head) and false if this
    /// handle is invalid in the specified list. This method simply
    /// calls
    /// [`LinkedList::make_head_()`](../struct.LinkedList.html#method.make_head)
    ///
    /// This operation should complete in *O*(*1*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(3);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    ///
    /// assert_eq!(list.head(), Some(&0));
    /// hnd2.make_head(&mut list);
    /// assert_eq!(list.head(), Some(&2));
    /// ```
    pub fn make_head(&self, list: &mut LinkedList<T>) -> bool {
        list.make_head(self)
    }

    /// Moves the node associated with this handle to the back (tail)
    /// of the list. If the node is already at the tail of the list
    /// then this operation has no effect.
    ///
    /// Returns true if the node is successfully moved to the tail of
    /// the list (or if it was already at the tail) and false if this
    /// handle is invalid in the specified list. This method simply
    /// calls
    /// [`LinkedList::make_tail()`](../struct.LinkedList.html#method.make_tail)
    ///
    /// This operation should complete in *O*(*1*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(3);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    ///
    /// assert_eq!(list.tail(), Some(&2));
    /// hnd0.make_tail(&mut list);
    /// assert_eq!(list.tail(), Some(&0));
    /// ```
    pub fn make_tail(&self, list: &mut LinkedList<T>) -> bool {
        list.make_tail(self)
    }

    /// Swaps the position of the node associated with this handle in
    /// the specified list with the position of `other` and returns
    /// true on success. If either node is invalid in the specified
    /// list then this method returns false. This method simply calls
    /// [`LinkedList::swap_node()`](../struct.LinkedList.html#method.swap_node)
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::lists::LinkedList;
    /// let mut list = LinkedList::<u8>::with_capacity(4);
    /// let hnd0 = list.push_tail(0);
    /// let hnd1 = list.push_tail(1);
    /// let hnd2 = list.push_tail(2);
    /// list.pop_tail();
    /// assert_eq!(hnd0.swap_node(&hnd1, &mut list), true);
    /// assert_eq!(hnd1.swap_node(&hnd2, &mut list), false);
    /// assert_eq!(hnd1.is_head(&list), Some(true));
    /// assert_eq!(hnd0.is_tail(&list), Some(true));
    /// ```
    pub fn swap_node(&self, other: &Node<T>, list: &mut LinkedList<T>) -> bool {
        list.swap_node(self, other)
    }
}

#[cfg(test)]
mod test {

    //Test clone
    //Test Default Node<T>
}
