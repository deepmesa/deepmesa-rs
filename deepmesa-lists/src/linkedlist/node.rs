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

use crate::linkedlist::list::FastLinkedList;
use core::ptr;

#[derive(Debug, PartialEq, Eq)]
pub(super) struct InternalNode<T> {
    pub(super) val: T,
    pub(super) fl_node: bool,
    pub(super) nid: usize,
    pub(super) prev: *mut InternalNode<T>,
    pub(super) next: *mut InternalNode<T>,
}

/// A handle to a node in the [`FastLinkedList`](../struct.FastLinkedList.html).
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
/// [`push_head()`](../struct.FastLinkedList.html#method.push_head),
/// [`push_tail()`](../struct.FastLinkedList.html#method.push_tail),
/// [`push_next()`](../struct.FastLinkedList.html#method.push_next)
/// and
/// [`push_prev()`](../struct.FastLinkedList.html#method.push_prev)
/// methods of [`FastLinkedList`](../struct.FastLinkedList.html)
/// return handles to the nodes pushed to the linked list. Handles can
/// only be used by passing them as arguments to the
/// [`next()`](../struct.FastLinkedList.html#method.next),
/// [`next_mut()`](../struct.FastLinkedList.html#method.next_mut),
/// [`prev()`](../struct.FastLinkedList.html#method.prev),
/// [`prev_mut()`](../struct.FastLinkedList.html#method.prev_mut),
/// [`prev_node()`](../struct.FastLinkedList.html#method.prev_node),
/// [`next_node()`](../struct.FastLinkedList.html#method.next_node),
/// [`node()`](../struct.FastLinkedList.html#method.node),
/// [`node_mut()`](../struct.FastLinkedList.html#method.node_mut),
/// [`has_next()`](../struct.FastLinkedList.html#method.has_next),
/// [`has_prev()`](../struct.FastLinkedList.html#method.has_prev),
/// [`pop_next()`](../struct.FastLinkedList.html#method.pop_next),
/// [`pop_prev()`](../struct.FastLinkedList.html#method.pop_prev),
/// [`pop_node()`](../struct.FastLinkedList.html#method.pop_node),
/// [`push_next()`](../struct.FastLinkedList.html#method.push_next),
/// [`push_prev()`](../struct.FastLinkedList.html#method.push_prev),
/// methods of the list. This allows adding, removing and mutating
/// elements in the middle of the list in O(1) time.

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

    pub fn is_head(&self, list: &FastLinkedList<T>) -> Option<bool> {
        list.is_head(self)
    }

    pub fn is_tail(&self, list: &FastLinkedList<T>) -> Option<bool> {
        list.is_tail(self)
    }

    pub fn is_prev(&self, other: &Node<T>, list: &FastLinkedList<T>) -> Option<bool> {
        list.is_prev(self, other)
    }

    pub fn is_next(&self, other: &Node<T>, list: &FastLinkedList<T>) -> Option<bool> {
        list.is_next(self, other)
    }

    pub fn has_next(&self, list: &FastLinkedList<T>) -> Option<bool> {
        list.has_next(self)
    }

    pub fn has_prev(&self, list: &FastLinkedList<T>) -> Option<bool> {
        list.has_prev(self)
    }

    pub fn next<'a>(&self, list: &'a FastLinkedList<T>) -> Option<&'a T> {
        list.next(self)
    }

    pub fn prev<'a>(&self, list: &'a FastLinkedList<T>) -> Option<&'a T> {
        list.prev(self)
    }

    pub fn next_mut<'a>(&self, list: &'a mut FastLinkedList<T>) -> Option<&'a mut T> {
        list.next_mut(self)
    }

    pub fn prev_mut<'a>(&self, list: &'a mut FastLinkedList<T>) -> Option<&'a mut T> {
        list.prev_mut(self)
    }

    pub fn next_node(&self, list: &FastLinkedList<T>) -> Option<Node<T>> {
        list.next_node(self)
    }

    pub fn prev_node(&self, list: &FastLinkedList<T>) -> Option<Node<T>> {
        list.prev_node(self)
    }

    pub fn val<'a>(&self, list: &'a FastLinkedList<T>) -> Option<&'a T> {
        list.node(self)
    }

    pub fn val_mut<'a>(&self, list: &'a mut FastLinkedList<T>) -> Option<&'a mut T> {
        list.node_mut(self)
    }

    pub fn pop_next(&self, list: &mut FastLinkedList<T>) -> Option<T> {
        list.pop_next(self)
    }

    pub fn pop_prev(&self, list: &mut FastLinkedList<T>) -> Option<T> {
        list.pop_prev(self)
    }

    pub fn pop(&self, list: &mut FastLinkedList<T>) -> Option<T> {
        list.pop_node(self)
    }

    pub fn push_next(&self, elem: T, list: &mut FastLinkedList<T>) -> Option<Node<T>> {
        list.push_next(self, elem)
    }

    pub fn push_prev(&self, elem: T, list: &mut FastLinkedList<T>) -> Option<Node<T>> {
        list.push_prev(self, elem)
    }

    pub fn make_head(&self, list: &mut FastLinkedList<T>) -> bool {
        list.make_head(self)
    }

    pub fn make_tail(&self, list: &mut FastLinkedList<T>) -> bool {
        list.make_tail(self)
    }

    pub fn swap_node(&self, other: &Node<T>, list: &mut FastLinkedList<T>) -> bool {
        list.swap_node(self, other)
    }
}

#[cfg(test)]
mod test {

    //Test clone
    //Test Default Node<T>
}
