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

use std::ptr;

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
/// the `Deref` trait so you cannot dereference that pointer directly.
/// Handles can be used only by methods of the linkedlist that they
/// were obtained from. They can be copied and passed around by value
/// regardless of the lifetime of the linkedlist. Once the element
/// that the handle refers to is removed from the linked list, the
/// handle then becomes invalid. Passing an invalid handle into the
/// linked list is safe since all methods that accept a reference to a
/// handle return `None` if the handle is invalid.
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
}

#[cfg(test)]
mod test {

    //Test clone
    //Test Default Node<T>
}
