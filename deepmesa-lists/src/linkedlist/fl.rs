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
use crate::linkedlist::node::InternalNode;
extern crate alloc;

use alloc::{alloc::alloc, alloc::dealloc, alloc::Layout};
use core::ptr;

#[derive(Debug)]
pub(super) struct FreeList<T> {
    capacity: usize,
    len: usize,
    head: *mut InternalNode<T>,
    tail: *mut InternalNode<T>,
}

impl<T> Drop for FreeList<T> {
    fn drop(&mut self) {
        let mut cur = self.tail;
        while !cur.is_null() {
            cur = self.pop_tail();
            unsafe {
                let layout = Layout::new::<InternalNode<T>>();
                dealloc(cur as *mut u8, layout);
            }
            cur = self.tail;
        }
    }
}

impl<T> FreeList<T> {
    pub(super) fn new(capacity: usize) -> FreeList<T> {
        let mut fl = FreeList {
            capacity: capacity,
            len: 0,
            head: ptr::null_mut(),
            tail: ptr::null_mut(),
        };
        fl.alloc(capacity);
        fl
    }

    pub(super) fn len(&self) -> usize {
        self.len
    }

    fn alloc(&mut self, size: usize) {
        let layout = Layout::new::<InternalNode<T>>();

        let mut count: usize = 0;
        unsafe {
            while count < size {
                let ptr: *mut InternalNode<T> = alloc(layout) as *mut InternalNode<T>;
                self.push_head(ptr);
                count += 1;
            }
        }
    }

    fn push_head(&mut self, ptr: *mut InternalNode<T>) {
        unsafe {
            (*ptr).prev = ptr::null_mut();
            if self.head.is_null() {
                (*ptr).next = ptr::null_mut();
            } else {
                (*self.head).prev = ptr;
                (*ptr).next = self.head;
            }
            if self.tail.is_null() {
                self.tail = ptr;
            }

            self.len += 1;
            self.head = ptr;
        }
    }

    fn pop_tail(&mut self) -> *mut InternalNode<T> {
        if self.tail.is_null() {
            return ptr::null_mut();
        }
        unsafe {
            let ptr: *mut InternalNode<T>;
            if !(*self.tail).prev.is_null() {
                (*(*self.tail).prev).next = ptr::null_mut();
            }
            ptr = self.tail;
            if self.head == ptr {
                self.head = ptr::null_mut();
            }
            self.tail = (*self.tail).prev;
            (*ptr).next = ptr::null_mut();
            (*ptr).prev = ptr::null_mut();
            self.len -= 1;
            ptr
        }
    }

    pub(super) fn release(&mut self, ptr: *mut InternalNode<T>) -> T {
        unsafe {
            let node = ptr::read(ptr);
            (*ptr).next = ptr::null_mut();
            (*ptr).prev = ptr::null_mut();
            (*ptr).fl_node = true;
            self.push_head(ptr);
            node.val
        }
    }

    pub(super) fn acquire(&mut self, val: T, nid: usize) -> *mut InternalNode<T> {
        let mut ptr = self.pop_tail();
        if ptr.is_null() {
            self.grow();
            ptr = self.pop_tail();
            if ptr.is_null() {
                panic!("alloc failed on acquire");
            }
        }

        let node = InternalNode::new(val, nid);
        unsafe {
            ptr::write(ptr, node);
        }
        ptr
    }

    fn grow(&mut self) {
        if self.capacity == 0 {
            self.alloc(1);
        } else {
            self.alloc(self.capacity);
            self.capacity *= 2;
        }
    }
}
