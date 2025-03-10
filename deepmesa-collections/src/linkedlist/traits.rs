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

use crate::linkedlist::list::DropPolicy;
use crate::linkedlist::list::LinkedList;
use crate::linkedlist::node::InternalNode;

unsafe impl<T> Send for LinkedList<T> {}
unsafe impl<T> Sync for LinkedList<T> {}

impl<T> Drop for LinkedList<T> {
    fn drop(&mut self) {
        let mut cur: *mut InternalNode<T> = self.head;
        //Create a Vec to store the items so that we don't leak memory
        // if the Drop implementation of any of the elements of the
        // LinkedList panics.
        match self.drop_policy {
            DropPolicy::None => {
                while !cur.is_null() {
                    let node = self.pop_ptr(cur);
                    cur = self.head;
                }
            }
            DropPolicy::PanicSafe => {
                let mut node_vec = Vec::with_capacity(self.len());
                while !cur.is_null() {
                    let node = self.pop_ptr(cur);
                    node_vec.push(node);
                    cur = self.head;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {

    #[derive(Debug)]
    struct Foo {
        val: u8,
    }

    impl Drop for Foo {
        fn drop(&mut self) {
            if self.val == 5 {
                panic!("DING Panic drop val = {:?}", self.val);
            //                println!("DING Dropping foo val={:?}", self.val);
            } else {
                println!("DING Dropping foo val={:?}", self.val);
            }
        }
    }

    use crate::linkedlist::list::*;

    #[test]
    fn test_drop_panic() {
        let mut ll = LinkedList::<Foo>::new();
        for i in 0..10 {
            ll.push_head(Foo { val: i });
        }

        println!("LL={:?}", ll);
    }
}
