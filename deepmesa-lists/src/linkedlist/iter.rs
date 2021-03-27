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
use crate::{linkedlist::list::FastLinkedList, linkedlist::node::Node};

#[derive(Debug)]
enum IterDirection {
    HeadToTail,
    TailToHead,
}

#[derive(Debug)]
pub struct Iter<'a, T> {
    list: &'a FastLinkedList<T>,
    cursor: Option<Node<T>>,
    dir: IterDirection,
}

pub struct IterMut<'a, T> {
    list: &'a mut FastLinkedList<T>,
    cursor: Option<Node<T>>,
    dir: IterDirection,
}

macro_rules! iter_reverse {
    ($self: ident) => {
        pub fn reverse(mut $self) -> Self {
            match &$self.cursor {
                None => match $self.dir {
                    IterDirection::HeadToTail => {
                        $self.dir = IterDirection::TailToHead;
                        $self.cursor = $self.list.tail_node();
                    }
                    IterDirection::TailToHead => {
                        $self.dir = IterDirection::HeadToTail;
                        $self.cursor = $self.list.head_node();
                    }
                },
                Some(node) => match $self.dir {
                    IterDirection::HeadToTail => {
                        if node.ptr == $self.list.head {
                            $self.cursor = $self.list.tail_node();
                        } else {
                            $self.cursor = $self.list.prev_node(&node);
                            if !$self.cursor.is_none() {
                                $self.cursor = $self.list.prev_node(&$self.cursor.unwrap());
                            }
                        }
                        $self.dir = IterDirection::TailToHead;
                    }
                    IterDirection::TailToHead => {
                        if node.ptr == $self.list.tail {
                            $self.cursor = $self.list.head_node();
                        }  else {
                            $self.cursor = $self.list.next_node(&node);
                            if !$self.cursor.is_none() {
                                $self.cursor = $self.list.next_node(&$self.cursor.unwrap());
                            }
                        }
                        $self.dir = IterDirection::HeadToTail;
                    }
                },
            }
            $self
        }
    };
}

impl<'a, T> Iter<'a, T> {
    pub(crate) fn new(list: &'a FastLinkedList<T>) -> Iter<T> {
        Iter {
            list,
            cursor: list.head_node(),
            dir: IterDirection::HeadToTail,
        }
    }

    iter_reverse!(self);
    // pub fn reverse(mut self) -> Self {
    //     match &self.cursor {
    //         None => match self.dir {
    //             IterDirection::HeadToTail => {
    //                 self.dir = IterDirection::TailToHead;
    //                 self.cursor = self.list.tail_node();
    //             }
    //             IterDirection::TailToHead => {
    //                 self.dir = IterDirection::HeadToTail;
    //                 self.cursor = self.list.head_node();
    //             }
    //         },
    //         Some(node) => match self.dir {
    //             IterDirection::HeadToTail => {
    //                 if node.ptr == self.list.head {
    //                     self.cursor = self.list.tail_node();
    //                 } else {
    //                     self.cursor = self.list.prev_node(&node);
    //                     if !self.cursor.is_none() {
    //                         self.cursor = self.list.prev_node(&self.cursor.unwrap());
    //                     }
    //                 }
    //                 self.dir = IterDirection::TailToHead;
    //             }
    //             IterDirection::TailToHead => {
    //                 if node.ptr == self.list.tail {
    //                     self.cursor = self.list.head_node();
    //                 } else {
    //                     self.cursor = self.list.next_node(&node);
    //                     if !self.cursor.is_none() {
    //                         self.cursor = self.list.next_node(&self.cursor.unwrap());
    //                     }
    //                 }
    //                 self.dir = IterDirection::HeadToTail;
    //             }
    //         },
    //     }
    //     self
    // }
}

impl<'a, T> IterMut<'a, T> {
    pub(crate) fn new(list: &'a mut FastLinkedList<T>) -> IterMut<T> {
        IterMut {
            cursor: list.head_node(),
            list,
            dir: IterDirection::HeadToTail,
        }
    }

    iter_reverse!(self);
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        match &self.cursor {
            None => None,
            Some(cur) => {
                let node_ptr = cur.ptr;
                match self.dir {
                    IterDirection::HeadToTail => {
                        self.cursor = self.list.next_node(&cur);
                    }
                    IterDirection::TailToHead => {
                        self.cursor = self.list.prev_node(&cur);
                    }
                }
                unsafe { Some(&(*node_ptr).val) }
            }
        }
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;
    fn next(&mut self) -> Option<&'a mut T> {
        match &mut self.cursor {
            None => None,
            Some(cur) => {
                let node_ptr = cur.ptr;
                match self.dir {
                    IterDirection::HeadToTail => {
                        self.cursor = self.list.next_node(&cur);
                    }
                    IterDirection::TailToHead => {
                        self.cursor = self.list.prev_node(&cur);
                    }
                }
                unsafe { Some(&mut (*node_ptr).val) }
            }
        }
    }
}
