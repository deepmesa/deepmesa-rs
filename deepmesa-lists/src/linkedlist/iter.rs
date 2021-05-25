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
use crate::{linkedlist::list::LinkedList, linkedlist::node::Node};

#[derive(Debug)]
enum IterDirection {
    HeadToTail,
    TailToHead,
}

/// A bidirectional iterator over the nodes of the
/// [`LinkedList`](LinkedList).
///
/// This struct is created by the [`.iter()`](LinkedList#method.iter)
/// of the [`LinkedList`](LinkedList).
///
/// # Examples
/// ```
/// use deepmesa::lists::LinkedList;
/// use deepmesa::lists::linkedlist::Iter;
///
/// let mut list = LinkedList::<u8>::new();
/// list.push_front(1);
/// list.push_front(2);
/// list.push_front(3);
/// list.push_front(4);
/// list.push_front(5);
///
/// let mut iter:Iter<u8> = list.iter();
/// assert_eq!(iter.next(), Some(&5));
/// assert_eq!(iter.next(), Some(&4));
/// assert_eq!(iter.next(), Some(&3));
/// iter = iter.reverse();
/// assert_eq!(iter.next(), Some(&4));
/// assert_eq!(iter.next(), Some(&5));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Debug)]
pub struct Iter<'a, T> {
    list: &'a LinkedList<T>,
    cursor: Option<Node<T>>,
    dir: IterDirection,
}

/// A bidirectional iterator over the node of the [`LinkedList`] with
/// mutable references that allows the value to be modified.
///
/// This struct is created by the
/// [`.iter_mut()`](LinkedList#method.iter_mut) method of the
/// [`LinkedList`](LinkedList).
///
/// # Examples
/// ```
/// use deepmesa::lists::LinkedList;
/// use deepmesa::lists::linkedlist::IterMut;
/// use deepmesa::lists::linkedlist::Iter;
///
/// let mut list = LinkedList::<u8>::new();
/// list.push_front(1);
/// list.push_front(2);
/// list.push_front(3);
///
/// let mut iter_mut: IterMut<u8> = list.iter_mut();
/// for e in iter_mut {
///     *e += 100;
/// }
///
/// let mut iter:Iter<u8> = list.iter();
/// assert_eq!(iter.next(), Some(&103));
/// assert_eq!(iter.next(), Some(&102));
/// assert_eq!(iter.next(), Some(&101));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Debug)]
pub struct IterMut<'a, T> {
    list: &'a mut LinkedList<T>,
    cursor: Option<Node<T>>,
    dir: IterDirection,
}

macro_rules! iter_reverse {
    ($self: ident) => {
        /// Reverses the direction of the iterator
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
    pub(crate) fn new(list: &'a LinkedList<T>) -> Iter<T> {
        Iter {
            list,
            cursor: list.head_node(),
            dir: IterDirection::HeadToTail,
        }
    }

    iter_reverse!(self);
}

impl<'a, T> IterMut<'a, T> {
    pub(crate) fn new(list: &'a mut LinkedList<T>) -> IterMut<T> {
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
