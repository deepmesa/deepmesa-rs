/*
   CircularDeque: A Double Ended Queue circular implementation backed
   by contiguous memory

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
pub use crate::cdeque::iter::{Drain, IntoIter, Iter, IterMut};

extern crate alloc;
use crate::cdeque::macros::*;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::dealloc;
use alloc::alloc::Layout;
use core::ptr;
use std::fmt::Debug;
use std::ptr::null_mut;

/// A convenience macro for creating a `CircularDeque` from a list of elements.
///
/// # Examples
///
/// Create an empty CircularDeque
///
/// ```
/// # use deepmesa_collections::CircularDeque;
/// # use deepmesa_collections::deque::cdeque;
/// let mut empty_cdq = cdeque!();
///
/// assert_eq!(empty_cdq.len(), 0);
/// empty_cdq.push_back(1);
/// empty_cdq.push_back(2);
/// empty_cdq.push_back(3);
/// assert_eq!(empty_cdq.len(), 3);
/// assert_eq!(empty_cdq.get(0), Some(&1));
/// assert_eq!(empty_cdq.get(1), Some(&2));
/// assert_eq!(empty_cdq.get(2), Some(&3));
/// ```
/// Create a Circular Deque initialized with 3 elements
///
/// ```
/// # use deepmesa_collections::CircularDeque;
/// # use deepmesa_collections::deque::cdeque;
/// let mut cdq = cdeque!(1, 2, 3);
///
/// assert_eq!(cdq.len(), 3);
/// assert_eq!(cdq.get(0), Some(&1));
/// assert_eq!(cdq.get(1), Some(&2));
/// assert_eq!(cdq.get(2), Some(&3));
/// ```
#[macro_export]
macro_rules! cdeque {
    () => {
        CircularDeque::new()
    };
    ($($x:literal),+) => {
        CircularDeque::from_slice(&[$($x,)*][..])
    };
}

/// A circular double-ended queue (deque) implemented with a growable ring buffer.
///
/// This data structure allows for efficient insertion and removal at both ends,
/// with O(1) push/pop operations at the front and back. The implementation uses
/// a contiguous block of memory with circular indexing for optimal performance.
///
/// # Examples
///
/// ```
/// # use deepmesa_collections::CircularDeque;
/// let mut deque = CircularDeque::new();
/// deque.push_back(1);
/// deque.push_back(2);
/// deque.push_front(0);
///
/// assert_eq!(deque.len(), 3);
/// assert_eq!(deque.front(), Some(&0));
/// assert_eq!(deque.back(), Some(&2));
///
/// assert_eq!(deque.pop_front(), Some(0));
/// assert_eq!(deque.pop_back(), Some(2));
/// ```
pub struct CircularDeque<T> {
    pub(in crate::cdeque) len: usize,
    pub(in crate::cdeque) capacity: usize,
    pub(in crate::cdeque) p_idxz: *mut T,
    pub(in crate::cdeque) p_idxc: *mut T,
    pub(in crate::cdeque) p_head: *mut T,
    pub(in crate::cdeque) p_tail: *mut T,
}

/*
Head: Head points to the element that is at the front of the queue
Tail: Tail points to the first empty element in the queue. i.e. the
(empty) element after the last element in the queue.

push_back(): push_tail: write the element and increment tail
pop_front(): pop_head:  read the element and increment head

push_front(): push_head: decrement head and write element
pop_back(): pop_tail: decrement tail and read element

tail: *mut T points to an empty slot
head: *mut T points to the first element in the queue

first element of the allocation: queue
last element of the allocation: queue.add(capacity)

// POINTERS vs INDEXES: If we store usize indexes then on every push we
have to do one addition to find the index to write to, Then a second
addition to increment the index.

If we store pointers then we have to do only one addition to update the pointer

BlogPost: the Devil is in the details - a post about how the details
matter ex: the circular buffer in a contiguous deque

Rules:

1. if the queue is empty: p_head == p_tail
2. else if the queue is full:  p_head == p_tail
3. else p_tail = p_head + len
4. ALWAYS: p_idxc = p_idxz + cap - 1
*/

macro_rules! dec_ptr {
    ($self:ident, $ptr:expr) => {
        if $ptr == $self.p_idxz {
            $ptr = $self.p_idxc;
        } else {
            unsafe {
                $ptr = $ptr.sub(1);
            }
        }
    };
}

macro_rules! inc_ptr {
    ($self:ident, $ptr:expr) => {
        if $ptr == $self.p_idxc {
            $ptr = $self.p_idxz;
        } else {
            unsafe {
                $ptr = $ptr.add(1);
            }
        }
    };
}

macro_rules! inc_head {
    ($self:ident) => {
        inc_ptr!($self, $self.p_head);
    };
}

macro_rules! dec_head {
    ($self:ident) => {
        dec_ptr!($self, $self.p_head);
    };
}

macro_rules! inc_tail {
    ($self:ident) => {
        inc_ptr!($self, $self.p_tail);
    };
}

macro_rules! dec_tail {
    ($self:ident) => {
        dec_ptr!($self, $self.p_tail);
    };
}

impl<T> CircularDeque<T> {
    /// Creates an iterator that covers the specified range in the deque.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or
    /// if the end point is greater than the length of the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    /// deque.push_back(5);
    ///
    /// let values: Vec<&i32> = deque.range(1..4).collect();
    /// assert_eq!(values, vec![&2, &3, &4]);
    /// ```
    pub fn range<R>(&self, range: R) -> Iter<'_, T>
    where
        R: std::ops::RangeBounds<usize>,
    {
        use std::ops::Bound;

        let start = match range.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n + 1,
            Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            Bound::Included(&n) => n + 1,
            Bound::Excluded(&n) => n,
            Bound::Unbounded => self.len(),
        };

        if start > end {
            panic!(
                "range start is greater than end: start={}, end={}",
                start, end
            );
        }

        if end > self.len() {
            panic!(
                "range end is greater than length: end={}, len={}",
                end,
                self.len()
            );
        }

        Iter::new_range(self, start, end)
    }

    /// Creates a mutable iterator that covers the specified range in the deque.
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or
    /// if the end point is greater than the length of the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    /// deque.push_back(5);
    ///
    /// for item in deque.range_mut(1..4) {
    ///     *item *= 2;
    /// }
    ///
    /// let values: Vec<&i32> = deque.iter().collect();
    /// assert_eq!(values, vec![&1, &4, &6, &8, &5]);
    /// ```
    pub fn range_mut<R>(&mut self, range: R) -> IterMut<'_, T>
    where
        R: std::ops::RangeBounds<usize>,
    {
        use std::ops::Bound;

        let start = match range.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n + 1,
            Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            Bound::Included(&n) => n + 1,
            Bound::Excluded(&n) => n,
            Bound::Unbounded => self.len(),
        };

        if start > end {
            panic!(
                "range start is greater than end: start={}, end={}",
                start, end
            );
        }

        if end > self.len() {
            panic!(
                "range end is greater than length: end={}, len={}",
                end,
                self.len()
            );
        }

        IterMut::new_range(self, start, end)
    }

    /// Shrinks the capacity of the deque as much as possible.
    ///
    /// It will drop down as close as possible to the length but the allocator may still inform the
    /// deque that there is space for a few more elements.
    ///
    /// This method is useful for freeing up memory when you know the deque won't grow further.
    /// It's particularly beneficial after operations that may have reserved more capacity than
    /// needed, such as `reserve()` or after removing many elements.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// // Reserve extra capacity
    /// deque.reserve(100);
    /// assert!(deque.capacity() >= 103);
    ///
    /// // Shrink to fit the actual length
    /// deque.shrink_to_fit();
    /// assert_eq!(deque.capacity(), 3);
    /// assert_eq!(deque.len(), 3);
    /// ```
    ///
    /// Empty deques will have their capacity reduced to zero:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::<i32>::with_capacity(10);
    /// assert_eq!(deque.capacity(), 10);
    /// assert_eq!(deque.len(), 0);
    ///
    /// deque.shrink_to_fit();
    /// assert_eq!(deque.capacity(), 0);
    /// assert_eq!(deque.len(), 0);
    /// ```
    ///
    /// If the capacity already equals the length, this operation is a no-op:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// let original_capacity = deque.capacity();
    /// deque.shrink_to_fit();
    /// assert_eq!(deque.capacity(), original_capacity);
    /// ```
    ///
    pub fn shrink_to_fit(&mut self) {
        if self.capacity > self.len {
            let new_capacity = if self.len == 0 { 0 } else { self.len };

            if new_capacity == 0 {
                // If length is 0, deallocate completely
                if self.capacity > 0 {
                    Self::dealloc(self.p_idxz, self.capacity);
                    self.capacity = 0;
                    self.p_idxz = ptr::null_mut();
                    self.p_idxc = ptr::null_mut();
                    self.p_head = ptr::null_mut();
                    self.p_tail = ptr::null_mut();
                }
            } else {
                // Reallocate with smaller capacity
                let new_mem = Self::alloc(new_capacity);
                unsafe {
                    self.rebase(new_mem, new_capacity);
                }
            }
        }
    }

    /// Shrinks the capacity of the deque with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// If the current capacity is less than or equal to the lower limit, this is a no-op.
    /// This method is useful when you want to free memory while ensuring a minimum capacity
    /// for future operations.
    ///
    /// # Arguments
    ///
    /// * `min_capacity` - The minimum capacity to maintain
    ///
    /// # Examples
    ///
    /// Shrinking to a specific capacity:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// // Reserve extra capacity
    /// deque.reserve(100);
    /// assert!(deque.capacity() >= 103);
    ///
    /// // Shrink to a minimum of 10
    /// deque.shrink_to(10);
    /// assert_eq!(deque.capacity(), 10);
    /// assert_eq!(deque.len(), 3);
    /// ```
    ///
    /// The capacity will not shrink below the current length:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    /// deque.push_back(5);
    ///
    /// // Reserve extra capacity
    /// deque.reserve(20);
    /// assert!(deque.capacity() >= 25);
    ///
    /// // Try to shrink to 3, but capacity will be 5 (current length)
    /// deque.shrink_to(3);
    /// assert_eq!(deque.capacity(), 5);
    /// assert_eq!(deque.len(), 5);
    /// ```
    ///
    /// Empty deques can be shrunk to any capacity:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::<i32>::with_capacity(50);
    /// assert_eq!(deque.capacity(), 50);
    /// assert_eq!(deque.len(), 0);
    ///
    /// // Shrink to 10
    /// deque.shrink_to(10);
    /// assert_eq!(deque.capacity(), 10);
    /// assert_eq!(deque.len(), 0);
    ///
    /// // Shrink to 0
    /// deque.shrink_to(0);
    /// assert_eq!(deque.capacity(), 0);
    /// assert_eq!(deque.len(), 0);
    /// ```
    ///
    /// If the current capacity is already at or below the minimum, this is a no-op:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// let original_capacity = deque.capacity();
    /// deque.shrink_to(20);
    /// assert_eq!(deque.capacity(), original_capacity);
    /// ```
    ///
    pub fn shrink_to(&mut self, min_capacity: usize) {
        let new_capacity = std::cmp::max(self.len, min_capacity);

        if self.capacity > new_capacity {
            if new_capacity == 0 {
                // If new capacity is 0, deallocate completely
                if self.capacity > 0 {
                    Self::dealloc(self.p_idxz, self.capacity);
                    self.capacity = 0;
                    self.p_idxz = ptr::null_mut();
                    self.p_idxc = ptr::null_mut();
                    self.p_head = ptr::null_mut();
                    self.p_tail = ptr::null_mut();
                }
            } else {
                // Reallocate with smaller capacity
                let new_mem = Self::alloc(new_capacity);
                unsafe {
                    self.rebase(new_mem, new_capacity);
                }
            }
        }
    }

    /// Returns the index of the partition point according to the given predicate
    /// (the index of the first element of the second partition).
    ///
    /// The deque is assumed to be partitioned according to the given predicate.
    /// This means that all elements for which the predicate returns true are at the start of the deque
    /// and all elements for which the predicate returns false are at the end.
    /// For example, `[7, 15, 3, 5, 4, 12, 6]` is partitioned under the predicate `x % 2 != 0`
    /// (all odd numbers are at the start, all even at the end).
    ///
    /// If the deque is not partitioned, the returned result is unspecified and meaningless,
    /// as this method performs a kind of binary search.
    ///
    /// See also [`binary_search`], [`binary_search_by`], and [`binary_search_by_key`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(3);
    /// deque.push_back(5);
    /// deque.push_back(6);
    /// deque.push_back(7);
    ///
    /// let i = deque.partition_point(|&x| x < 5);
    /// assert_eq!(i, 4);
    /// assert!(deque.iter().take(i).all(|&x| x < 5));
    /// assert!(deque.iter().skip(i).all(|&x| !(x < 5)));
    /// ```
    ///
    /// If all elements of the deque match the predicate, including if the deque
    /// is empty, then the length of the deque is returned:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(2);
    /// deque.push_back(4);
    /// deque.push_back(8);
    /// assert_eq!(deque.partition_point(|&x| x < 100), 3);
    ///
    /// let empty_deque: CircularDeque<i32> = CircularDeque::new();
    /// assert_eq!(empty_deque.partition_point(|&x| x < 100), 0);
    /// ```
    ///
    /// If no elements of the deque match the predicate, then 0 is returned:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(2);
    /// deque.push_back(4);
    /// deque.push_back(8);
    /// assert_eq!(deque.partition_point(|&x| x > 100), 0);
    /// ```
    ///
    /// [`binary_search`]: CircularDeque::binary_search
    /// [`binary_search_by`]: CircularDeque::binary_search_by
    /// [`binary_search_by_key`]: CircularDeque::binary_search_by_key
    pub fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&T) -> bool,
    {
        let mut left = 0;
        let mut right = self.len();

        while left < right {
            let mid = left + (right - left) / 2;

            // Get the element at the mid position
            let element = unsafe { &*self.ptr_at(mid) };

            if pred(element) {
                left = mid + 1;
            } else {
                right = mid;
            }
        }

        left
    }

    /// Removes the specified range from the deque in bulk, returning all
    /// removed elements as an iterator. If the iterator is dropped before
    /// being fully consumed, it drops the remaining removed elements.
    ///
    /// The returned iterator keeps a mutable borrow on the queue to optimize
    /// its implementation.
    ///
    /// # Arguments
    ///
    /// * `range` - The range of elements to drain. Can be any type that implements `RangeBounds<usize>`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    /// deque.push_back(5);
    ///
    /// let drained: Vec<i32> = deque.drain(1..4).collect();
    /// assert_eq!(drained, vec![2, 3, 4]);
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[1], 5);
    /// ```
    ///
    /// Draining all elements:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// let drained: Vec<i32> = deque.drain(..).collect();
    /// assert_eq!(drained, vec![1, 2, 3]);
    /// assert_eq!(deque.len(), 0);
    /// ```
    ///
    /// Draining from the front:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    ///
    /// let drained: Vec<i32> = deque.drain(..2).collect();
    /// assert_eq!(drained, vec![1, 2]);
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque[0], 3);
    /// assert_eq!(deque[1], 4);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the starting point is greater than the end point or if
    /// the end point is greater than the length of the deque.
    ///
    /// # Leaking
    ///
    /// If the returned iterator goes out of scope without being dropped (due to
    /// [`mem::forget`], for example), the deque may have lost and leaked
    /// elements arbitrarily, including elements outside the range.
    ///
    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T>
    where
        R: std::ops::RangeBounds<usize>,
    {
        use std::ops::Bound;
        let start = match range.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n + 1,
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(&n) => n + 1,
            Bound::Excluded(&n) => n,
            Bound::Unbounded => self.len,
        };

        if start > end {
            panic!("range start is greater than range end");
        }
        if end > self.len {
            panic!("range end is greater than length");
        }

        Drain::new(self, start, end)
    }

    /// Splits the deque into two at the given index.
    ///
    /// Returns a newly allocated deque containing the elements in the range
    /// `[at, len)`. After the call, the original deque will be left containing
    /// the elements `[0, at)` with its previous capacity unchanged.
    ///
    /// # Arguments
    ///
    /// * `at` - The index at which to split the deque
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    /// deque.push_back(5);
    ///
    /// let split_deque = deque.split_off(2);
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[1], 2);
    ///
    /// assert_eq!(split_deque.len(), 3);
    /// assert_eq!(split_deque[0], 3);
    /// assert_eq!(split_deque[1], 4);
    /// assert_eq!(split_deque[2], 5);
    /// ```
    ///
    /// Splitting at the beginning:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// let split_deque = deque.split_off(0);
    /// assert_eq!(deque.len(), 0);
    /// assert_eq!(split_deque.len(), 3);
    /// assert_eq!(split_deque[0], 1);
    /// assert_eq!(split_deque[1], 2);
    /// assert_eq!(split_deque[2], 3);
    /// ```
    ///
    /// Splitting at the end:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// let split_deque = deque.split_off(3);
    /// assert_eq!(deque.len(), 3);
    /// assert_eq!(split_deque.len(), 0);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[1], 2);
    /// assert_eq!(deque[2], 3);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    pub fn split_off(&mut self, at: usize) -> Self {
        if at > self.len {
            panic!("split index {} is greater than length {}", at, self.len);
        }

        if at == 0 {
            // Split at the beginning - return the entire deque and clear self
            let mut new_deque = Self::new();
            std::mem::swap(self, &mut new_deque);
            return new_deque;
        }

        if at == self.len {
            // Split at the end - return empty deque
            return Self::new();
        }

        // Create a new deque with the split-off elements
        let split_len = self.len - at;
        let mut new_deque = Self::with_capacity(split_len);

        // Copy elements from at to end into the new deque
        for i in at..self.len {
            unsafe {
                let ptr = self.ptr_at(i);
                let value = std::ptr::read(ptr);
                new_deque.push_back(value);
            }
        }

        // Truncate the original deque at the split point
        self.truncate(at);

        new_deque
    }

    /// Modifies the deque in-place so that len() is equal to new_len,
    /// either by removing excess elements from the back or by
    /// appending elements generated by calling the closure to the back.
    ///
    /// # Arguments
    ///
    /// * `new_len` - The new length of the deque
    /// * `generator` - A closure that will be called to generate new elements
    ///
    /// # Examples
    ///
    /// Growing the deque with a generator function:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// let mut counter = 10;
    /// deque.resize_with(5, || {
    ///     counter += 1;
    ///     counter
    /// });
    ///
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[1], 2);
    /// assert_eq!(deque[2], 11);
    /// assert_eq!(deque[3], 12);
    /// assert_eq!(deque[4], 13);
    /// ```
    ///
    /// Shrinking the deque (generator is not called):
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    ///
    /// deque.resize_with(2, || panic!("Should not be called"));
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[1], 2);
    /// ```
    ///
    /// Using a generator that produces different values:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back("hello".to_string());
    ///
    /// let mut index = 0;
    /// deque.resize_with(4, || {
    ///     let result = format!("item_{}", index);
    ///     index += 1;
    ///     result
    /// });
    ///
    /// assert_eq!(deque.len(), 4);
    /// assert_eq!(deque[0], "hello");
    /// assert_eq!(deque[1], "item_0");
    /// assert_eq!(deque[2], "item_1");
    /// assert_eq!(deque[3], "item_2");
    /// ```
    pub fn resize_with<F>(&mut self, new_len: usize, mut generator: F)
    where
        F: FnMut() -> T,
    {
        if new_len > self.len {
            // Need to grow - append elements generated by calling the closure
            let additional = new_len - self.len;
            self.reserve(additional);

            for _ in 0..additional {
                self.push_back(generator());
            }
        } else if new_len < self.len {
            // Need to shrink - remove elements from the back
            self.truncate(new_len);
        }
        // If new_len == self.len, do nothing
    }

    /// Creates a new empty circular deque.
    ///
    /// This does not allocate any memory. The deque will only allocate
    /// memory when elements are first inserted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let deque = CircularDeque::<i32>::new();
    /// assert_eq!(deque.len(), 0);
    /// assert_eq!(deque.capacity(), 0);
    /// assert!(deque.is_empty());
    /// ```
    pub fn new() -> CircularDeque<T> {
        return CircularDeque {
            len: 0,
            capacity: 0,
            // Pointer to the first item of the allocated capacity
            // (index zero)
            p_idxz: null_mut(),
            // Pointer to the last item of the allocated capacity
            // (index capacity - 1)
            p_idxc: null_mut(),
            // Pointer to the head of the queue
            p_head: null_mut(),
            // Pointer to the tail of the queue
            p_tail: null_mut(),
        };
    }

    /// Creates a new empty circular deque with the specified capacity.
    ///
    /// This pre-allocates memory for the given capacity. The deque will
    /// not need to allocate memory until the capacity is exceeded.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let deque = CircularDeque::<i32>::with_capacity(10);
    /// assert_eq!(deque.len(), 0);
    /// assert_eq!(deque.capacity(), 10);
    /// assert!(deque.is_empty());
    /// ```
    pub fn with_capacity(capacity: usize) -> CircularDeque<T> {
        let p_idxz = Self::alloc(capacity);
        unsafe {
            return CircularDeque {
                len: 0,
                capacity,
                p_idxz,
                p_idxc: p_idxz.add(capacity - 1),
                p_head: p_idxz,
                p_tail: p_idxz,
            };
        }
    }

    /// Returns `true` if the deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// assert!(deque.is_empty());
    ///
    /// deque.push_back(1);
    /// assert!(!deque.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        return self.len == 0;
    }

    /// Returns `true` if the deque is at capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::with_capacity(2);
    /// assert!(!deque.is_full());
    ///
    /// deque.push_back(1);
    /// assert!(!deque.is_full());
    ///
    /// deque.push_back(2);
    /// assert!(deque.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        return self.len == self.capacity;
    }

    /// Returns the number of elements in the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// assert_eq!(deque.len(), 0);
    ///
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// assert_eq!(deque.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        return self.len;
    }

    /// Returns the capacity of the deque.
    ///
    /// This is the maximum number of elements the deque can hold
    /// without reallocating memory.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let deque = CircularDeque::<i32>::with_capacity(10);
    /// assert_eq!(deque.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        return self.capacity;
    }

    /// Appends an element to the back of the deque.
    ///
    /// If the deque is at capacity, it will automatically grow
    /// to accommodate the new element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque.back(), Some(&2));
    /// ```
    pub fn push_back(&mut self, val: T) {
        if self.len == self.capacity {
            self.grow(0);
        }

        self.push_back_unchecked(val);
    }

    /// Removes and returns the first element of the deque.
    ///
    /// Returns `None` if the deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// assert_eq!(deque.pop_front(), Some(1));
    /// assert_eq!(deque.pop_front(), Some(2));
    /// assert_eq!(deque.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        len_zero_none!(self);
        return Some(self.pop_front_unchecked());
    }

    /// Removes and returns the last element of the deque.
    ///
    /// Returns `None` if the deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// assert_eq!(deque.pop_back(), Some(2));
    /// assert_eq!(deque.pop_back(), Some(1));
    /// assert_eq!(deque.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        len_zero_none!(self);
        return Some(self.pop_back_unchecked());
    }

    /// Prepends an element to the front of the deque.
    ///
    /// If the deque is at capacity, it will automatically grow
    /// to accommodate the new element.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_front(1);
    /// deque.push_front(2);
    ///
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque.front(), Some(&2));
    /// ```
    pub fn push_front(&mut self, val: T) {
        if self.len == self.capacity {
            self.grow(0);
        }
        self.push_front_unchecked(val);
    }

    /// Returns a reference to the first element of the deque.
    ///
    /// Returns `None` if the deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// assert_eq!(deque.front(), None);
    ///
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// assert_eq!(deque.front(), Some(&1));
    /// ```
    pub fn front(&self) -> Option<&T> {
        len_zero_none!(self);

        unsafe {
            return Some(&(*(self.p_head)));
        }
    }
    /// Returns a mutable reference to the first element of the deque.
    ///
    /// Returns `None` if the deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// assert_eq!(deque.front_mut(), None);
    ///
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// if let Some(front) = deque.front_mut() {
    ///     *front = 10;
    /// }
    /// assert_eq!(deque.front(), Some(&10));
    /// ```
    pub fn front_mut(&mut self) -> Option<&mut T> {
        len_zero_none!(self);
        unsafe {
            return Some(&mut (*(self.p_head)));
        }
    }

    /// Returns a reference to the last element of the deque.
    ///
    /// Returns `None` if the deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// assert_eq!(deque.back(), None);
    ///
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// assert_eq!(deque.back(), Some(&2));
    /// ```
    pub fn back(&self) -> Option<&T> {
        len_zero_none!(self);
        unsafe {
            let mut p_last = self.p_tail;
            dec_ptr!(self, p_last);
            return Some(&(*p_last));
        }
    }

    /// Returns a mutable reference to the last element of the deque.
    ///
    /// Returns `None` if the deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// assert_eq!(deque.back_mut(), None);
    ///
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// if let Some(back) = deque.back_mut() {
    ///     *back = 20;
    /// }
    /// assert_eq!(deque.back(), Some(&20));
    /// ```
    pub fn back_mut(&mut self) -> Option<&mut T> {
        len_zero_none!(self);
        unsafe {
            let mut p_last = self.p_tail;
            dec_ptr!(self, p_last);
            return Some(&mut (*p_last));
        }
    }

    /// Returns a reference to the element at the given index.
    ///
    /// Index 0 refers to the front of the deque, and index `len() - 1`
    /// refers to the back. Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// assert_eq!(deque.get(0), Some(&1));
    /// assert_eq!(deque.get(1), Some(&2));
    /// assert_eq!(deque.get(2), Some(&3));
    /// assert_eq!(deque.get(3), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        bounds_check_none!(self, index);

        let ptr = self.ptr_at(index);
        unsafe {
            return Some(&(*ptr));
        }
    }

    /// Returns a mutable reference to the element at the given index.
    ///
    /// Index 0 refers to the front of the deque, and index `len() - 1`
    /// refers to the back. Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// if let Some(elem) = deque.get_mut(1) {
    ///     *elem = 20;
    /// }
    /// assert_eq!(deque.get(1), Some(&20));
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        bounds_check_none!(self, index);
        let ptr = self.ptr_at(index);
        unsafe {
            return Some(&mut (*ptr));
        }
    }

    /// Swaps elements at indices `i` and `j`.
    ///
    /// # Panics
    ///
    /// Panics if either index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// deque.swap(0, 2);
    /// assert_eq!(deque.get(0), Some(&3));
    /// assert_eq!(deque.get(2), Some(&1));
    /// ```
    pub fn swap(&mut self, i: usize, j: usize) {
        bounds_check_panic!(self, i, "i");
        bounds_check_panic!(self, j, "j");

        let ptr_i = self.ptr_at(i);
        let ptr_j = self.ptr_at(j);

        if ptr_i == ptr_j {
            return;
        }

        unsafe {
            let val_i = ptr::read(ptr_i);
            let val_j = ptr::read(ptr_j);

            ptr::write(ptr_i, val_j);
            ptr::write(ptr_j, val_i);
        }
    }

    /// Inserts an element at the specified index.
    ///
    /// All elements at indices greater than or equal to `index` are shifted
    /// one position to the right. This operation is O(n) where n is the
    /// number of elements that need to be shifted.
    ///
    /// # Panics
    ///
    /// Panics if `index` is greater than the length of the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(3);
    ///
    /// deque.insert(1, 2);
    /// assert_eq!(deque.get(0), Some(&1));
    /// assert_eq!(deque.get(1), Some(&2));
    /// assert_eq!(deque.get(2), Some(&3));
    /// ```
    pub fn insert(&mut self, index: usize, value: T) {
        if index > self.len {
            panic!("index out of bounds: index={}, len={}", index, self.len)
        }

        if self.len == self.capacity {
            self.grow(0);
        }

        let ptr = self.ptr_at(index);
        let mut cur = self.p_tail;
        //TODO: Break up this loop into len and back_n
        loop {
            if cur == ptr {
                break;
            }

            let mut prev = cur;
            dec_ptr!(self, prev);
            unsafe {
                let val = ptr::read(prev);
                ptr::write(cur, val);
                cur = prev;
            }
        }
        unsafe {
            ptr::write(ptr, value);
        }
        inc_tail!(self);
        self.len += 1;
    }

    /// Removes and returns the element at the specified index.
    ///
    /// This operation is O(n) where n is the number of elements that need
    /// to be shifted. The implementation chooses the direction with fewer
    /// elements to shift for better performance.
    ///
    /// Returns `None` if the index is out of bounds or the deque is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// assert_eq!(deque.remove(1), Some(2));
    /// assert_eq!(deque.get(0), Some(&1));
    /// assert_eq!(deque.get(1), Some(&3));
    /// assert_eq!(deque.remove(5), None);
    /// ```
    pub fn remove(&mut self, index: usize) -> Option<T> {
        len_zero_none!(self);
        bounds_check_none!(self, index);
        unsafe {
            let ptr = self.ptr_at(index);
            let val = ptr::read(ptr);
            let mut idx: usize = index;
            let mut p_dst = ptr;
            let mut p_src = ptr;
            if index > self.len - index {
                inc_ptr!(self, p_src);
                //move the elements from the tail one back
                loop {
                    if idx >= self.len {
                        break;
                    }
                    self.move_elem(p_src, p_dst);
                    inc_ptr!(self, p_src);
                    inc_ptr!(self, p_dst);
                    idx += 1;
                }

                dec_tail!(self);
            } else {
                dec_ptr!(self, p_src);
                //move the elements from the head one forward
                loop {
                    if idx <= 0 {
                        break;
                    }
                    self.move_elem(p_src, p_dst);
                    dec_ptr!(self, p_src);
                    dec_ptr!(self, p_dst);

                    idx -= 1;
                }

                inc_head!(self);
            }

            self.len -= 1;
            return Some(val);
        }
    }

    /// Reserves capacity for at least `additional` more elements.
    ///
    /// This method allocates exactly the requested capacity,
    /// unlike `reserve` which may allocate more than requested.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    ///
    /// deque.reserve_exact(10);
    /// assert!(deque.capacity() >= 11);
    /// ```
    pub fn reserve_exact(&mut self, additional: usize) {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return;
        }

        let new_mem = Self::alloc(new_len);
        unsafe {
            self.rebase(new_mem, new_len);
        }
    }

    /// Reserves capacity for at least `additional` more elements.
    ///
    /// This method may allocate more than requested to avoid frequent
    /// reallocations. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    ///
    /// deque.reserve(10);
    /// assert!(deque.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return;
        }

        self.grow(new_len);
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return Ok(());
        }

        match Self::try_alloc(new_len) {
            Ok(p_mem) => {
                unsafe {
                    self.rebase(p_mem, new_len);
                }
                return Ok(());
            }
            Err(e) => {
                return Err(TryReserveError::new(e.code, e.msg));
            }
        }
    }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return Ok(());
        }

        let mut new_capacity = 0;
        if self.capacity == 0 {
            new_capacity = 1;
        } else {
            new_capacity = 2 * self.capacity;
        }

        if new_len > new_capacity {
            new_capacity = new_len;
        }

        match Self::try_alloc(new_capacity) {
            Ok(p_mem) => {
                unsafe {
                    self.rebase(p_mem, new_capacity);
                }
                return Ok(());
            }
            Err(e) => {
                return Err(TryReserveError::new(e.code, e.msg));
            }
        }
    }

    pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {
        len_zero_none!(self);
        bounds_check_none!(self, index);

        if index == 0 {
            return self.remove(index);
        }
        unsafe {
            let ptr = self.ptr_at(index);
            let val = ptr::read(ptr);
            self.move_elem(self.p_head, ptr);
            inc_head!(self);
            self.len -= 1;
            return Some(val);
        }
    }

    pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
        len_zero_none!(self);
        bounds_check_none!(self, index);

        if index == self.len - 1 {
            return self.remove(index);
        }
        unsafe {
            let ptr = self.ptr_at(index);
            let val = ptr::read(ptr);
            let p_last = self.ptr_at(self.len - 1);
            self.move_elem(p_last, ptr);
            dec_tail!(self);
            self.len -= 1;
            return Some(val);
        }
    }

    /// Removes all elements from the deque.
    ///
    /// This method does not deallocate memory - the capacity remains unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// assert_eq!(deque.len(), 3);
    /// deque.clear();
    /// assert_eq!(deque.len(), 0);
    /// assert!(deque.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Shortens the deque to the specified length.
    ///
    /// If the current length is less than or equal to `len`, this has no effect.
    /// Otherwise, elements are removed from the back until the deque has the
    /// specified length.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    ///
    /// deque.truncate(2);
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque.get(0), Some(&1));
    /// assert_eq!(deque.get(1), Some(&2));
    /// ```
    pub fn truncate(&mut self, len: usize) {
        if len >= self.len {
            return;
        }

        loop {
            if self.len == len {
                break;
            }

            self.pop_back();
        }
    }

    /// Returns the contents of the deque as a pair of mutable slices.
    ///
    /// The deque may be split into two slices due to its circular nature.
    /// The first slice contains elements from the front to either the end
    /// of the buffer or the back of the deque. The second slice contains
    /// the remaining elements, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// let (first, second) = deque.as_mut_slices();
    /// first[0] = 10;
    /// assert_eq!(deque.get(0), Some(&10));
    /// ```
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        let s_ptrs = self.slice_ptrs();
        unsafe {
            return (&mut *s_ptrs.0, &mut *s_ptrs.1);
        }
    }

    /// Returns the contents of the deque as a pair of slices.
    ///
    /// The deque may be split into two slices due to its circular nature.
    /// The first slice contains elements from the front to either the end
    /// of the buffer or the back of the deque. The second slice contains
    /// the remaining elements, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// let (first, second) = deque.as_slices();
    /// assert_eq!(first, &[1, 2, 3]);
    /// assert_eq!(second, &[]);
    /// ```
    pub fn as_slices(&self) -> (&[T], &[T]) {
        let s_ptrs = self.slice_ptrs();
        unsafe {
            return (&*(s_ptrs.0 as *const [T]), &*(s_ptrs.1 as *const [T]));
        }
    }

    fn slice_ptrs(&self) -> (*mut [T], *mut [T]) {
        unsafe {
            if self.len == 0 {
                return (
                    ptr::slice_from_raw_parts_mut(self.p_head, 0),
                    ptr::slice_from_raw_parts_mut(self.p_idxz, 0),
                );
            }

            let f_len = (self.p_idxc.offset_from(self.p_head) + 1) as usize;
            if f_len >= self.len {
                return (
                    ptr::slice_from_raw_parts_mut(self.p_head, self.len),
                    ptr::slice_from_raw_parts_mut(self.p_idxz, 0),
                );
            } else {
                return (
                    ptr::slice_from_raw_parts_mut(self.p_head, f_len),
                    ptr::slice_from_raw_parts_mut(self.p_idxz, self.len - f_len),
                );
            }
        }
    }

    pub fn append(&mut self, other: &mut CircularDeque<T>) {
        if other.len == 0 {
            return;
        }

        self.reserve(self.len + other.len);

        loop {
            let val = other.remove(0);
            match val {
                None => {
                    return;
                }
                Some(v) => {
                    self.push_back(v);
                }
            }
        }
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.retain_mut(|e| f(e));
    }

    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        //Index of the current item to examine
        let mut idx_c = 0;
        let mut idx_d = 0;
        let mut d_ct = 0;
        loop {
            if idx_c >= self.len {
                break;
            }

            unsafe {
                let ptr_c = self.ptr_at(idx_c);
                if f(&mut *ptr_c) {
                    if idx_c != idx_d {
                        //move the item from idx_c to idx_d
                        let ptr_d = self.ptr_at(idx_d);
                        let val = ptr::read(ptr_c);
                        ptr::write(ptr_d, val);
                    }
                    idx_d += 1;
                } else {
                    std::ptr::drop_in_place(ptr_c);
                    d_ct += 1;
                }
            }
            idx_c += 1;
        }
        self.p_tail = self.ptr_at(idx_d);
        self.len -= d_ct;
    }
}

impl<T> CircularDeque<T> {
    /// Returns a front-to-back iterator
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa_collections::CircularDeque;
    ///
    /// let mut cdq = CircularDeque::<i32>::new();
    /// cdq.push_back(5);
    /// cdq.push_back(3);
    /// cdq.push_back(4);
    /// let b: &[_] = &[&5, &3, &4];
    /// let c: Vec<&i32> = cdq.iter().collect();
    /// assert_eq!(&c[..], b);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }

    /// Returns a front-to-back mutable iterator
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa_collections::CircularDeque;
    ///
    /// let mut cdq = CircularDeque::<u8>::new();
    /// cdq.push_back(1);
    /// cdq.push_back(2);
    /// cdq.push_back(3);
    ///
    /// for item in cdq.iter_mut() {
    ///     *item *= 2;
    /// }
    ///
    /// let collected: Vec<&u8> = cdq.iter().collect();
    /// assert_eq!(collected, vec![&2, &4, &6]);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut::new(self)
    }
}

impl<T> CircularDeque<T> {
    /// Rearranges the internal storage to make all elements contiguous.
    ///
    /// This method rearranges the elements so they are stored in a single
    /// contiguous slice within the buffer. After calling this method,
    /// `as_slices()` will return a pair where the second slice is empty.
    ///
    /// Returns a mutable slice containing all elements in order.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::with_capacity(10);
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_front(0);
    ///
    /// // Elements might be split across two slices
    /// let (first, second) = deque.as_slices();
    ///
    /// // Make contiguous
    /// let slice = deque.make_contiguous();
    /// assert_eq!(slice, &[0, 1, 2]);
    ///
    /// // Now all elements are in one slice
    /// let (first, second) = deque.as_slices();
    /// assert_eq!(first, &[0, 1, 2]);
    /// assert_eq!(second, &[]);
    /// ```
    pub fn make_contiguous(&mut self) -> &mut [T] {
        if self.len == 0 {
            unsafe {
                return (&mut *(ptr::slice_from_raw_parts_mut(self.p_head, 0)));
            }
        }

        // Check if already contiguous The queue is contiguous if
        // p_head < p_tail (no wraparound) OR if p_head == p_tail and
        // p_head == p_idxz (full queue starting at buffer beginning).
        // Other cases with p_head == p_tail are wrapped full queues.
        if self.p_head < self.p_tail || (self.p_head == self.p_tail && self.p_head == self.p_idxz) {
            unsafe {
                return (&mut *(ptr::slice_from_raw_parts_mut(self.p_head, self.len)));
            }
        }

        // Calculate key metrics for determining which case applies
        unsafe {
            let front_len = (self.p_idxc.offset_from(self.p_head) + 1) as usize;
            let back_len = self.p_tail.offset_from(self.p_idxz) as usize;
            let gap_len = self.capacity - self.len;

            // Case 1: Gap is big enough to fit the front segment
            if gap_len >= front_len {
                // Copy back segment over by front_len elements
                ptr::copy(self.p_idxz, self.p_idxz.add(front_len), back_len);
                // Copy front segment before back
                ptr::copy_nonoverlapping(self.p_head, self.p_idxz, front_len);
            }
            // Case 2: Gap is big enough to fit the back segment
            else if gap_len >= back_len {
                // Shift front segment left by back_len
                ptr::copy(self.p_head, self.p_head.sub(back_len), front_len);
                // Copy back segment after front
                ptr::copy_nonoverlapping(
                    self.p_idxz,
                    self.p_head.sub(back_len).add(front_len),
                    back_len,
                );
                // Update head pointer for this case
                self.p_head = self.p_head.sub(back_len);
            }
            // Cases 3 & 4: Gap too small for either segment
            else {
                // Case 3: Front is smaller than or equal to back
                if front_len <= back_len {
                    // If gap != 0 then copy front to make the two segments adjacent
                    if gap_len != 0 {
                        ptr::copy(self.p_head, self.p_tail, front_len);
                    }
                    // Use slice.rotate_right to make the elements contiguous
                    let slice = ptr::slice_from_raw_parts_mut(self.p_idxz, self.len);
                    (&mut *slice).rotate_right(front_len);
                }
                // Case 4: Back is smaller than front
                else {
                    // If gap != 0 then copy back to make the two segments adjacent
                    if gap_len != 0 {
                        ptr::copy(self.p_idxz, self.p_head.sub(back_len), back_len);
                    }
                    // Use slice.rotate_left to make the elements contiguous
                    let slice = ptr::slice_from_raw_parts_mut(self.p_idxz, self.len);
                    (&mut *slice).rotate_left(back_len);
                }
            }

            // Update pointers after rearrangement
            self.p_head = self.p_idxz;
            self.p_tail = self.p_idxz.add(self.len);

            // Return the contiguous slice
            return (&mut *(ptr::slice_from_raw_parts_mut(self.p_head, self.len)));
        }
    }

    pub fn rotate_right(&mut self, n: usize) {
        if self.len == 0 || n == self.len || n == 0 {
            return;
        }

        if n > self.len {
            panic!("n={:?} cannot be greater than len = {:?}", n, self.len);
        }

        if self.len == self.capacity {
            self.p_head = self.ptr_at(self.len - n);
            self.p_tail = self.p_head;
        } else {
            let len_f = n;
            let len_b = self.len - n;
            if len_f <= len_b {
                for i in 0..len_f {
                    let val = self.pop_back_unchecked();
                    self.push_front_unchecked(val);
                }
            } else {
                for i in 0..len_b {
                    let val = self.pop_front_unchecked();
                    self.push_back_unchecked(val);
                }
            }
        }
    }

    pub fn rotate_left(&mut self, n: usize) {
        if self.len == 0 || n == self.len || n == 0 {
            return;
        }

        if n > self.len {
            panic!("n={:?} cannot be greater than len = {:?}", n, self.len);
        }

        // If the len equals the capacity then there are no gaps and we
        // can simply update the pointers without actually moving any
        // elements.
        if self.len == self.capacity {
            self.p_head = self.ptr_at(n);
            self.p_tail = self.p_head;
        } else {
            // len_b is the length of the part of the array that will not be rotated.
            let len_b = self.len - n;
            if n <= len_b {
                // Move the first n elements to the back (fewer moves)
                for i in 0..n {
                    let val = self.pop_front_unchecked();
                    self.push_back_unchecked(val);
                }
            } else {
                // Move the last len_b elements to the front (fewer moves)
                for i in 0..len_b {
                    let val = self.pop_back_unchecked();
                    self.push_front_unchecked(val);
                }
            }
        }
    }
}

impl<T: Copy> CircularDeque<T> {
    /// Creates a new circular deque from a slice.
    ///
    /// The elements are copied from the slice into the deque.
    /// This method is only available for types that implement `Copy`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let slice = &[1, 2, 3, 4, 5];
    /// let deque = CircularDeque::from_slice(slice);
    ///
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque.get(0), Some(&1));
    /// assert_eq!(deque.get(4), Some(&5));
    /// ```
    pub fn from_slice(src: &[T]) -> CircularDeque<T> {
        let mut cdq = CircularDeque::with_capacity(src.len());
        for i in 0..src.len() {
            cdq.push_back(src[i]);
        }
        return cdq;
    }
}

/// Error codes for memory allocation and capacity management operations.
///
/// These error codes are used to indicate various failure conditions
/// when attempting to allocate or manage memory for the circular deque.
///
/// # Examples
///
/// ```
/// # use deepmesa_collections::deque::ErrorCode;
/// let error = ErrorCode::AllocError;
/// // Handle allocation error appropriately
/// ```
pub enum ErrorCode {
    /// Memory allocation failed
    AllocError,
    /// Memory layout computation failed
    MemLayoutError,
    /// Capacity overflow (requested capacity too large)
    CapacityOverflow,
}

/// Error type returned when a memory reservation operation fails.
///
/// This error contains both an error code indicating the type of failure
/// and a descriptive message explaining what went wrong.
///
/// # Examples
///
/// ```
/// # use deepmesa_collections::{CircularDeque, deque::TryReserveError};
/// let mut deque = CircularDeque::<i32>::new();
///
/// // This might fail if we request too much memory
/// match deque.try_reserve(usize::MAX) {
///     Ok(()) => println!("Successfully reserved memory"),
///     Err(error) => println!("Failed to reserve memory: {}", error.msg),
/// }
/// ```
pub struct TryReserveError {
    /// The error code indicating the type of failure
    pub code: ErrorCode,
    /// A descriptive message explaining the error
    pub msg: String,
}

impl TryReserveError {
    pub(crate) fn new(code: ErrorCode, msg: String) -> TryReserveError {
        return TryReserveError { code, msg };
    }
}

/// Error type returned when a memory allocation operation fails.
///
/// This error contains both an error code indicating the type of failure
/// and a descriptive message explaining what went wrong.
///
/// # Examples
///
/// ```
/// # use deepmesa_collections::deque::{TryAllocError, ErrorCode};
/// // TryAllocError is typically created internally by the library
/// // when allocation operations fail
/// ```
pub struct TryAllocError {
    /// The error code indicating the type of failure
    code: ErrorCode,
    /// A descriptive message explaining the error
    msg: String,
}

impl TryAllocError {
    pub(crate) fn new(code: ErrorCode, msg: String) -> TryAllocError {
        return TryAllocError { code, msg };
    }
}

//Private methods
impl<T> CircularDeque<T> {
    fn pop_back_unchecked(&mut self) -> T {
        dec_tail!(self);
        let val: T;
        unsafe {
            val = ptr::read(self.p_tail);
        }
        self.len -= 1;
        return val;
    }

    fn push_front_unchecked(&mut self, val: T) {
        dec_head!(self);
        unsafe {
            ptr::write(self.p_head, val);
        }
        self.len += 1;
    }

    fn push_back_unchecked(&mut self, val: T) {
        unsafe {
            ptr::write(self.p_tail, val);
        }

        inc_tail!(self);
        self.len += 1;
    }

    fn pop_front_unchecked(&mut self) -> T {
        let val: T;
        unsafe {
            val = ptr::read(self.p_head);
        }

        inc_head!(self);
        self.len -= 1;
        return val;
    }

    fn grow(&mut self, min_capacity: usize) {
        let mut new_capacity = 0;
        if self.capacity == 0 {
            new_capacity = 1;
        } else {
            new_capacity = 2 * self.capacity;
        }

        if min_capacity > new_capacity {
            new_capacity = min_capacity;
        }

        let new_mem = Self::alloc(new_capacity);
        unsafe {
            self.rebase(new_mem, new_capacity);
        }
    }

    //Move an element from the location p_src to the location
    // p_dst. p_src may or may not be overwritten / changed
    fn move_elem(&mut self, p_src: *mut T, p_dst: *mut T) {
        unsafe {
            let val: T = ptr::read(p_src);
            ptr::write(p_dst, val);
        }
    }

    //Copies the data from the old to the new memory allocated and
    // drops the old memory.
    unsafe fn rebase(&mut self, p_new: *mut T, alloc_size: usize) {
        debug_assert!(self.len <= alloc_size);
        let mut cur: *mut T = self.p_head;
        let mut idx: usize = 0;
        let mut p_dst = p_new;
        loop {
            if idx >= self.len {
                break;
            }
            self.move_elem(cur, p_dst);
            inc_ptr!(self, cur);
            p_dst = p_dst.add(1);
            idx += 1;
        }

        self.capacity = alloc_size;
        let p_old = self.p_idxz;
        self.p_idxz = p_new;
        self.p_idxc = self.p_idxz.add(self.capacity - 1);
        self.p_head = p_new;
        self.p_tail = self.p_head.add(self.len);

        Self::dealloc(p_old, self.len);
    }

    fn dealloc(ptr: *mut T, len: usize) {
        //TODO: Remove this unwrap: check that len < isize::MAX
        let layout = Layout::array::<T>(len).unwrap();
        unsafe {
            dealloc(ptr as *mut u8, layout);
        }
    }

    fn try_alloc(len: usize) -> Result<*mut T, TryAllocError> {
        unsafe {
            match Layout::array::<T>(len) {
                Ok(layout) => {
                    let arr = alloc_zeroed(layout) as *mut T;
                    if arr.is_null() {
                        return Err(TryAllocError::new(
                            ErrorCode::AllocError,
                            "Memory Allocation Failed".to_string(),
                        ));
                    }
                    return Ok(arr);
                }
                Err(_) => {
                    return Err(TryAllocError::new(
                        ErrorCode::CapacityOverflow,
                        "Memory Allocation Failed: Capacity Overflow".to_string(),
                    ));
                }
            }
        }
    }

    fn alloc(len: usize) -> *mut T {
        unsafe {
            //TODO: remove this unwrap and handle the error
            let layout = Layout::array::<T>(len).unwrap();
            let arr = alloc_zeroed(layout) as *mut T;
            if arr.is_null() {
                panic!("memory allocation failed!");
            }
            return arr;
        }
    }

    // Returns the pointer for the given index (between 0 and len)
    // starting at the head of the deque. If the index is greater than
    // or equal to len then the behavior is undefined
    pub(in crate::cdeque) fn ptr_at(&self, index: usize) -> *mut T {
        unsafe {
            let dist = self.p_idxc.offset_from(self.p_head) as usize;
            if dist < index {
                return self.p_idxz.add(index - dist - 1);
            } else {
                return self.p_head.add(index);
            }
        }
    }

    //Returns the index from the head to the end of the buffer
    fn head2end(&self) -> usize {
        unsafe {
            return self.p_idxc.offset_from(self.p_head) as usize;
        }
    }

    //Returns the index from the beginning of the buffer to tail.
    fn start2tail(&self) -> usize {
        unsafe {
            return self.p_tail.offset_from(self.p_idxz) as usize;
        }
    }
}

impl<T> CircularDeque<T>
where
    T: PartialEq,
{
    /// Returns `true` if the deque contains an element equal to the given value.
    ///
    /// This method performs a linear search through the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// assert!(deque.contains(&2));
    /// assert!(!deque.contains(&4));
    /// ```
    pub fn contains(&self, x: &T) -> bool {
        let mut idx: usize = 0;
        loop {
            if idx >= self.len() {
                break;
            }

            unsafe {
                let val = &*self.ptr_at(idx);
                if val.eq(x) {
                    return true;
                }
                idx += 1;
            }
        }
        return false;
    }
}

impl<T: Debug> CircularDeque<T> {
    //TODO: Remove
    fn print_mem(&self) {
        let mut cur = self.p_idxz;
        for i in 0..self.capacity {
            unsafe {
                let mut s = String::with_capacity(32);
                if cur == self.p_head {
                    s.push_str(&format!(" p_head [{}]", i));
                }
                if cur == self.p_tail {
                    s.push_str(&format!(" p_tail [{}]", i));
                }
                if cur == self.p_idxz {
                    s.push_str(&format!(" p_idxz [{}]", i));
                }
                if cur == self.p_idxc {
                    s.push_str(&format!(" p_idxc [{}]", i));
                }

                println!("[{:}]: {:?} = {:?} <-- {:}", i, cur, *cur, s);
                cur = cur.add(1);
            }
        }
        println!("len: {:?}", self.len);
        println!("p_head: {:?}", self.p_head);
        println!("p_tail: {:?}", self.p_tail);
        println!("p_idxz: {:?}", self.p_idxz);
        println!("p_idxc: {:?}", self.p_idxc);
    }
}

impl<T> CircularDeque<T>
where
    T: Clone,
{
    /// Modifies the deque in-place so that len() is equal to new_len,
    /// either by removing excess elements from the back or by
    /// appending clones of value to the back.
    ///
    /// # Examples
    ///
    /// Growing the deque:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// deque.resize(5, 0);
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[1], 2);
    /// assert_eq!(deque[2], 0);
    /// assert_eq!(deque[3], 0);
    /// assert_eq!(deque[4], 0);
    /// ```
    ///
    /// Shrinking the deque:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    /// deque.push_back(4);
    ///
    /// deque.resize(2, 0);
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[1], 2);
    /// ```
    ///
    /// Resizing to the same length is a no-op:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// deque.resize(2, 999);
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[1], 2);
    /// ```
    pub fn resize(&mut self, new_len: usize, value: T) {
        if new_len > self.len {
            // Need to grow - append clones of value
            let additional = new_len - self.len;
            self.reserve(additional);

            for _ in 0..additional {
                self.push_back(value.clone());
            }
        } else if new_len < self.len {
            // Need to shrink - remove elements from the back
            self.truncate(new_len);
        }
        // If new_len == self.len, do nothing
    }
}

#[cfg(test)]
mod tests {
    use super::CircularDeque;

    macro_rules! assert_ptrs {
        ($cdq:ident) => {
            if $cdq.is_empty() {
                assert_eq!($cdq.p_head, $cdq.p_tail);
            } else if $cdq.is_full() {
                assert_eq!($cdq.p_head, $cdq.p_tail);
            } else {
                unsafe { assert_eq!($cdq.p_idxc, $cdq.p_idxz.add($cdq.capacity - 1)) }
            }
        };
    }

    #[test]
    fn test_contains() {
        let mut cdq = cdeque!(1, 2, 3);
        assert_eq!(cdq.contains(&9), false);
        assert_eq!(cdq.contains(&1), true);
        assert_eq!(cdq.contains(&2), true);
        assert_eq!(cdq.contains(&3), true);
    }

    #[test]
    fn test_eq() {
        let mut cdq = cdeque!(1, 2, 3);
        assert_eq!(cdq, cdeque!(1, 2, 3));
        assert_ne!(cdq, cdeque!(1, 2, 3, 5));
    }

    #[test]
    fn test_append() {
        let mut cdq = cdeque!(1, 2, 3);
        let mut other = cdeque!(5, 6, 7, 8);
        cdq.append(&mut other);
        assert_eq!(other, cdeque!());
        assert_eq!(cdq, cdeque!(1, 2, 3, 5, 6, 7, 8));

        let mut cdq = cdeque!();
        let mut other = cdeque!(5, 6, 7, 8);
        cdq.append(&mut other);
        assert_eq!(other, cdeque!());
        assert_eq!(cdq, cdeque!(5, 6, 7, 8));
    }

    #[test]
    fn test_remove() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
        assert_ptrs!(cdq);
        assert_eq!(cdq.len(), 10);
        let val = cdq.remove(3);
        assert_eq!(val, Some(4u8));
        assert_eq!(cdq, cdeque!(1, 2, 3, 5, 6, 7, 8, 9, 10));
        for i in 0..10 {
            cdq.remove(1);
        }
        assert_eq!(cdq.len(), 1);
        cdq.remove(0);
        assert_eq!(cdq.len(), 0);
    }

    #[test]
    fn test_swap_remove_back() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);

        let val = cdq.swap_remove_back(4);
        assert_eq!(val, Some(5));
        assert_eq!(cdq, cdeque!(1, 2, 3, 4));

        let val = cdq.swap_remove_back(1);
        assert_eq!(val, Some(2));
        assert_eq!(cdq, cdeque!(1, 4, 3));

        let val = cdq.swap_remove_back(1);
        assert_eq!(val, Some(4));
        assert_eq!(cdq, cdeque!(1, 3));

        let val = cdq.swap_remove_back(0);
        assert_eq!(val, Some(1));
        assert_eq!(cdq, cdeque!(3));

        let val = cdq.swap_remove_back(0);
        assert_eq!(val, Some(3));
        assert_eq!(cdq, cdeque!());
    }

    #[test]
    fn test_swap_remove_front() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        let val = cdq.swap_remove_front(0);
        assert_eq!(val, Some(1));
        assert_eq!(cdq, cdeque!(2, 3, 4, 5));

        let val = cdq.swap_remove_front(2);
        assert_eq!(val, Some(4));
        assert_eq!(cdq, cdeque!(3, 2, 5));

        let val = cdq.swap_remove_front(1);
        assert_eq!(val, Some(2));
        assert_eq!(cdq, cdeque!(3, 5));

        let val = cdq.swap_remove_front(1);
        assert_eq!(val, Some(5));
        assert_eq!(cdq, cdeque!(3));

        let val = cdq.swap_remove_front(0);
        assert_eq!(val, Some(3));
        assert_eq!(cdq, cdeque!());

        let val = cdq.swap_remove_front(10);
        assert_eq!(val, None);
        assert_eq!(cdq, cdeque!());
    }

    // push_back and pop_front
    #[test]
    fn test_back2front() {
        let mut cdq = CircularDeque::<u8>::with_capacity(5);

        assert_eq!(cdq.len(), 0);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        assert_eq!(cdq.p_head, cdq.p_idxz);
        assert_eq!(cdq.p_head, cdq.p_tail);
        for i in 0u8..5 {
            cdq.push_back(i);
            assert_ptrs!(cdq);
        }
        assert_ptrs!(cdq);

        assert_eq!(cdq.len(), 5);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        assert_eq!(cdq.p_head, cdq.p_idxz);
        assert_eq!(cdq.p_tail, cdq.p_idxz);
        assert_ptrs!(cdq);

        for i in 0u8..3 {
            match cdq.pop_front() {
                None => {
                    assert!(false);
                }
                Some(v) => {
                    assert_eq!(v, i);
                    assert_ptrs!(cdq);
                }
            }
        }
        assert_ptrs!(cdq);

        assert_eq!(cdq.len(), 2);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        unsafe {
            assert_eq!(cdq.p_head, cdq.p_idxz.add(3));
        }
        assert_eq!(cdq.p_tail, cdq.p_idxz);
        assert_ptrs!(cdq);

        cdq.push_back(9);
        assert_eq!(cdq.len(), 3);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        unsafe {
            assert_eq!(cdq.p_head, cdq.p_idxz.add(3));
            assert_eq!(cdq.p_tail, cdq.p_idxz.add(1));
        }
        assert_ptrs!(cdq);

        cdq.push_back(10);
        assert_ptrs!(cdq);
        cdq.push_back(11);
        assert_ptrs!(cdq);
        assert_eq!(cdq.len(), 5);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        unsafe {
            assert_eq!(cdq.p_head, cdq.p_idxz.add(3));
            assert_eq!(cdq.p_tail, cdq.p_idxz.add(3));
        }
        assert_ptrs!(cdq);

        //now grow it
        cdq.push_back(1);
        assert_eq!(cdq.len(), 6);
        assert_eq!(cdq.capacity(), 10);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        assert_eq!(cdq.p_head, cdq.p_idxz);
        unsafe {
            assert_eq!(cdq.p_tail, cdq.p_idxz.add(cdq.len()));
        }
        assert_ptrs!(cdq);
    }

    #[test]
    fn test_front2back() {
        let mut cdq = CircularDeque::<u8>::with_capacity(5);
        assert_eq!(cdq.len(), 0);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        assert_eq!(cdq.p_head, cdq.p_idxz);
        assert_eq!(cdq.p_head, cdq.p_tail);
        assert_ptrs!(cdq);

        cdq.push_front(0);
        assert_eq!(cdq.len(), 1);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        assert_eq!(cdq.p_head, cdq.p_idxc);
        assert_eq!(cdq.p_tail, cdq.p_idxz);
        assert_ptrs!(cdq);

        for i in 1u8..5 {
            cdq.push_front(i);
        }
        assert_eq!(cdq.len(), 5);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        assert_eq!(cdq.p_head, cdq.p_idxz);
        assert_eq!(cdq.p_tail, cdq.p_idxz);
        assert_ptrs!(cdq);

        for i in 0u8..3 {
            match cdq.pop_back() {
                None => {
                    assert!(false);
                }
                Some(v) => {
                    assert_eq!(v, i);
                    assert_ptrs!(cdq);
                }
            }
        }
        assert_ptrs!(cdq);
        assert_eq!(cdq.len(), 2);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        unsafe {
            assert_eq!(cdq.p_tail, cdq.p_idxz.add(2));
        }
        assert_eq!(cdq.p_head, cdq.p_idxz);
        assert_ptrs!(cdq);

        cdq.push_front(9);
        assert_eq!(cdq.len(), 3);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        unsafe {
            assert_eq!(cdq.p_tail, cdq.p_idxz.add(2));
            assert_eq!(cdq.p_head, cdq.p_idxc);
        }
        assert_ptrs!(cdq);

        cdq.push_front(10);
        assert_ptrs!(cdq);
        cdq.push_front(11);
        assert_eq!(cdq.len(), 5);
        assert_eq!(cdq.capacity(), 5);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        unsafe {
            assert_eq!(cdq.p_head, cdq.p_idxz.add(2));
            assert_eq!(cdq.p_tail, cdq.p_idxz.add(2));
        }
        assert_ptrs!(cdq);
        //now grow it
        cdq.push_front(1);
        assert_eq!(cdq.len(), 6);
        assert_eq!(cdq.capacity(), 10);
        assert!(!cdq.p_head.is_null());
        assert!(!cdq.p_tail.is_null());
        assert_eq!(cdq.p_head, cdq.p_idxc);
        unsafe {
            assert_eq!(cdq.p_tail, cdq.p_idxz.add(cdq.len() - 1));
        }
        assert_ptrs!(cdq);
    }

    #[test]
    fn test_grow() {
        let mut cdq = CircularDeque::<u8>::new();
        assert_eq!(cdq.len(), 0);
        assert_eq!(cdq.capacity(), 0);
        assert!(cdq.p_head.is_null());
        assert!(cdq.p_tail.is_null());
        assert!(cdq.p_idxz.is_null());
        assert!(cdq.p_idxc.is_null());
        assert_ptrs!(cdq);

        cdq.push_back(0);
        assert_eq!(cdq.len(), 1);
        assert_eq!(cdq.capacity(), 1);
        assert_eq!(cdq.p_head, cdq.p_idxz);
        unsafe {
            assert_eq!(cdq.p_tail, cdq.p_head);
            assert_eq!(cdq.p_idxc, cdq.p_idxz.add(cdq.capacity() - 1));
        }
        assert_ptrs!(cdq);

        cdq.push_back(1);
        assert_eq!(cdq.len(), 2);
        assert_eq!(cdq.capacity(), 2);
        assert_eq!(cdq.p_head, cdq.p_idxz);
        unsafe {
            assert_eq!(cdq.p_tail, cdq.p_head);
            assert_eq!(cdq.p_idxc, cdq.p_idxz.add(cdq.capacity() - 1));
        }
        assert_ptrs!(cdq);

        cdq.push_back(2);
        assert_eq!(cdq.len(), 3);
        assert_eq!(cdq.capacity(), 4);
        assert_eq!(cdq.p_head, cdq.p_idxz);
        unsafe {
            assert_eq!(cdq.p_tail, cdq.p_idxc);
            assert_eq!(cdq.p_idxc, cdq.p_idxz.add(cdq.capacity() - 1));
        }
        assert_ptrs!(cdq);

        cdq.push_back(3);
        assert_eq!(cdq.len(), 4);
        assert_eq!(cdq.capacity(), 4);
        assert_eq!(cdq.p_head, cdq.p_idxz);
        unsafe {
            assert_eq!(cdq.p_tail, cdq.p_head);
            assert_eq!(cdq.p_idxc, cdq.p_idxz.add(cdq.capacity() - 1));
        }
        assert_ptrs!(cdq);

        cdq.push_back(4);
        assert_eq!(cdq.len(), 5);
        assert_eq!(cdq.capacity(), 8);
        assert_eq!(cdq.p_head, cdq.p_idxz);
        unsafe {
            assert_eq!(cdq.p_tail, cdq.p_head.add(cdq.len()));
            assert_eq!(cdq.p_idxc, cdq.p_idxz.add(cdq.capacity() - 1));
        }
        assert_ptrs!(cdq);
    }

    #[test]
    fn test_swap() {
        let mut cdq = CircularDeque::<u8>::with_capacity(10);
        assert_eq!(cdq.len(), 0);
        assert_eq!(cdq.capacity(), 10);

        cdq.push_front(4);
        cdq.push_front(3);
        cdq.push_front(2);
        cdq.push_front(1);
        cdq.push_back(7);
        cdq.push_back(8);
        cdq.push_back(9);

        //        cdq.print_mem();

        let val2 = cdq.get(2);
        assert_eq!(val2, Some(&3));
        let val5 = cdq.get(5);
        assert_eq!(val5, Some(&8));

        cdq.swap(2, 5);
        let val2 = cdq.get(2);
        assert_eq!(val2, Some(&8));
        let val5 = cdq.get(5);
        assert_eq!(val5, Some(&3));
    }

    #[test]
    fn test_get() {
        let cdq: CircularDeque<u8> = cdeque!(1, 2, 3, 4, 7, 8, 9);
        assert_eq!(cdq.get(6).unwrap(), &9u8);
        assert_eq!(cdq.get(0).unwrap(), &1u8);
        assert_eq!(cdq.get(12), None);
    }

    #[test]
    fn test_insert() {
        let mut cdq: CircularDeque<u8> = cdeque!(1, 2, 3, 4, 7, 8, 9);
        cdq.insert(7, 12);
        assert_eq!(cdq, cdeque!(1, 2, 3, 4, 7, 8, 9, 12));
    }

    #[test]
    fn test_reserve() {
        let mut cdq = cdeque!(1, 2, 3, 4);
        assert_eq!(cdq.len, 4);
        assert_eq!(cdq.capacity, 4);
        cdq.reserve(8);
        assert_eq!(cdq, cdeque!(1, 2, 3, 4));
        assert_eq!(cdq.len, 4);
        assert_eq!(cdq.capacity, 12);
    }

    #[test]
    fn test_reserve_exact() {
        let mut cdq = cdeque!(1, 2, 3, 4);
        assert_eq!(cdq.len, 4);
        assert_eq!(cdq.capacity, 4);
        cdq.reserve_exact(2);
        assert_eq!(cdq, cdeque!(1, 2, 3, 4));
        assert_eq!(cdq.len, 4);
        assert_eq!(cdq.capacity, 6);
    }

    #[test]
    fn test_as_slices() {
        let mut cdq: CircularDeque<u8> = cdeque!();
        assert_eq!(cdq.as_slices(), (&[][..], &[][..]));

        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        let s = cdq.as_slices();
        assert_eq!(cdq.as_slices(), (&[1, 2, 3, 4, 5][..], &[][..]));

        cdq.push_front(9);
        cdq.push_front(8);

        let s = cdq.as_slices();
        assert_eq!(cdq.as_slices(), (&[8, 9][..], &[1, 2, 3, 4, 5][..]));
    }

    #[test]
    fn test_as_mut_slices() {
        let mut cdq: CircularDeque<u8> = cdeque!();
        assert_eq!(cdq.as_mut_slices(), (&mut [][..], &mut [][..]));

        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        let s = cdq.as_mut_slices();
        let front = s.0;
        let back = s.1;

        assert_eq!(front, &[1, 2, 3, 4, 5][..]);
        assert_eq!(back, &[][..]);

        front[2] = 9;
        assert_eq!(front, &[1, 2, 9, 4, 5][..]);
        assert_eq!(back, &[][..]);

        cdq.push_front(19);
        cdq.push_front(18);

        let s = cdq.as_mut_slices();
        let front = s.0;
        let back = s.1;

        assert_eq!(front, &[18, 19][..]);
        assert_eq!(back, &[1, 2, 9, 4, 5][..]);

        front[1] = 11;

        assert_eq!(front, &[18, 11][..]);
        assert_eq!(back, &[1, 2, 9, 4, 5][..]);
    }

    #[test]
    fn test_truncate() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.truncate(3);
        assert_eq!(cdq, cdeque!(1, 2, 3));
        cdq.truncate(1);
        assert_eq!(cdq, cdeque!(1));
        cdq.truncate(0);
        assert_eq!(cdq, cdeque!());
    }

    #[test]
    fn test_clear() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.clear();
        assert_eq!(cdq, cdeque!());
    }

    #[test]
    fn test_retain_mut() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.retain_mut(|x| {
            if *x % 2 == 0 {
                return false;
            } else {
                *x += 3;
                return true;
            }
        });

        assert_eq!(cdq, cdeque!(4, 6, 8));
    }

    #[test]
    fn test_retain() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.retain(|x| {
            if *x % 2 == 0 {
                return false;
            } else {
                return true;
            }
        });

        assert_eq!(cdq, cdeque!(1, 3, 5));
    }

    #[test]
    fn test_rotate_left() {
        let mut cdq = cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9);
        cdq.rotate_left(3);
        assert_eq!(cdq, cdeque!(3, 4, 5, 6, 7, 8, 9, 0, 1, 2));

        for i in 1..10 {
            assert_eq!(i * 3 % 10, cdq[0]);
            cdq.rotate_left(3);
        }
        assert_eq!(cdq, cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));

        //now test when the deque is not full
        cdq.reserve_exact(20);

        cdq.rotate_left(6);
        assert_eq!(cdq, cdeque!(6, 7, 8, 9, 0, 1, 2, 3, 4, 5));

        for i in 1..10 {
            assert_eq!(i * 6 % 10, cdq[0]);
            cdq.rotate_left(6);
        }
        assert_eq!(cdq, cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));

        cdq.rotate_left(3);
        assert_eq!(cdq, cdeque!(3, 4, 5, 6, 7, 8, 9, 0, 1, 2));

        for i in 1..10 {
            assert_eq!(i * 3 % 10, cdq[0]);
            cdq.rotate_left(3);
        }
        assert_eq!(cdq, cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));
    }

    #[test]
    fn test_rotate_right() {
        let mut cdq = cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9);
        cdq.rotate_right(3);
        assert_eq!(cdq, cdeque!(7, 8, 9, 0, 1, 2, 3, 4, 5, 6));

        for i in 1..10 {
            assert_eq!((10 - (i * 3) % 10) % 10, cdq[0]);
            cdq.rotate_right(3);
        }
        assert_eq!(cdq, cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));

        //now test when the deque is not full
        cdq.reserve_exact(20);

        cdq.rotate_right(4);
        assert_eq!(cdq, cdeque!(6, 7, 8, 9, 0, 1, 2, 3, 4, 5));

        for i in 1..10 {
            assert_eq!((10 - (i * 4) % 10) % 10, cdq[0]);
            cdq.rotate_right(4);
        }
        assert_eq!(cdq, cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));

        cdq.rotate_right(7);
        assert_eq!(cdq, cdeque!(3, 4, 5, 6, 7, 8, 9, 0, 1, 2));

        for i in 1..10 {
            assert_eq!((10 - (i * 7) % 10) % 10, cdq[0]);
            cdq.rotate_right(7);
        }
        assert_eq!(cdq, cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));
    }

    #[test]
    fn test_make_contiguous() {
        // Test 1: Already contiguous
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        let slice = cdq.make_contiguous();
        assert_eq!(slice, &[1, 2, 3, 4, 5]);
        assert_eq!(cdq.len(), 5);

        // Test 2: Empty deque
        let mut empty_cdq = CircularDeque::<i32>::new();
        let empty_slice = empty_cdq.make_contiguous();
        assert_eq!(empty_slice, &[]);
        assert_eq!(empty_cdq.len(), 0);

        // Test 3: Single element
        let mut single_cdq = cdeque!(42);
        let single_slice = single_cdq.make_contiguous();
        assert_eq!(single_slice, &[42]);
        assert_eq!(single_cdq.len(), 1);

        // Test 4: Simple wrapped scenario
        let mut wrapped_cdq = CircularDeque::with_capacity(10);
        // Fill some elements normally
        wrapped_cdq.push_back(5);
        wrapped_cdq.push_back(6);

        // Now add to front to create wraparound
        wrapped_cdq.push_front(4);
        wrapped_cdq.push_front(3);
        wrapped_cdq.push_front(2);
        wrapped_cdq.push_front(1);

        // Elements should be logically [1, 2, 3, 4, 5]
        // Verify individual access works first
        assert_eq!(wrapped_cdq.get(0), Some(&1));
        assert_eq!(wrapped_cdq.get(1), Some(&2));
        assert_eq!(wrapped_cdq.get(2), Some(&3));
        assert_eq!(wrapped_cdq.get(3), Some(&4));
        assert_eq!(wrapped_cdq.get(4), Some(&5));
        assert_eq!(wrapped_cdq.get(5), Some(&6));

        // Now make contiguous
        let contiguous_slice = wrapped_cdq.make_contiguous();

        assert_eq!(contiguous_slice, &[1, 2, 3, 4, 5, 6]);
        assert_eq!(wrapped_cdq.len(), 6);

        // Verify the deque still works after make_contiguous
        assert_eq!(wrapped_cdq.front(), Some(&1));
        assert_eq!(wrapped_cdq.back(), Some(&6));

        // Test 5: Edge case - queue is full (len=capacity) and already contiguous
        let mut full_contiguous_cdq = CircularDeque::with_capacity(5);
        for i in 1..=5 {
            full_contiguous_cdq.push_back(i);
        }
        // At this point: len=5, capacity=5, elements are contiguous [1,2,3,4,5]
        assert_eq!(full_contiguous_cdq.len(), 5);
        assert_eq!(full_contiguous_cdq.capacity(), 5);
        assert_eq!(full_contiguous_cdq.is_full(), true);

        // Verify elements are already contiguous
        let (first_slice, second_slice) = full_contiguous_cdq.as_slices();
        assert_eq!(first_slice, &[1, 2, 3, 4, 5]);
        assert_eq!(second_slice, &[]);

        // Now call make_contiguous on the full, already contiguous deque
        let contiguous_slice = full_contiguous_cdq.make_contiguous();

        // Should return the same contiguous slice
        assert_eq!(contiguous_slice, &[1, 2, 3, 4, 5]);
        assert_eq!(full_contiguous_cdq.len(), 5);
        assert_eq!(full_contiguous_cdq.capacity(), 5);

        // Verify the deque still works correctly
        assert_eq!(full_contiguous_cdq.front(), Some(&1));
        assert_eq!(full_contiguous_cdq.back(), Some(&5));
        assert_eq!(full_contiguous_cdq.get(0), Some(&1));
        assert_eq!(full_contiguous_cdq.get(4), Some(&5));

        // Test 6: Edge case - queue is full (len=capacity) and NOT contiguous
        let mut full_wrapped_cdq = CircularDeque::with_capacity(5);

        // First fill normally to create some elements
        full_wrapped_cdq.push_back(3);
        full_wrapped_cdq.push_back(4);
        full_wrapped_cdq.push_back(5);

        // Now add to front to create wraparound and fill to capacity
        full_wrapped_cdq.push_front(2);
        full_wrapped_cdq.push_front(1);

        // At this point: len=5, capacity=5, elements wrap around [1,2,3,4,5]
        assert_eq!(full_wrapped_cdq.len(), 5);
        assert_eq!(full_wrapped_cdq.capacity(), 5);
        assert_eq!(full_wrapped_cdq.is_full(), true);

        // Verify elements are NOT contiguous (they wrap around)
        let (first_slice, second_slice) = full_wrapped_cdq.as_slices();
        // The exact split depends on internal pointer positions, but both slices should be non-empty
        assert!(
            !first_slice.is_empty() && !second_slice.is_empty(),
            "Expected non-contiguous layout with both slices non-empty"
        );

        // Verify logical order is correct
        assert_eq!(full_wrapped_cdq.get(0), Some(&1));
        assert_eq!(full_wrapped_cdq.get(1), Some(&2));
        assert_eq!(full_wrapped_cdq.get(2), Some(&3));
        assert_eq!(full_wrapped_cdq.get(3), Some(&4));
        assert_eq!(full_wrapped_cdq.get(4), Some(&5));

        // Now call make_contiguous on the full, non-contiguous deque
        let contiguous_slice = full_wrapped_cdq.make_contiguous();

        // Should return the contiguous slice in logical order
        assert_eq!(contiguous_slice, &[1, 2, 3, 4, 5]);

        assert_eq!(full_wrapped_cdq.len(), 5);
        assert_eq!(full_wrapped_cdq.capacity(), 5);

        // Verify the deque still works correctly after make_contiguous
        assert_eq!(full_wrapped_cdq.front(), Some(&1));
        assert_eq!(full_wrapped_cdq.back(), Some(&5));
        assert_eq!(full_wrapped_cdq.get(0), Some(&1));
        assert_eq!(full_wrapped_cdq.get(4), Some(&5));

        // Verify it's now contiguous
        let (first_slice_after, second_slice_after) = full_wrapped_cdq.as_slices();
        assert_eq!(first_slice_after, &[1, 2, 3, 4, 5]);
        assert_eq!(second_slice_after, &[]);
    }

    #[test]
    fn test_back() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        assert_eq!(cdq.back(), Some(&5));
    }

    #[test]
    fn test_iter() {
        let cdq = cdeque!(1, 2, 3, 4, 5);
        let collected: Vec<&u8> = cdq.iter().collect();
        assert_eq!(collected, vec![&1, &2, &3, &4, &5]);

        // Test with empty deque
        let empty_cdq = CircularDeque::<u8>::new();
        let empty_collected: Vec<&u8> = empty_cdq.iter().collect();
        assert_eq!(empty_collected, Vec::<&u8>::new());

        // Test with single element
        let single_cdq = cdeque!(42);
        let single_collected: Vec<&u8> = single_cdq.iter().collect();
        assert_eq!(single_collected, vec![&42]);

        // Test iterator size hint
        let cdq = cdeque!(1, 2, 3);
        let mut iter = cdq.iter();
        assert_eq!(iter.size_hint(), (3, Some(3)));
        assert_eq!(iter.len(), 3);

        iter.next();
        assert_eq!(iter.size_hint(), (2, Some(2)));
        assert_eq!(iter.len(), 2);

        iter.next();
        iter.next();
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.len(), 0);
    }

    #[test]
    fn test_iter_wrapped() {
        // Test iterator on a wrapped deque
        let mut cdq = CircularDeque::with_capacity(5);
        cdq.push_back(3);
        cdq.push_back(4);
        cdq.push_back(5);
        cdq.push_front(2);
        cdq.push_front(1);

        // Now elements are: [1, 2, 3, 4, 5] but wrapped in memory
        let collected: Vec<&u8> = cdq.iter().collect();
        assert_eq!(collected, vec![&1, &2, &3, &4, &5]);

        // Test partial iteration
        let mut iter = cdq.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));

        let remaining: Vec<&u8> = iter.collect();
        assert_eq!(remaining, vec![&4, &5]);
    }

    #[test]
    fn test_iter_mut() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);

        // Test basic mutable iteration
        for item in cdq.iter_mut() {
            *item *= 2;
        }

        let collected: Vec<&u8> = cdq.iter().collect();
        assert_eq!(collected, vec![&2, &4, &6, &8, &10]);

        // Test with empty deque
        let mut empty_cdq = CircularDeque::<u8>::new();
        let empty_collected: Vec<&mut u8> = empty_cdq.iter_mut().collect();
        assert_eq!(empty_collected, Vec::<&mut u8>::new());

        // Test with single element
        let mut single_cdq = cdeque!(42);
        for item in single_cdq.iter_mut() {
            *item += 1;
        }
        assert_eq!(single_cdq.get(0), Some(&43));

        // Test iterator size hint
        let mut cdq = cdeque!(1, 2, 3);
        let mut iter = cdq.iter_mut();
        assert_eq!(iter.size_hint(), (3, Some(3)));
        assert_eq!(iter.len(), 3);

        iter.next();
        assert_eq!(iter.size_hint(), (2, Some(2)));
        assert_eq!(iter.len(), 2);

        iter.next();
        iter.next();
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.len(), 0);
    }

    #[test]
    fn test_iter_mut_wrapped() {
        // Test mutable iterator on a wrapped deque
        let mut cdq = CircularDeque::with_capacity(5);
        cdq.push_back(3);
        cdq.push_back(4);
        cdq.push_back(5);
        cdq.push_front(2);
        cdq.push_front(1);

        // Now elements are: [1, 2, 3, 4, 5] but wrapped in memory
        // Double each element
        for item in cdq.iter_mut() {
            *item *= 2;
        }

        let collected: Vec<&u8> = cdq.iter().collect();
        assert_eq!(collected, vec![&2, &4, &6, &8, &10]);

        // Test partial iteration
        let mut iter = cdq.iter_mut();
        if let Some(first) = iter.next() {
            *first += 1; // 2 + 1 = 3
        }
        if let Some(second) = iter.next() {
            *second += 1; // 4 + 1 = 5
        }

        let final_collected: Vec<&u8> = cdq.iter().collect();
        assert_eq!(final_collected, vec![&3, &5, &6, &8, &10]);
    }

    #[test]
    fn test_range() {
        let cdq = cdeque!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10);

        // Test basic range
        let values: Vec<&u8> = cdq.range(1..4).collect();
        assert_eq!(values, vec![&2, &3, &4]);

        // Test inclusive range
        let values: Vec<&u8> = cdq.range(1..=4).collect();
        assert_eq!(values, vec![&2, &3, &4, &5]);

        // Test open-ended range
        let values: Vec<&u8> = cdq.range(7..).collect();
        assert_eq!(values, vec![&8, &9, &10]);

        // Test range from beginning
        let values: Vec<&u8> = cdq.range(..3).collect();
        assert_eq!(values, vec![&1, &2, &3]);

        // Test full range
        let values: Vec<&u8> = cdq.range(..).collect();
        assert_eq!(values, vec![&1, &2, &3, &4, &5, &6, &7, &8, &9, &10]);

        // Test empty range
        let values: Vec<&u8> = cdq.range(3..3).collect();
        assert_eq!(values, Vec::<&u8>::new());

        // Test single element range
        let values: Vec<&u8> = cdq.range(5..6).collect();
        assert_eq!(values, vec![&6]);

        // Test range with wrapped deque
        let mut wrapped_cdq = CircularDeque::with_capacity(10);
        wrapped_cdq.push_back(6);
        wrapped_cdq.push_back(7);
        wrapped_cdq.push_back(8);
        wrapped_cdq.push_front(5);
        wrapped_cdq.push_front(4);
        wrapped_cdq.push_front(3);
        wrapped_cdq.push_front(2);
        wrapped_cdq.push_front(1);

        // Elements should be: [1, 2, 3, 4, 5, 6, 7, 8]
        let values: Vec<&u8> = wrapped_cdq.range(2..6).collect();
        assert_eq!(values, vec![&3, &4, &5, &6]);

        // Test range size hints
        let mut range_iter = cdq.range(2..5);
        assert_eq!(range_iter.size_hint(), (3, Some(3)));
        assert_eq!(range_iter.len(), 3);

        range_iter.next();
        assert_eq!(range_iter.size_hint(), (2, Some(2)));
        assert_eq!(range_iter.len(), 2);
    }

    #[test]
    #[should_panic(expected = "range start is greater than end")]
    fn test_range_invalid_start_greater_than_end() {
        let cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.range(3..2);
    }

    #[test]
    #[should_panic(expected = "range end is greater than length")]
    fn test_range_invalid_end_greater_than_len() {
        let cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.range(1..10);
    }

    #[test]
    fn test_range_mut() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10);

        // Test basic range mutation
        for item in cdq.range_mut(1..4) {
            *item *= 2;
        }
        assert_eq!(cdq, cdeque!(1, 4, 6, 8, 5, 6, 7, 8, 9, 10));

        // Test inclusive range mutation
        for item in cdq.range_mut(4..=6) {
            *item += 10;
        }
        assert_eq!(cdq, cdeque!(1, 4, 6, 8, 15, 16, 17, 8, 9, 10));

        // Test open-ended range mutation
        for item in cdq.range_mut(7..) {
            *item = 0;
        }
        assert_eq!(cdq, cdeque!(1, 4, 6, 8, 15, 16, 17, 0, 0, 0));

        // Test range from beginning
        for item in cdq.range_mut(..3) {
            *item = 99;
        }
        assert_eq!(cdq, cdeque!(99, 99, 99, 8, 15, 16, 17, 0, 0, 0));

        // Test full range mutation
        for item in cdq.range_mut(..) {
            *item = 42;
        }
        assert_eq!(cdq, cdeque!(42, 42, 42, 42, 42, 42, 42, 42, 42, 42));

        // Test empty range
        let mut empty_count = 0;
        for _item in cdq.range_mut(3..3) {
            empty_count += 1;
        }
        assert_eq!(empty_count, 0);

        // Test single element range
        for item in cdq.range_mut(5..6) {
            *item = 100;
        }
        assert_eq!(cdq, cdeque!(42, 42, 42, 42, 42, 100, 42, 42, 42, 42));

        // Test range with wrapped deque
        let mut wrapped_cdq = CircularDeque::with_capacity(10);
        wrapped_cdq.push_back(6);
        wrapped_cdq.push_back(7);
        wrapped_cdq.push_back(8);
        wrapped_cdq.push_front(5);
        wrapped_cdq.push_front(4);
        wrapped_cdq.push_front(3);
        wrapped_cdq.push_front(2);
        wrapped_cdq.push_front(1);

        // Elements should be: [1, 2, 3, 4, 5, 6, 7, 8]
        for item in wrapped_cdq.range_mut(2..6) {
            *item *= 10;
        }

        let expected = cdeque!(1, 2, 30, 40, 50, 60, 7, 8);
        assert_eq!(wrapped_cdq, expected);

        // Test range size hints
        let mut range_iter = cdq.range_mut(2..5);
        assert_eq!(range_iter.size_hint(), (3, Some(3)));
        assert_eq!(range_iter.len(), 3);

        range_iter.next();
        assert_eq!(range_iter.size_hint(), (2, Some(2)));
        assert_eq!(range_iter.len(), 2);
    }

    #[test]
    #[should_panic(expected = "range start is greater than end")]
    fn test_range_mut_invalid_start_greater_than_end() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.range_mut(3..2);
    }

    #[test]
    #[should_panic(expected = "range end is greater than length")]
    fn test_range_mut_invalid_end_greater_than_len() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.range_mut(1..10);
    }

    #[test]
    fn test_shrink_to_fit() {
        // Test shrinking when capacity > length
        let mut cdq = cdeque!(1, 2, 3, 4);
        assert_eq!(cdq.len(), 4);
        assert_eq!(cdq.capacity(), 4);

        // Reserve extra capacity
        cdq.reserve(8);
        assert_eq!(cdq.len(), 4);
        assert_eq!(cdq.capacity(), 12);

        // Shrink to fit
        cdq.shrink_to_fit();
        assert_eq!(cdq.len(), 4);
        assert_eq!(cdq.capacity(), 4);
        assert_eq!(cdq, cdeque!(1, 2, 3, 4));

        // Test shrinking empty deque
        let mut empty_cdq: CircularDeque<i32> = CircularDeque::new();
        empty_cdq.reserve(10);
        assert_eq!(empty_cdq.len(), 0);
        assert_eq!(empty_cdq.capacity(), 10);

        empty_cdq.shrink_to_fit();
        assert_eq!(empty_cdq.len(), 0);
        assert_eq!(empty_cdq.capacity(), 0);

        // Test when capacity already equals length
        let mut cdq2 = cdeque!(5, 6, 7);
        let original_capacity = cdq2.capacity();
        cdq2.shrink_to_fit();
        assert_eq!(cdq2.capacity(), original_capacity);
        assert_eq!(cdq2, cdeque!(5, 6, 7));
    }

    #[test]
    fn test_shrink_to() {
        // Test shrinking to a specific capacity larger than length
        let mut cdq = cdeque!(1, 2, 3, 4);
        assert_eq!(cdq.len(), 4);
        assert_eq!(cdq.capacity(), 4);

        // Reserve extra capacity
        cdq.reserve(12);
        assert_eq!(cdq.len(), 4);
        assert_eq!(cdq.capacity(), 16);

        // Shrink to 8 (larger than length)
        cdq.shrink_to(8);
        assert_eq!(cdq.len(), 4);
        assert_eq!(cdq.capacity(), 8);
        assert_eq!(cdq, cdeque!(1, 2, 3, 4));

        // Test shrinking to capacity smaller than length (should use length)
        cdq.shrink_to(2);
        assert_eq!(cdq.len(), 4);
        assert_eq!(cdq.capacity(), 4);
        assert_eq!(cdq, cdeque!(1, 2, 3, 4));

        // Test shrinking empty deque to specific capacity
        let mut empty_cdq: CircularDeque<i32> = CircularDeque::new();
        empty_cdq.reserve(20);
        assert_eq!(empty_cdq.len(), 0);
        assert_eq!(empty_cdq.capacity(), 20);

        empty_cdq.shrink_to(5);
        assert_eq!(empty_cdq.len(), 0);
        assert_eq!(empty_cdq.capacity(), 5);

        // Test shrinking empty deque to 0
        empty_cdq.shrink_to(0);
        assert_eq!(empty_cdq.len(), 0);
        assert_eq!(empty_cdq.capacity(), 0);

        // Test when current capacity is already less than or equal to min_capacity (no-op)
        let mut cdq2 = cdeque!(10, 20, 30);
        let original_capacity = cdq2.capacity();
        cdq2.shrink_to(10);
        assert_eq!(cdq2.capacity(), original_capacity);
        assert_eq!(cdq2, cdeque!(10, 20, 30));

        // Test with exact capacity match
        let mut cdq3 = cdeque!(1, 2, 3, 4, 5);
        cdq3.reserve(5);
        let current_capacity = cdq3.capacity();
        cdq3.shrink_to(current_capacity);
        assert_eq!(cdq3.capacity(), current_capacity);
        assert_eq!(cdq3, cdeque!(1, 2, 3, 4, 5));
    }

    #[test]
    fn test_resize() {
        // Test growing the deque
        let mut cdq = cdeque!(1, 2, 3);
        assert_eq!(cdq.len(), 3);

        cdq.resize(6, 42);
        assert_eq!(cdq.len(), 6);
        assert_eq!(cdq[0], 1);
        assert_eq!(cdq[1], 2);
        assert_eq!(cdq[2], 3);
        assert_eq!(cdq[3], 42);
        assert_eq!(cdq[4], 42);
        assert_eq!(cdq[5], 42);

        // Test shrinking the deque
        cdq.resize(2, 999);
        assert_eq!(cdq.len(), 2);
        assert_eq!(cdq[0], 1);
        assert_eq!(cdq[1], 2);

        // Test resizing to the same length (no-op)
        let original_len = cdq.len();
        cdq.resize(2, 123);
        assert_eq!(cdq.len(), original_len);
        assert_eq!(cdq[0], 1);
        assert_eq!(cdq[1], 2);

        // Test resizing empty deque
        let mut empty_cdq: CircularDeque<i32> = CircularDeque::new();
        empty_cdq.resize(4, 7);
        assert_eq!(empty_cdq.len(), 4);
        assert_eq!(empty_cdq[0], 7);
        assert_eq!(empty_cdq[1], 7);
        assert_eq!(empty_cdq[2], 7);
        assert_eq!(empty_cdq[3], 7);

        // Test resizing to 0 (truncate all)
        empty_cdq.resize(0, 999);
        assert_eq!(empty_cdq.len(), 0);
        assert!(empty_cdq.is_empty());

        // Test with string values to ensure Clone works
        let mut str_cdq = CircularDeque::new();
        str_cdq.push_back("hello".to_string());
        str_cdq.push_back("world".to_string());

        str_cdq.resize(4, "test".to_string());
        assert_eq!(str_cdq.len(), 4);
        assert_eq!(str_cdq[0], "hello");
        assert_eq!(str_cdq[1], "world");
        assert_eq!(str_cdq[2], "test");
        assert_eq!(str_cdq[3], "test");
    }

    #[test]
    fn test_resize_with() {
        // Test growing the deque with a generator function
        let mut cdq = cdeque!(1, 2, 3);
        assert_eq!(cdq.len(), 3);

        let mut counter = 10;
        cdq.resize_with(6, || {
            counter += 1;
            counter
        });

        assert_eq!(cdq.len(), 6);
        assert_eq!(cdq[0], 1);
        assert_eq!(cdq[1], 2);
        assert_eq!(cdq[2], 3);
        assert_eq!(cdq[3], 11);
        assert_eq!(cdq[4], 12);
        assert_eq!(cdq[5], 13);

        // Test shrinking the deque (generator should not be called)
        let mut panic_called = false;
        cdq.resize_with(2, || {
            panic_called = true;
            999
        });
        assert_eq!(cdq.len(), 2);
        assert_eq!(cdq[0], 1);
        assert_eq!(cdq[1], 2);
        assert!(!panic_called);

        // Test resizing to the same length (no-op, generator should not be called)
        let original_len = cdq.len();
        let mut generator_called = false;
        cdq.resize_with(2, || {
            generator_called = true;
            123
        });
        assert_eq!(cdq.len(), original_len);
        assert_eq!(cdq[0], 1);
        assert_eq!(cdq[1], 2);
        assert!(!generator_called);

        // Test resizing empty deque
        let mut empty_cdq: CircularDeque<i32> = CircularDeque::new();
        empty_cdq.resize_with(4, || 42);
        assert_eq!(empty_cdq.len(), 4);
        assert_eq!(empty_cdq[0], 42);
        assert_eq!(empty_cdq[1], 42);
        assert_eq!(empty_cdq[2], 42);
        assert_eq!(empty_cdq[3], 42);

        // Test resizing to 0 (truncate all)
        empty_cdq.resize_with(0, || panic!("Should not be called"));
        assert_eq!(empty_cdq.len(), 0);
        assert!(empty_cdq.is_empty());

        // Test with more complex generator producing different values
        let mut str_cdq = CircularDeque::new();
        str_cdq.push_back("hello".to_string());

        let mut index = 0;
        str_cdq.resize_with(4, || {
            let result = format!("item_{}", index);
            index += 1;
            result
        });

        assert_eq!(str_cdq.len(), 4);
        assert_eq!(str_cdq[0], "hello");
        assert_eq!(str_cdq[1], "item_0");
        assert_eq!(str_cdq[2], "item_1");
        assert_eq!(str_cdq[3], "item_2");

        // Test generator that captures environment
        let base_value = 100;
        let mut multiplier = 1;
        let mut math_cdq: CircularDeque<i32> = CircularDeque::new();
        math_cdq.resize_with(3, || {
            let result = base_value * multiplier;
            multiplier += 1;
            result
        });

        assert_eq!(math_cdq.len(), 3);
        assert_eq!(math_cdq[0], 100);
        assert_eq!(math_cdq[1], 200);
        assert_eq!(math_cdq[2], 300);
    }

    #[test]
    fn test_drain() {
        // Test basic drain functionality
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        let drained: Vec<i32> = cdq.drain(1..4).collect();
        assert_eq!(drained, vec![2, 3, 4]);
        assert_eq!(cdq.len(), 2);
        assert_eq!(cdq[0], 1);
        assert_eq!(cdq[1], 5);

        // Test draining all elements
        let mut cdq2 = cdeque!(10, 20, 30);
        let drained: Vec<i32> = cdq2.drain(..).collect();
        assert_eq!(drained, vec![10, 20, 30]);
        assert_eq!(cdq2.len(), 0);
        assert!(cdq2.is_empty());

        // Test draining from the front
        let mut cdq3 = cdeque!(1, 2, 3, 4);
        let drained: Vec<i32> = cdq3.drain(..2).collect();
        assert_eq!(drained, vec![1, 2]);
        assert_eq!(cdq3.len(), 2);
        assert_eq!(cdq3[0], 3);
        assert_eq!(cdq3[1], 4);

        // Test draining from the back
        let mut cdq4 = cdeque!(1, 2, 3, 4);
        let drained: Vec<i32> = cdq4.drain(2..).collect();
        assert_eq!(drained, vec![3, 4]);
        assert_eq!(cdq4.len(), 2);
        assert_eq!(cdq4[0], 1);
        assert_eq!(cdq4[1], 2);

        // Test draining empty range
        let mut cdq5 = cdeque!(1, 2, 3);
        let drained: Vec<i32> = cdq5.drain(1..1).collect();
        assert_eq!(drained, vec![]);
        assert_eq!(cdq5.len(), 3);
        assert_eq!(cdq5, cdeque!(1, 2, 3));

        // Test draining single element
        let mut cdq6 = cdeque!(1, 2, 3);
        let drained: Vec<i32> = cdq6.drain(1..2).collect();
        assert_eq!(drained, vec![2]);
        assert_eq!(cdq6.len(), 2);
        assert_eq!(cdq6[0], 1);
        assert_eq!(cdq6[1], 3);

        // Test with string elements
        let mut str_cdq = cdeque!("a", "b", "c", "d");
        let drained: Vec<&str> = str_cdq.drain(1..3).collect();
        assert_eq!(drained, vec!["b", "c"]);
        assert_eq!(str_cdq.len(), 2);
        assert_eq!(str_cdq[0], "a");
        assert_eq!(str_cdq[1], "d");
    }

    #[test]
    #[should_panic(expected = "range start is greater than range end")]
    fn test_drain_invalid_range() {
        let mut cdq = cdeque!(1, 2, 3);
        cdq.drain(2..1);
    }

    #[test]
    #[should_panic(expected = "range end is greater than length")]
    fn test_drain_out_of_bounds() {
        let mut cdq = cdeque!(1, 2, 3);
        cdq.drain(1..5);
    }

    #[test]
    fn test_split_off() {
        // Test basic split functionality
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        let split_deque = cdq.split_off(2);

        assert_eq!(cdq.len(), 2);
        assert_eq!(cdq[0], 1);
        assert_eq!(cdq[1], 2);

        assert_eq!(split_deque.len(), 3);
        assert_eq!(split_deque[0], 3);
        assert_eq!(split_deque[1], 4);
        assert_eq!(split_deque[2], 5);

        // Test splitting at the beginning
        let mut cdq2 = cdeque!(1, 2, 3);
        let split_deque2 = cdq2.split_off(0);

        assert_eq!(cdq2.len(), 0);
        assert!(cdq2.is_empty());

        assert_eq!(split_deque2.len(), 3);
        assert_eq!(split_deque2[0], 1);
        assert_eq!(split_deque2[1], 2);
        assert_eq!(split_deque2[2], 3);

        // Test splitting at the end
        let mut cdq3 = cdeque!(1, 2, 3);
        let split_deque3 = cdq3.split_off(3);

        assert_eq!(cdq3.len(), 3);
        assert_eq!(cdq3[0], 1);
        assert_eq!(cdq3[1], 2);
        assert_eq!(cdq3[2], 3);

        assert_eq!(split_deque3.len(), 0);
        assert!(split_deque3.is_empty());

        // Test splitting single element deque
        let mut cdq4 = cdeque!(42);
        let split_deque4 = cdq4.split_off(0);

        assert_eq!(cdq4.len(), 0);
        assert!(cdq4.is_empty());

        assert_eq!(split_deque4.len(), 1);
        assert_eq!(split_deque4[0], 42);

        // Test splitting at index 1 of two-element deque
        let mut cdq5 = cdeque!(10, 20);
        let split_deque5 = cdq5.split_off(1);

        assert_eq!(cdq5.len(), 1);
        assert_eq!(cdq5[0], 10);

        assert_eq!(split_deque5.len(), 1);
        assert_eq!(split_deque5[0], 20);

        // Test with string elements
        let mut str_cdq = cdeque!("a", "b", "c", "d");
        let split_str_deque = str_cdq.split_off(2);

        assert_eq!(str_cdq.len(), 2);
        assert_eq!(str_cdq[0], "a");
        assert_eq!(str_cdq[1], "b");

        assert_eq!(split_str_deque.len(), 2);
        assert_eq!(split_str_deque[0], "c");
        assert_eq!(split_str_deque[1], "d");

        // Test splitting empty deque
        let mut empty_cdq: CircularDeque<i32> = CircularDeque::new();
        let split_empty = empty_cdq.split_off(0);

        assert_eq!(empty_cdq.len(), 0);
        assert_eq!(split_empty.len(), 0);
        assert!(empty_cdq.is_empty());
        assert!(split_empty.is_empty());
    }

    #[test]
    #[should_panic(expected = "split index 5 is greater than length 3")]
    fn test_split_off_out_of_bounds() {
        let mut cdq = cdeque!(1, 2, 3);
        cdq.split_off(5);
    }

    #[test]
    fn test_partition_point() {
        // Test basic partition functionality
        let cdq = cdeque!(1, 2, 3, 3, 5, 6, 7);
        let i = cdq.partition_point(|&x| x < 5);
        assert_eq!(i, 4);
        assert!(cdq.iter().take(i).all(|&x| x < 5));
        assert!(cdq.iter().skip(i).all(|&x| !(x < 5)));

        // Test all elements match predicate
        let cdq2 = cdeque!(2, 4, 8);
        assert_eq!(cdq2.partition_point(|&x| x < 100), 3);

        // Test no elements match predicate
        let cdq3 = cdeque!(2, 4, 8);
        assert_eq!(cdq3.partition_point(|&x| x > 100), 0);

        // Test empty deque
        let empty_cdq: CircularDeque<i32> = CircularDeque::new();
        assert_eq!(empty_cdq.partition_point(|&x| x < 100), 0);

        // Test single element - matches
        let cdq4 = cdeque!(5);
        assert_eq!(cdq4.partition_point(|&x| x < 10), 1);

        // Test single element - doesn't match
        let cdq5 = cdeque!(5);
        assert_eq!(cdq5.partition_point(|&x| x > 10), 0);

        // Test with all elements matching
        let cdq6 = cdeque!(1, 2, 3, 4);
        assert_eq!(cdq6.partition_point(|&x| x < 10), 4);

        // Test with no elements matching
        let cdq7 = cdeque!(1, 2, 3, 4);
        assert_eq!(cdq7.partition_point(|&x| x > 10), 0);

        // Test partition with different predicate
        let cdq8 = cdeque!(1, 3, 5, 7, 2, 4, 6, 8);
        let i = cdq8.partition_point(|&x| x % 2 == 1);
        assert_eq!(i, 4);
        assert!(cdq8.iter().take(i).all(|&x| x % 2 == 1));
        assert!(cdq8.iter().skip(i).all(|&x| x % 2 == 0));

        // Test with strings
        let str_cdq = cdeque!("a", "bb", "ccc", "dddd", "eeeee");
        let i = str_cdq.partition_point(|&s| s.len() < 4);
        assert_eq!(i, 3);
        assert!(str_cdq.iter().take(i).all(|&s| s.len() < 4));
        assert!(str_cdq.iter().skip(i).all(|&s| s.len() >= 4));

        // Test with repeated elements at boundary
        let cdq9 = cdeque!(1, 2, 3, 3, 3, 4, 5);
        let i = cdq9.partition_point(|&x| x <= 3);
        assert_eq!(i, 5);
        assert!(cdq9.iter().take(i).all(|&x| x <= 3));
        assert!(cdq9.iter().skip(i).all(|&x| x > 3));

        // Test binary search behavior - sorted array
        let sorted_cdq = cdeque!(1, 3, 5, 7, 9, 11, 13);
        let i = sorted_cdq.partition_point(|&x| x < 8);
        assert_eq!(i, 4);
        assert!(sorted_cdq.iter().take(i).all(|&x| x < 8));
        assert!(sorted_cdq.iter().skip(i).all(|&x| x >= 8));
    }

    #[test]
    fn test_hash_trait() {
        use std::collections::hash_map::DefaultHasher;
        use std::collections::{HashMap, HashSet};
        use std::hash::{Hash, Hasher};

        // Test that equal deques have equal hashes
        let mut deque1 = cdeque!(1, 2, 3, 4, 5);
        let mut deque2 = cdeque!(1, 2, 3, 4, 5);

        let mut hasher1 = DefaultHasher::new();
        let mut hasher2 = DefaultHasher::new();

        deque1.hash(&mut hasher1);
        deque2.hash(&mut hasher2);

        assert_eq!(hasher1.finish(), hasher2.finish());

        // Test that different deques have different hashes
        let deque3 = cdeque!(1, 2, 3, 4, 6); // Different last element
        let mut hasher3 = DefaultHasher::new();
        deque3.hash(&mut hasher3);

        assert_ne!(hasher1.finish(), hasher3.finish());

        // Test that order matters for hashing
        let deque4 = cdeque!(5, 4, 3, 2, 1); // Reverse order
        let mut hasher4 = DefaultHasher::new();
        deque4.hash(&mut hasher4);

        assert_ne!(hasher1.finish(), hasher4.finish());

        // Test using deques as HashMap keys
        let mut map: HashMap<CircularDeque<i32>, String> = HashMap::new();

        let key1 = cdeque!(1, 2, 3);
        let key2 = cdeque!(4, 5, 6);
        let key3 = cdeque!(1, 2, 3); // Same as key1

        map.insert(key1, "first".to_string());
        map.insert(key2, "second".to_string());
        map.insert(key3, "third".to_string()); // Should replace "first"

        assert_eq!(map.len(), 2);

        let lookup_key = cdeque!(1, 2, 3);
        assert_eq!(map.get(&lookup_key), Some(&"third".to_string()));

        // Test using deques in HashSet
        let mut set: HashSet<CircularDeque<i32>> = HashSet::new();

        set.insert(cdeque!(1, 2, 3));
        set.insert(cdeque!(4, 5, 6));
        set.insert(cdeque!(1, 2, 3)); // Duplicate, should not increase size

        assert_eq!(set.len(), 2);

        assert!(set.contains(&cdeque!(1, 2, 3)));
        assert!(set.contains(&cdeque!(4, 5, 6)));
        assert!(!set.contains(&cdeque!(7, 8, 9)));

        // Test empty deques
        let empty1: CircularDeque<i32> = CircularDeque::new();
        let empty2: CircularDeque<i32> = CircularDeque::new();

        let mut hasher_empty1 = DefaultHasher::new();
        let mut hasher_empty2 = DefaultHasher::new();

        empty1.hash(&mut hasher_empty1);
        empty2.hash(&mut hasher_empty2);

        assert_eq!(hasher_empty1.finish(), hasher_empty2.finish());

        // Test single element deques
        let single1 = cdeque!(42);
        let single2 = cdeque!(42);
        let single3 = cdeque!(43);

        let mut hasher_s1 = DefaultHasher::new();
        let mut hasher_s2 = DefaultHasher::new();
        let mut hasher_s3 = DefaultHasher::new();

        single1.hash(&mut hasher_s1);
        single2.hash(&mut hasher_s2);
        single3.hash(&mut hasher_s3);

        assert_eq!(hasher_s1.finish(), hasher_s2.finish());
        assert_ne!(hasher_s1.finish(), hasher_s3.finish());
    }

    #[test]
    fn test_clone_trait() {
        // Test basic cloning
        let mut original = cdeque!(1, 2, 3, 4, 5);
        let cloned = original.clone();

        assert_eq!(original, cloned);
        assert_eq!(cloned.len(), 5);
        assert_eq!(cloned.capacity(), original.capacity());

        // Verify elements are the same
        for i in 0..5 {
            assert_eq!(original[i], cloned[i]);
        }

        // Test independence - modifying one doesn't affect the other
        original.push_back(6);
        assert_eq!(original.len(), 6);
        assert_eq!(cloned.len(), 5);
        assert_ne!(original, cloned);

        // Test cloning empty deque
        let empty: CircularDeque<i32> = CircularDeque::new();
        let empty_clone = empty.clone();
        assert_eq!(empty, empty_clone);
        assert_eq!(empty_clone.len(), 0);

        // Test cloning with complex types
        let mut str_deque = CircularDeque::new();
        str_deque.push_back("hello".to_string());
        str_deque.push_back("world".to_string());

        let str_clone = str_deque.clone();
        assert_eq!(str_deque, str_clone);
        assert_eq!(str_clone[0], "hello");
        assert_eq!(str_clone[1], "world");

        // Modify original string and verify independence
        str_deque[0] = "modified".to_string();
        assert_ne!(str_deque, str_clone);
        assert_eq!(str_clone[0], "hello"); // Clone unchanged
    }

    #[test]
    fn test_default_trait() {
        // Test default creation
        let deque: CircularDeque<i32> = Default::default();
        assert_eq!(deque.len(), 0);
        assert_eq!(deque.capacity(), 0);
        assert!(deque.is_empty());

        // Test equivalence with new()
        let new_deque = CircularDeque::<i32>::new();
        assert_eq!(deque.len(), new_deque.len());
        assert_eq!(deque.capacity(), new_deque.capacity());

        // Test in generic context
        fn create_default_collection<T: Default>() -> T {
            T::default()
        }

        let generic_deque: CircularDeque<String> = create_default_collection();
        assert!(generic_deque.is_empty());
        assert_eq!(generic_deque.capacity(), 0);

        // Test with different types
        let bool_deque: CircularDeque<bool> = Default::default();
        let vec_deque: CircularDeque<Vec<i32>> = Default::default();

        assert!(bool_deque.is_empty());
        assert!(vec_deque.is_empty());
    }

    #[test]
    fn test_into_iterator_trait() {
        // Test consuming iteration (IntoIterator for CircularDeque<T>)
        let mut deque = cdeque!(1, 2, 3, 4, 5);
        let collected: Vec<i32> = deque.into_iter().collect();
        assert_eq!(collected, vec![1, 2, 3, 4, 5]);
        // deque is now consumed and cannot be used

        // Test reference iteration (IntoIterator for &CircularDeque<T>)
        let deque = cdeque!(10, 20, 30);
        let collected: Vec<&i32> = (&deque).into_iter().collect();
        assert_eq!(collected, vec![&10, &20, &30]);

        // deque is still usable
        assert_eq!(deque.len(), 3);
        assert_eq!(deque[0], 10);

        // Test mutable reference iteration (IntoIterator for &mut CircularDeque<T>)
        let mut deque = cdeque!(1, 2, 3);

        // Modify elements through mutable iterator
        for item in &mut deque {
            *item *= 2;
        }

        assert_eq!(deque[0], 2);
        assert_eq!(deque[1], 4);
        assert_eq!(deque[2], 6);

        // Test that deque is still usable after mutable iteration
        assert_eq!(deque.len(), 3);
        deque.push_back(8);
        assert_eq!(deque.len(), 4);

        // Test for loop syntax (uses IntoIterator)
        let test_deque = cdeque!("a", "b", "c");
        let mut result = Vec::new();

        for item in &test_deque {
            result.push(*item);
        }

        assert_eq!(result, vec!["a", "b", "c"]);
        assert_eq!(test_deque.len(), 3); // Still usable

        // Test empty deque iteration
        let empty: CircularDeque<i32> = CircularDeque::new();
        let empty_collected: Vec<&i32> = (&empty).into_iter().collect();
        assert_eq!(empty_collected, Vec::<&i32>::new());
    }

    #[test]
    fn test_from_iterator_trait() {
        // Test basic collection from iterator
        let vec = vec![1, 2, 3, 4, 5];
        let deque: CircularDeque<i32> = vec.into_iter().collect();

        assert_eq!(deque.len(), 5);
        assert_eq!(deque[0], 1);
        assert_eq!(deque[4], 5);

        // Test with iterator adaptors
        let deque: CircularDeque<i32> = (0..10).filter(|&x| x % 2 == 0).map(|x| x * x).collect();

        assert_eq!(deque.len(), 5);
        assert_eq!(deque[0], 0); // 0^2
        assert_eq!(deque[1], 4); // 2^2
        assert_eq!(deque[2], 16); // 4^2
        assert_eq!(deque[3], 36); // 6^2
        assert_eq!(deque[4], 64); // 8^2

        // Test from string chars
        let deque: CircularDeque<char> = "hello".chars().collect();
        assert_eq!(deque.len(), 5);
        assert_eq!(deque[0], 'h');
        assert_eq!(deque[1], 'e');
        assert_eq!(deque[4], 'o');

        // Test empty iterator
        let empty_vec: Vec<i32> = vec![];
        let empty_deque: CircularDeque<i32> = empty_vec.into_iter().collect();
        assert_eq!(empty_deque.len(), 0);
        assert!(empty_deque.is_empty());

        // Test single element
        let single_deque: CircularDeque<i32> = std::iter::once(42).collect();
        assert_eq!(single_deque.len(), 1);
        assert_eq!(single_deque[0], 42);

        // Test with complex types
        let strings = vec!["hello".to_string(), "world".to_string()];
        let string_deque: CircularDeque<String> = strings.into_iter().collect();
        assert_eq!(string_deque.len(), 2);
        assert_eq!(string_deque[0], "hello");
        assert_eq!(string_deque[1], "world");
    }

    #[test]
    fn test_extend_trait() {
        // Test Extend<T>
        let mut deque = cdeque!(1, 2);
        deque.extend(vec![3, 4, 5]);

        assert_eq!(deque.len(), 5);
        assert_eq!(deque, cdeque!(1, 2, 3, 4, 5));

        // Test extending with iterator
        let mut deque2 = cdeque!(10);
        deque2.extend((20..=50).step_by(10));

        assert_eq!(deque2.len(), 5);
        assert_eq!(deque2, cdeque!(10, 20, 30, 40, 50));

        // Test extending empty deque
        let mut empty_deque = CircularDeque::new();
        empty_deque.extend(vec![1, 2, 3]);

        assert_eq!(empty_deque.len(), 3);
        assert_eq!(empty_deque, cdeque!(1, 2, 3));

        // Test Extend<&T> with cloning
        let mut deque3 = CircularDeque::new();
        deque3.push_back("a".to_string());
        deque3.push_back("b".to_string());
        let source = vec!["c".to_string(), "d".to_string()];
        deque3.extend(&source);

        assert_eq!(deque3.len(), 4);
        assert_eq!(deque3[0], "a");
        assert_eq!(deque3[3], "d");

        // Source should still be available (not moved)
        assert_eq!(source.len(), 2);
        assert_eq!(source[0], "c");

        // Test extending with references to primitives
        let mut int_deque = cdeque!(1, 2);
        let int_source = vec![3, 4, 5];
        int_deque.extend(&int_source);

        assert_eq!(int_deque.len(), 5);
        assert_eq!(int_deque, cdeque!(1, 2, 3, 4, 5));
        assert_eq!(int_source.len(), 3); // Source unchanged

        // Test extending with empty iterator
        let mut deque4 = cdeque!(1, 2, 3);
        let empty_vec: Vec<i32> = vec![];
        deque4.extend(empty_vec);

        assert_eq!(deque4.len(), 3);
        assert_eq!(deque4, cdeque!(1, 2, 3));
    }

    #[test]
    fn test_from_vec_trait() {
        // Test basic conversion
        let vec = vec![1, 2, 3, 4, 5];
        let deque = CircularDeque::from(vec);

        assert_eq!(deque.len(), 5);
        assert_eq!(deque[0], 1);
        assert_eq!(deque[4], 5);

        // Test with complex types
        let string_vec = vec!["hello".to_string(), "world".to_string()];
        let string_deque = CircularDeque::from(string_vec);

        assert_eq!(string_deque.len(), 2);
        assert_eq!(string_deque[0], "hello");
        assert_eq!(string_deque[1], "world");

        // Test empty vector
        let empty_vec: Vec<i32> = vec![];
        let empty_deque = CircularDeque::from(empty_vec);

        assert_eq!(empty_deque.len(), 0);
        assert!(empty_deque.is_empty());

        // Test single element
        let single_vec = vec![42];
        let single_deque = CircularDeque::from(single_vec);

        assert_eq!(single_deque.len(), 1);
        assert_eq!(single_deque[0], 42);

        // Test using Into syntax
        let vec2 = vec![10, 20, 30];
        let deque2: CircularDeque<i32> = vec2.into();

        assert_eq!(deque2.len(), 3);
        assert_eq!(deque2[0], 10);
        assert_eq!(deque2[2], 30);

        // Test large vector
        let large_vec: Vec<i32> = (0..1000).collect();
        let large_deque = CircularDeque::from(large_vec);

        assert_eq!(large_deque.len(), 1000);
        assert_eq!(large_deque[0], 0);
        assert_eq!(large_deque[999], 999);

        // Test with nested vectors
        let nested_vec = vec![vec![1, 2], vec![3, 4], vec![5, 6]];
        let nested_deque = CircularDeque::from(nested_vec);

        assert_eq!(nested_deque.len(), 3);
        assert_eq!(nested_deque[0], vec![1, 2]);
        assert_eq!(nested_deque[2], vec![5, 6]);
    }

    #[test]
    fn test_index_trait() {
        // Test basic indexing
        let mut deque = CircularDeque::new();
        deque.push_back("first");
        deque.push_back("second");
        deque.push_back("third");

        // Test valid indices
        assert_eq!(deque[0], "first");
        assert_eq!(deque[1], "second");
        assert_eq!(deque[2], "third");

        // Test indexing after rotation
        deque.push_front("zero");
        assert_eq!(deque[0], "zero");
        assert_eq!(deque[1], "first");
        assert_eq!(deque[2], "second");
        assert_eq!(deque[3], "third");

        // Test indexing with complex rotation
        let mut rotated_deque = CircularDeque::new();
        for i in 0..10 {
            rotated_deque.push_back(i);
        }

        // Remove some from front and back to create rotation
        rotated_deque.pop_front();
        rotated_deque.pop_front();
        rotated_deque.pop_back();
        rotated_deque.push_front(100);
        rotated_deque.push_back(200);

        // Verify indexing still works correctly
        assert_eq!(rotated_deque[0], 100);
        assert_eq!(rotated_deque[1], 2);
        assert_eq!(rotated_deque[rotated_deque.len() - 1], 200);

        // Test with single element
        let mut single = CircularDeque::new();
        single.push_back(42);
        assert_eq!(single[0], 42);
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_index_trait_panic_empty() {
        let deque: CircularDeque<i32> = CircularDeque::new();
        let _ = deque[0]; // Should panic
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_index_trait_panic_out_of_bounds() {
        let mut deque = CircularDeque::new();
        deque.push_back(1);
        deque.push_back(2);
        let _ = deque[5]; // Should panic
    }

    #[test]
    fn test_index_mut_trait() {
        // Test basic mutable indexing
        let mut deque = CircularDeque::new();
        deque.push_back(10);
        deque.push_back(20);
        deque.push_back(30);

        // Test mutable access and modification
        deque[0] = 100;
        deque[1] = 200;
        deque[2] = 300;

        assert_eq!(deque[0], 100);
        assert_eq!(deque[1], 200);
        assert_eq!(deque[2], 300);

        // Test mutable indexing after rotation
        deque.push_front(50);
        deque[0] = 500;
        assert_eq!(deque[0], 500);
        assert_eq!(deque[1], 100);

        // Test with complex types
        let mut string_deque = CircularDeque::new();
        string_deque.push_back("hello".to_string());
        string_deque.push_back("world".to_string());

        string_deque[0] = "goodbye".to_string();
        assert_eq!(string_deque[0], "goodbye");
        assert_eq!(string_deque[1], "world");

        // Test mutable indexing with rotation and capacity changes
        let mut dynamic_deque = CircularDeque::new();
        for i in 0..20 {
            dynamic_deque.push_back(i);
        }

        // Create rotation by removing from front and adding to back
        for _ in 0..5 {
            dynamic_deque.pop_front();
            dynamic_deque.push_back(100);
        }

        // Modify elements through mutable indexing
        for i in 0..dynamic_deque.len() {
            dynamic_deque[i] = dynamic_deque[i] * 2;
        }

        // Verify modifications
        assert_eq!(dynamic_deque[0], 10); // Was 5, now 5*2
        assert_eq!(dynamic_deque[dynamic_deque.len() - 1], 200); // Was 100, now 100*2
    }

    #[test]
    #[should_panic(expected = "called `Option::unwrap()` on a `None` value")]
    fn test_index_mut_trait_panic_empty() {
        let mut deque: CircularDeque<i32> = CircularDeque::new();
        deque[0] = 42; // Should panic
    }

    #[test]
    #[should_panic(expected = "called `Option::unwrap()` on a `None` value")]
    fn test_index_mut_trait_panic_out_of_bounds() {
        let mut deque = CircularDeque::new();
        deque.push_back(1);
        deque.push_back(2);
        deque[10] = 42; // Should panic
    }

    #[test]
    fn test_debug_trait() {
        // Test empty deque debug output
        let empty: CircularDeque<i32> = CircularDeque::new();
        let debug_str = format!("{:?}", empty);
        assert!(debug_str.contains("[0,0]:()"));

        // Test single element deque
        let mut single = CircularDeque::new();
        single.push_back(42);
        let debug_str = format!("{:?}", single);
        assert!(debug_str.contains("[1,"));
        assert!(debug_str.contains("]:42"));

        // Test multiple elements
        let mut multi = CircularDeque::new();
        multi.push_back(1);
        multi.push_back(2);
        multi.push_back(3);
        let debug_str = format!("{:?}", multi);
        assert!(debug_str.contains("[3,"));
        assert!(debug_str.contains("]:1,2,3"));

        // Test with strings
        let mut string_deque = CircularDeque::new();
        string_deque.push_back("hello");
        string_deque.push_back("world");
        let debug_str = format!("{:?}", string_deque);
        assert!(debug_str.contains("\"hello\""));
        assert!(debug_str.contains("\"world\""));

        // Test with complex types (nested structures)
        let mut nested = CircularDeque::new();
        nested.push_back(vec![1, 2]);
        nested.push_back(vec![3, 4]);
        let debug_str = format!("{:?}", nested);
        assert!(debug_str.contains("[1, 2]"));
        assert!(debug_str.contains("[3, 4]"));

        // Test after rotation (internal structure should not affect debug output)
        let mut rotated = CircularDeque::new();
        for i in 0..5 {
            rotated.push_back(i);
        }
        rotated.push_front(99);
        rotated.pop_back();
        let debug_str = format!("{:?}", rotated);
        assert!(debug_str.contains("99,0,1,2,3"));

        // Test large deque (should still format correctly)
        let mut large = CircularDeque::new();
        for i in 0..100 {
            large.push_back(i);
        }
        let debug_str = format!("{:?}", large);
        assert!(debug_str.contains("[100,"));
        assert!(debug_str.contains("]:0,1,2"));
        assert!(debug_str.contains("98,99"));
    }

    #[test]
    fn test_ordering_traits() {
        // Test PartialOrd and Ord implementations

        // Test equal deques
        let mut deque1 = CircularDeque::new();
        deque1.push_back(1);
        deque1.push_back(2);
        deque1.push_back(3);

        let mut deque2 = CircularDeque::new();
        deque2.push_back(1);
        deque2.push_back(2);
        deque2.push_back(3);

        assert_eq!(deque1.partial_cmp(&deque2), Some(std::cmp::Ordering::Equal));
        assert_eq!(deque1.cmp(&deque2), std::cmp::Ordering::Equal);
        assert!(deque1 == deque2);
        assert!(!(deque1 < deque2));
        assert!(!(deque1 > deque2));

        // Test lexicographic ordering - first element differs
        let mut deque3 = CircularDeque::new();
        deque3.push_back(0); // Less than deque1's first element
        deque3.push_back(2);
        deque3.push_back(3);

        assert_eq!(deque3.partial_cmp(&deque1), Some(std::cmp::Ordering::Less));
        assert_eq!(deque3.cmp(&deque1), std::cmp::Ordering::Less);
        assert!(deque3 < deque1);
        assert!(deque1 > deque3);

        // Test lexicographic ordering - later element differs
        let mut deque4 = CircularDeque::new();
        deque4.push_back(1);
        deque4.push_back(2);
        deque4.push_back(4); // Greater than deque1's last element

        assert_eq!(
            deque4.partial_cmp(&deque1),
            Some(std::cmp::Ordering::Greater)
        );
        assert_eq!(deque4.cmp(&deque1), std::cmp::Ordering::Greater);
        assert!(deque4 > deque1);
        assert!(deque1 < deque4);

        // Test length-based comparison (shorter vs longer with same prefix)
        let mut short = CircularDeque::new();
        short.push_back(1);
        short.push_back(2);

        let mut long = CircularDeque::new();
        long.push_back(1);
        long.push_back(2);
        long.push_back(3);

        assert_eq!(short.partial_cmp(&long), Some(std::cmp::Ordering::Less));
        assert_eq!(short.cmp(&long), std::cmp::Ordering::Less);
        assert!(short < long);
        assert!(long > short);

        // Test empty deques
        let empty1: CircularDeque<i32> = CircularDeque::new();
        let empty2: CircularDeque<i32> = CircularDeque::new();

        assert_eq!(empty1.partial_cmp(&empty2), Some(std::cmp::Ordering::Equal));
        assert_eq!(empty1.cmp(&empty2), std::cmp::Ordering::Equal);
        assert!(empty1 == empty2);

        // Test empty vs non-empty
        assert_eq!(empty1.partial_cmp(&short), Some(std::cmp::Ordering::Less));
        assert_eq!(empty1.cmp(&short), std::cmp::Ordering::Less);
        assert!(empty1 < short);

        // Test sorting with Vec
        let mut deques = vec![long.clone(), short.clone(), deque4.clone(), deque3.clone()];
        deques.sort();

        // Should be in order: deque3 (starts with 0), short (1,2), long (1,2,3), deque4 (1,2,4)
        assert_eq!(deques[0], deque3);
        assert_eq!(deques[1], short);
        assert_eq!(deques[2], long);
        assert_eq!(deques[3], deque4);

        // Test with strings (lexicographic ordering)
        let mut str_deque1 = CircularDeque::new();
        str_deque1.push_back("apple");
        str_deque1.push_back("banana");

        let mut str_deque2 = CircularDeque::new();
        str_deque2.push_back("apple");
        str_deque2.push_back("cherry");

        assert!(str_deque1 < str_deque2); // "banana" < "cherry"

        // Test ordering with rotation (internal structure shouldn't matter)
        let mut rotated1 = CircularDeque::new();
        rotated1.push_back(2);
        rotated1.push_back(3);
        rotated1.push_front(1); // Now [1, 2, 3] but internally rotated

        let mut normal = CircularDeque::new();
        normal.push_back(1);
        normal.push_back(2);
        normal.push_back(3);

        assert_eq!(rotated1.cmp(&normal), std::cmp::Ordering::Equal);
        assert!(rotated1 == normal);
    }

    #[test]
    fn test_from_array_trait() {
        // Test empty array
        let empty_arr: [i32; 0] = [];
        let empty_deque = CircularDeque::from(empty_arr);
        assert_eq!(empty_deque.len(), 0);
        assert!(empty_deque.is_empty());

        // Test single element array
        let single_arr = [42];
        let single_deque = CircularDeque::from(single_arr);
        assert_eq!(single_deque.len(), 1);
        assert_eq!(single_deque[0], 42);

        // Test multiple elements
        let multi_arr = [1, 2, 3, 4, 5];
        let multi_deque = CircularDeque::from(multi_arr);
        assert_eq!(multi_deque.len(), 5);
        assert_eq!(multi_deque[0], 1);
        assert_eq!(multi_deque[4], 5);

        // Test with strings
        let str_arr = ["hello", "world", "rust"];
        let str_deque = CircularDeque::from(str_arr);
        assert_eq!(str_deque.len(), 3);
        assert_eq!(str_deque[0], "hello");
        assert_eq!(str_deque[2], "rust");

        // Test with owned strings
        let owned_arr = ["hello".to_string(), "world".to_string()];
        let owned_deque = CircularDeque::from(owned_arr);
        assert_eq!(owned_deque.len(), 2);
        assert_eq!(owned_deque[0], "hello");
        assert_eq!(owned_deque[1], "world");

        // Test with complex types
        let vec_arr = [vec![1, 2], vec![3, 4], vec![5, 6]];
        let vec_deque = CircularDeque::from(vec_arr);
        assert_eq!(vec_deque.len(), 3);
        assert_eq!(vec_deque[0], vec![1, 2]);
        assert_eq!(vec_deque[2], vec![5, 6]);

        // Test using Into syntax
        let into_arr = [10, 20, 30];
        let into_deque: CircularDeque<i32> = into_arr.into();
        assert_eq!(into_deque.len(), 3);
        assert_eq!(into_deque[0], 10);
        assert_eq!(into_deque[2], 30);

        // Test large array
        let large_arr: [i32; 100] = core::array::from_fn(|i| i as i32);
        let large_deque = CircularDeque::from(large_arr);
        assert_eq!(large_deque.len(), 100);
        assert_eq!(large_deque[0], 0);
        assert_eq!(large_deque[99], 99);

        // Test that order is preserved
        let order_arr = [5, 3, 8, 1, 9];
        let order_deque = CircularDeque::from(order_arr);
        for (i, &expected) in order_arr.iter().enumerate() {
            assert_eq!(order_deque[i], expected);
        }

        // Test capacity is appropriate
        let cap_arr = [1, 2, 3];
        let cap_deque = CircularDeque::from(cap_arr);
        assert!(cap_deque.capacity() >= cap_deque.len());
    }

    #[test]
    fn test_drop_trait() {
        use std::cell::RefCell;
        use std::rc::Rc;

        // Create a type that tracks when it's dropped
        #[derive(Debug)]
        struct DropTracker {
            id: u32,
            drop_count: Rc<RefCell<Vec<u32>>>,
        }

        impl DropTracker {
            fn new(id: u32, drop_count: Rc<RefCell<Vec<u32>>>) -> Self {
                DropTracker { id, drop_count }
            }
        }

        impl Drop for DropTracker {
            fn drop(&mut self) {
                self.drop_count.borrow_mut().push(self.id);
            }
        }

        let drop_count = Rc::new(RefCell::new(Vec::new()));

        // Test that elements are dropped when deque goes out of scope
        {
            let mut deque = CircularDeque::new();
            deque.push_back(DropTracker::new(1, drop_count.clone()));
            deque.push_back(DropTracker::new(2, drop_count.clone()));
            deque.push_back(DropTracker::new(3, drop_count.clone()));

            // Verify no drops yet
            assert_eq!(drop_count.borrow().len(), 0);

            // Test that clear() drops elements
            deque.clear();
            assert_eq!(drop_count.borrow().len(), 3);
            assert!(drop_count.borrow().contains(&1));
            assert!(drop_count.borrow().contains(&2));
            assert!(drop_count.borrow().contains(&3));
        }

        // Reset drop count
        drop_count.borrow_mut().clear();

        // Test that elements are dropped in correct order when deque is dropped
        {
            let mut deque = CircularDeque::new();
            deque.push_back(DropTracker::new(10, drop_count.clone()));
            deque.push_back(DropTracker::new(20, drop_count.clone()));
            deque.push_back(DropTracker::new(30, drop_count.clone()));

            // Add some rotation to test drop order with internal structure
            deque.push_front(DropTracker::new(5, drop_count.clone()));
            deque.pop_back(); // Remove 30

            assert_eq!(drop_count.borrow().len(), 1); // Only the popped element (30)
            assert!(drop_count.borrow().contains(&30));
        } // deque is dropped here

        // All remaining elements should be dropped
        assert_eq!(drop_count.borrow().len(), 4); // 30 (popped) + 5, 10, 20 (dropped)
        assert!(drop_count.borrow().contains(&5));
        assert!(drop_count.borrow().contains(&10));
        assert!(drop_count.borrow().contains(&20));
        assert!(drop_count.borrow().contains(&30));

        // Reset for next test
        drop_count.borrow_mut().clear();

        // Test empty deque drop (should not panic)
        {
            let _empty: CircularDeque<DropTracker> = CircularDeque::new();
        } // Should drop without issues

        assert_eq!(drop_count.borrow().len(), 0);

        // Test explicit drop
        drop_count.borrow_mut().clear();
        {
            let mut deque = CircularDeque::new();
            deque.push_back(DropTracker::new(100, drop_count.clone()));
            deque.push_back(DropTracker::new(200, drop_count.clone()));

            // Explicit drop
            drop(deque);

            assert_eq!(drop_count.borrow().len(), 2);
            assert!(drop_count.borrow().contains(&100));
            assert!(drop_count.borrow().contains(&200));
        }

        // Test that capacity changes don't affect drop behavior
        drop_count.borrow_mut().clear();
        {
            let mut deque = CircularDeque::with_capacity(2);
            deque.push_back(DropTracker::new(1, drop_count.clone()));
            deque.push_back(DropTracker::new(2, drop_count.clone()));
            deque.push_back(DropTracker::new(3, drop_count.clone())); // Should trigger reallocation
            deque.push_back(DropTracker::new(4, drop_count.clone()));

            assert_eq!(drop_count.borrow().len(), 0); // No drops during growth
        }

        // All elements should be dropped
        assert_eq!(drop_count.borrow().len(), 4);
        for id in 1..=4 {
            assert!(drop_count.borrow().contains(&id));
        }
    }
}
