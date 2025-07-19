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

use crate::queue::cdeque::CircularDeque;

/// An iterator over the elements of a [`CircularDeque`].
///
/// This struct is created by the [`iter`] method on [`CircularDeque`]. See its
/// documentation for more.
///
/// # Examples
///
/// ```
/// use deepmesa::collections::CircularDeque;
///
/// let mut deque = CircularDeque::new();
/// deque.push_back(1);
/// deque.push_back(2);
/// deque.push_back(3);
///
/// let mut iter = deque.iter();
/// assert_eq!(iter.next(), Some(&1));
/// assert_eq!(iter.next(), Some(&2));
/// assert_eq!(iter.next(), Some(&3));
/// assert_eq!(iter.next(), None);
/// ```
///
/// [`iter`]: CircularDeque::iter
pub struct Iter<'a, T> {
    deque: &'a CircularDeque<T>,
    index: usize,
    start: usize,
    end: usize,
}

/// A mutable iterator over the elements of a [`CircularDeque`].
///
/// This struct is created by the [`iter_mut`] method on [`CircularDeque`]. See its
/// documentation for more.
///
/// # Examples
///
/// ```
/// use deepmesa::collections::CircularDeque;
///
/// let mut deque = CircularDeque::new();
/// deque.push_back(1);
/// deque.push_back(2);
/// deque.push_back(3);
///
/// for item in deque.iter_mut() {
///     *item *= 2;
/// }
///
/// let values: Vec<i32> = deque.iter().copied().collect();
/// assert_eq!(values, vec![2, 4, 6]);
/// ```
///
/// [`iter_mut`]: CircularDeque::iter_mut
pub struct IterMut<'a, T> {
    deque: &'a mut CircularDeque<T>,
    index: usize,
    start: usize,
    end: usize,
}

impl<'a, T> Iter<'a, T> {
    /// Creates a new iterator over the elements of a [`CircularDeque`].
    ///
    /// This method is used internally by [`CircularDeque::iter`].
    pub(crate) fn new(deque: &'a CircularDeque<T>) -> Self {
        Iter {
            deque,
            index: 0,
            start: 0,
            end: deque.len(),
        }
    }

    /// Creates a new iterator over a range of elements in a [`CircularDeque`].
    ///
    /// This method is used internally by [`CircularDeque::range`].
    pub(crate) fn new_range(deque: &'a CircularDeque<T>, start: usize, end: usize) -> Self {
        Iter {
            deque,
            index: 0,
            start,
            end,
        }
    }
}

impl<'a, T> IterMut<'a, T> {
    /// Creates a new mutable iterator over the elements of a [`CircularDeque`].
    ///
    /// This method is used internally by [`CircularDeque::iter_mut`].
    pub(crate) fn new(deque: &'a mut CircularDeque<T>) -> Self {
        let len = deque.len();
        IterMut {
            deque,
            index: 0,
            start: 0,
            end: len,
        }
    }

    /// Creates a new mutable iterator over a range of elements in a [`CircularDeque`].
    ///
    /// This method is used internally by [`CircularDeque::range_mut`].
    pub(crate) fn new_range(deque: &'a mut CircularDeque<T>, start: usize, end: usize) -> Self {
        IterMut {
            deque,
            index: 0,
            start,
            end,
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    /// Returns the next element in the iteration.
    ///
    /// Returns `None` when the iteration is exhausted.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::collections::CircularDeque;
    ///
    /// let mut deque = CircularDeque::new();
    /// deque.push_back("hello");
    /// deque.push_back("world");
    ///
    /// let mut iter = deque.iter();
    /// assert_eq!(iter.next(), Some(&"hello"));
    /// assert_eq!(iter.next(), Some(&"world"));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        let current_index = self.start + self.index;
        if current_index >= self.end {
            return None;
        }

        let item = self.deque.get(current_index);
        self.index += 1;
        item
    }

    /// Returns bounds on the remaining length of the iterator.
    ///
    /// For this iterator, the bounds are exact, so the lower bound equals the upper bound.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::collections::CircularDeque;
    ///
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// let mut iter = deque.iter();
    /// assert_eq!(iter.size_hint(), (3, Some(3)));
    ///
    /// iter.next();
    /// assert_eq!(iter.size_hint(), (2, Some(2)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = (self.end - self.start).saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    /// Returns the exact number of elements remaining in the iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::collections::CircularDeque;
    ///
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// let mut iter = deque.iter();
    /// assert_eq!(iter.len(), 3);
    ///
    /// iter.next();
    /// assert_eq!(iter.len(), 2);
    /// ```
    fn len(&self) -> usize {
        (self.end - self.start).saturating_sub(self.index)
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    /// Returns the next mutable element in the iteration.
    ///
    /// Returns `None` when the iteration is exhausted.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::collections::CircularDeque;
    ///
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// let mut iter = deque.iter_mut();
    /// if let Some(first) = iter.next() {
    ///     *first = 10;
    /// }
    /// if let Some(second) = iter.next() {
    ///     *second = 20;
    /// }
    /// assert_eq!(iter.next(), None);
    ///
    /// assert_eq!(deque.get(0), Some(&10));
    /// assert_eq!(deque.get(1), Some(&20));
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        let current_index = self.start + self.index;
        if current_index >= self.end {
            return None;
        }

        let ptr = self.deque.ptr_at(current_index);
        self.index += 1;
        unsafe { Some(&mut *ptr) }
    }

    /// Returns bounds on the remaining length of the iterator.
    ///
    /// For this iterator, the bounds are exact, so the lower bound equals the upper bound.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::collections::CircularDeque;
    ///
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// let mut iter = deque.iter_mut();
    /// assert_eq!(iter.size_hint(), (3, Some(3)));
    ///
    /// iter.next();
    /// assert_eq!(iter.size_hint(), (2, Some(2)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = (self.end - self.start).saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    /// Returns the exact number of elements remaining in the iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa::collections::CircularDeque;
    ///
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    /// deque.push_back(3);
    ///
    /// let mut iter = deque.iter_mut();
    /// assert_eq!(iter.len(), 3);
    ///
    /// iter.next();
    /// assert_eq!(iter.len(), 2);
    /// ```
    fn len(&self) -> usize {
        (self.end - self.start).saturating_sub(self.index)
    }
}

/// A draining iterator for `CircularDeque<T>`.
///
/// This `struct` is created by [`CircularDeque::drain`].
/// See its documentation for more.
pub struct Drain<'a, T> {
    deque: &'a mut CircularDeque<T>,
    start: usize,
    end: usize,
    index: usize,
}

impl<'a, T> Drain<'a, T> {
    /// Creates a new drain iterator for the given range.
    ///
    /// This method is used internally by [`CircularDeque::drain`].
    pub(crate) fn new(deque: &'a mut CircularDeque<T>, start: usize, end: usize) -> Self {
        Drain {
            deque,
            start,
            end,
            index: 0,
        }
    }
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= (self.end - self.start) {
            return None;
        }

        let current_index = self.start + self.index;
        if current_index >= self.deque.len() {
            return None;
        }

        unsafe {
            let ptr = self.deque.ptr_at(current_index);
            self.index += 1;
            Some(std::ptr::read(ptr))
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = (self.end - self.start).saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<'a, T> ExactSizeIterator for Drain<'a, T> {
    fn len(&self) -> usize {
        (self.end - self.start).saturating_sub(self.index)
    }
}

impl<'a, T> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        // Drain any remaining elements
        while self.next().is_some() {}

        // Remove the drained range from the deque
        let range_len = self.end - self.start;
        if range_len > 0 && self.start < self.deque.len() {
            // Remove elements from start to end by calling remove repeatedly
            for _ in 0..range_len.min(self.deque.len() - self.start) {
                self.deque.remove(self.start);
            }
        }
    }
}

/// An owning iterator for `CircularDeque<T>`.
///
/// This `struct` is created by the `into_iter` method on `CircularDeque`
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
pub struct IntoIter<T> {
    deque: CircularDeque<T>,
    index: usize,
}

impl<T> IntoIter<T> {
    /// Creates a new owning iterator for the given deque.
    ///
    /// This method is used internally by the `IntoIterator` implementation.
    pub(crate) fn new(deque: CircularDeque<T>) -> Self {
        IntoIter { deque, index: 0 }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.deque.len() {
            return None;
        }

        // Remove the element at the front (index 0) each time
        // This maintains the order while consuming the deque
        let item = self.deque.pop_front();
        // Note: We don't increment index because we're removing from the front
        item
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.deque.len();
        (remaining, Some(remaining))
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.deque.len()
    }
}
