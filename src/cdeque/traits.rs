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

//! Trait implementations for `CircularDeque`.
//!
//! This module provides implementations of standard library traits for `CircularDeque<T>`,
//! including indexing, comparison, and formatting traits.
//!
//! ## Implemented Traits
//!
//! - [`Index<usize>`] - Allows indexing with the `[]` operator (read-only)
//! - [`IndexMut<usize>`] - Allows mutable indexing with the `[]` operator
//! - [`PartialEq`] - Enables equality comparison between deques
//! - [`Eq`] - Enables total equality (when `T: Eq`)
//! - [`Debug`] - Provides debug formatting for deques
//!
//! ## Examples
//!
//! ```
//! # use deepmesa_collections::CircularDeque;
//! let mut deque = CircularDeque::new();
//! deque.push_back(1);
//! deque.push_back(2);
//! deque.push_back(3);
//!
//! // Indexing
//! assert_eq!(deque[0], 1);
//! assert_eq!(deque[1], 2);
//!
//! // Mutable indexing
//! deque[0] = 10;
//! assert_eq!(deque[0], 10);
//!
//! // Comparison
//! let mut other = CircularDeque::new();
//! other.push_back(10);
//! other.push_back(2);
//! other.push_back(3);
//! assert_eq!(deque, other);
//!
//! // Debug formatting
//! println!("{:?}", deque); // Prints something like "[3,4]:10,2,3"
//! ```

use crate::cdeque::cdeque::{CircularDeque, IntoIter, Iter, IterMut};
use crate::cdeque::macros::*;
use std::cmp::{Ord, Ordering, PartialEq, PartialOrd};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::io::{BufRead, Read, Result as IoResult, Write};
use std::iter::{Extend, FromIterator};
use std::ops::Index;
use std::ops::IndexMut;

extern crate alloc;

impl<T> Index<usize> for CircularDeque<T> {
    type Output = T;

    /// Returns a reference to the element at the given index.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
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
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[1], 2);
    /// assert_eq!(deque[2], 3);
    /// ```
    #[inline]
    fn index(&self, index: usize) -> &T {
        bounds_check_panic!(self, index);
        let ptr = self.ptr_at(index);
        unsafe {
            return &(*ptr);
        }
    }
}

impl<T> IndexMut<usize> for CircularDeque<T> {
    /// Returns a mutable reference to the element at the given index.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
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
    /// deque[0] = 10;
    /// deque[1] = 20;
    ///
    /// assert_eq!(deque[0], 10);
    /// assert_eq!(deque[1], 20);
    /// assert_eq!(deque[2], 3);
    /// ```
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        return self.get_mut(index).unwrap();
    }
}

/// Implements `Eq` for `CircularDeque<T>` where `T` implements `Eq` and `Debug`.
///
/// This trait is automatically implemented when the element type supports equality comparison.
/// Two deques are equal if they have the same length and all corresponding elements are equal.
impl<T> Eq for CircularDeque<T> where T: Eq + Debug {}

impl<T> PartialEq<CircularDeque<T>> for CircularDeque<T>
where
    T: PartialEq,
{
    /// Compares two `CircularDeque`s for equality.
    ///
    /// Two deques are considered equal if they have the same length and all corresponding
    /// elements are equal according to the `PartialEq` implementation of `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque1 = CircularDeque::new();
    /// deque1.push_back(1);
    /// deque1.push_back(2);
    /// deque1.push_back(3);
    ///
    /// let mut deque2 = CircularDeque::new();
    /// deque2.push_back(1);
    /// deque2.push_back(2);
    /// deque2.push_back(3);
    ///
    /// assert_eq!(deque1, deque2);
    ///
    /// deque2.push_back(4);
    /// assert_ne!(deque1, deque2);
    /// ```
    ///
    /// Deques with different lengths are not equal:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque1 = CircularDeque::new();
    /// deque1.push_back(1);
    /// deque1.push_back(2);
    ///
    /// let mut deque2 = CircularDeque::new();
    /// deque2.push_back(1);
    ///
    /// assert_ne!(deque1, deque2);
    /// ```
    fn eq(&self, other: &CircularDeque<T>) -> bool {
        if self.len != other.len {
            return false;
        }

        let mut idx: usize = 0;
        loop {
            if idx >= self.len() {
                break;
            }

            unsafe {
                let val = &*self.ptr_at(idx);
                let val_rhs = &*other.ptr_at(idx);

                if val.ne(&val_rhs) {
                    return false;
                }
                idx += 1;
            }
        }

        return true;
    }
}

impl<T: Debug> Debug for CircularDeque<T> {
    /// Formats the `CircularDeque` for debugging output.
    ///
    /// The format shows the length and capacity followed by the elements in order.
    /// The format is `[length,capacity]:element1,element2,...` or `[length,capacity]:()` for empty deques.
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
    /// println!("{:?}", deque); // Prints something like "[3,4]:1,2,3"
    /// ```
    ///
    /// Empty deques are formatted as:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let deque: CircularDeque<i32> = CircularDeque::new();
    /// println!("{:?}", deque); // Prints "[0,0]:()"
    /// ```
    ///
    /// The first number in brackets is the length, and the second is the capacity.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{},{}]:", self.len(), self.capacity())?;
        let mut idx: usize = 0;
        if self.len == 0 {
            write!(f, "()")?;
            return Ok(());
        }

        loop {
            unsafe {
                let val = &*self.ptr_at(idx);
                if idx < self.len - 1 {
                    write!(f, "{:?},", val)?;
                } else if idx == self.len - 1 {
                    write!(f, "{:?}", val)?;
                    break;
                } else {
                    break;
                }

                idx += 1;
            }
        }
        return Ok(());
    }
}

impl<T> Clone for CircularDeque<T>
where
    T: Clone,
{
    /// Creates a deep copy of the `CircularDeque`.
    ///
    /// All elements in the deque are cloned using their `Clone` implementation.
    /// The new deque will have the same capacity as the original.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut original = CircularDeque::new();
    /// original.push_back(1);
    /// original.push_back(2);
    /// original.push_back(3);
    ///
    /// let cloned = original.clone();
    /// assert_eq!(original, cloned);
    /// assert_eq!(cloned.len(), 3);
    /// assert_eq!(cloned[0], 1);
    /// assert_eq!(cloned[1], 2);
    /// assert_eq!(cloned[2], 3);
    /// ```
    ///
    /// Cloning creates an independent copy:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut original = CircularDeque::new();
    /// original.push_back("hello".to_string());
    /// original.push_back("world".to_string());
    ///
    /// let mut cloned = original.clone();
    /// cloned.push_back("!".to_string());
    ///
    /// assert_eq!(original.len(), 2);
    /// assert_eq!(cloned.len(), 3);
    /// ```
    fn clone(&self) -> Self {
        let mut new_deque = if self.capacity() == 0 {
            CircularDeque::new()
        } else {
            CircularDeque::with_capacity(self.capacity())
        };

        for i in 0..self.len() {
            unsafe {
                let element = &*self.ptr_at(i);
                new_deque.push_back(element.clone());
            }
        }

        new_deque
    }
}

impl<T> Default for CircularDeque<T> {
    /// Creates an empty `CircularDeque<T>` with default configuration.
    ///
    /// This is equivalent to calling `CircularDeque::new()`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let deque: CircularDeque<i32> = Default::default();
    /// assert_eq!(deque.len(), 0);
    /// assert_eq!(deque.capacity(), 0);
    /// assert!(deque.is_empty());
    /// ```
    ///
    /// Using in generic contexts:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// fn create_default_collection<T: Default>() -> T {
    ///     T::default()
    /// }
    ///
    /// let deque: CircularDeque<String> = create_default_collection();
    /// assert!(deque.is_empty());
    /// ```
    fn default() -> Self {
        CircularDeque::new()
    }
}

impl<T> IntoIterator for CircularDeque<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Creates a consuming iterator over the deque.
    ///
    /// The deque is consumed and cannot be used after calling this method.
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
    /// let collected: Vec<i32> = deque.into_iter().collect();
    /// assert_eq!(collected, vec![1, 2, 3]);
    /// ```
    ///
    /// Using in a for loop:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back("hello");
    /// deque.push_back("world");
    ///
    /// for item in deque {
    ///     println!("{}", item);
    /// }
    /// // deque is no longer accessible here
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

impl<'a, T> IntoIterator for &'a CircularDeque<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    /// Creates an iterator over references to the deque's elements.
    ///
    /// The deque is borrowed and can still be used after iteration.
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
    /// let collected: Vec<&i32> = (&deque).into_iter().collect();
    /// assert_eq!(collected, vec![&1, &2, &3]);
    ///
    /// // deque is still accessible
    /// assert_eq!(deque.len(), 3);
    /// ```
    ///
    /// Using in a for loop:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// for item in &deque {
    ///     println!("{}", item);
    /// }
    /// // deque is still accessible here
    /// assert_eq!(deque.len(), 2);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut CircularDeque<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    /// Creates an iterator over mutable references to the deque's elements.
    ///
    /// The deque is mutably borrowed and can still be used after iteration.
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
    /// for item in &mut deque {
    ///     *item *= 2;
    /// }
    ///
    /// assert_eq!(deque[0], 2);
    /// assert_eq!(deque[1], 4);
    /// assert_eq!(deque[2], 6);
    /// ```
    ///
    /// Collecting mutable references:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// let mut refs: Vec<&mut i32> = (&mut deque).into_iter().collect();
    /// *refs[0] = 10;
    /// *refs[1] = 20;
    ///
    /// assert_eq!(deque[0], 10);
    /// assert_eq!(deque[1], 20);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T> FromIterator<T> for CircularDeque<T> {
    /// Creates a `CircularDeque` from an iterator.
    ///
    /// This allows using the `collect()` method to create a deque from any iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let vec = vec![1, 2, 3, 4, 5];
    /// let deque: CircularDeque<i32> = vec.into_iter().collect();
    ///
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[4], 5);
    /// ```
    ///
    /// Using with iterator adaptors:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let deque: CircularDeque<i32> = (0..10)
    ///     .filter(|&x| x % 2 == 0)
    ///     .map(|x| x * x)
    ///     .collect();
    ///
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque[0], 0);   // 0^2
    /// assert_eq!(deque[1], 4);   // 2^2
    /// assert_eq!(deque[2], 16);  // 4^2
    /// assert_eq!(deque[3], 36);  // 6^2
    /// assert_eq!(deque[4], 64);  // 8^2
    /// ```
    ///
    /// Creating from string characters:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let deque: CircularDeque<char> = "hello".chars().collect();
    ///
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque[0], 'h');
    /// assert_eq!(deque[4], 'o');
    /// ```
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let (lower_bound, _) = iter.size_hint();

        let mut deque = if lower_bound == 0 {
            CircularDeque::new()
        } else {
            CircularDeque::with_capacity(lower_bound)
        };

        for item in iter {
            deque.push_back(item);
        }

        deque
    }
}

impl<T> Extend<T> for CircularDeque<T> {
    /// Extends the deque with the contents of an iterator.
    ///
    /// All elements from the iterator are added to the back of the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// deque.extend(vec![3, 4, 5]);
    ///
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[4], 5);
    /// ```
    ///
    /// Extending with an iterator adaptor:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    ///
    /// deque.extend((2..=5).map(|x| x * 10));
    ///
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[1], 20);
    /// assert_eq!(deque[4], 50);
    /// ```
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.push_back(item);
        }
    }
}

impl<'a, T> Extend<&'a T> for CircularDeque<T>
where
    T: Clone,
{
    /// Extends the deque with clones of the contents of an iterator.
    ///
    /// All elements from the iterator are cloned and added to the back of the deque.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(1);
    /// deque.push_back(2);
    ///
    /// let source = vec![3, 4, 5];
    /// deque.extend(&source);
    ///
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[4], 5);
    ///
    /// // source is still available
    /// assert_eq!(source.len(), 3);
    /// ```
    ///
    /// Extending with references to string slices:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back("hello".to_string());
    ///
    /// let words = ["world", "rust", "deque"];
    /// deque.extend(words.iter().map(|&s| s.to_string()));
    ///
    /// assert_eq!(deque.len(), 4);
    /// assert_eq!(deque[0], "hello");
    /// assert_eq!(deque[1], "world");
    /// ```
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        for item in iter {
            self.push_back(item.clone());
        }
    }
}

impl<T> From<Vec<T>> for CircularDeque<T> {
    /// Creates a `CircularDeque` from a `Vec`.
    ///
    /// This conversion moves all elements from the Vec into the deque.
    /// The order of elements is preserved.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let vec = vec![1, 2, 3, 4, 5];
    /// let deque = CircularDeque::from(vec);
    ///
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[4], 5);
    /// ```
    ///
    /// Using with complex types:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let vec = vec!["hello".to_string(), "world".to_string()];
    /// let deque = CircularDeque::from(vec);
    ///
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque[0], "hello");
    /// assert_eq!(deque[1], "world");
    /// ```
    ///
    /// Automatic conversion with Into:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let vec = vec![1, 2, 3];
    /// let deque: CircularDeque<i32> = vec.into();
    ///
    /// assert_eq!(deque.len(), 3);
    /// ```
    fn from(vec: Vec<T>) -> Self {
        let mut deque = if vec.len() == 0 {
            CircularDeque::new()
        } else {
            CircularDeque::with_capacity(vec.len())
        };
        deque.extend(vec);
        deque
    }
}

impl<T> Hash for CircularDeque<T>
where
    T: Hash,
{
    /// Computes a hash for the `CircularDeque`.
    ///
    /// The hash is computed based on the elements in the deque in order.
    /// Two deques with the same elements in the same order will have the same hash.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// use std::collections::HashMap;
    ///
    /// let mut deque1 = CircularDeque::new();
    /// deque1.push_back(1);
    /// deque1.push_back(2);
    /// deque1.push_back(3);
    ///
    /// let mut deque2 = CircularDeque::new();
    /// deque2.push_back(1);
    /// deque2.push_back(2);
    /// deque2.push_back(3);
    ///
    /// // Same elements should have same hash
    /// let mut map = HashMap::new();
    /// map.insert(deque1, "first");
    /// map.insert(deque2, "second"); // This will replace "first" because deques are equal
    ///
    /// assert_eq!(map.len(), 1);
    /// ```
    ///
    /// Using as HashMap keys:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// use std::collections::HashMap;
    ///
    /// let mut map: HashMap<CircularDeque<i32>, String> = HashMap::new();
    ///
    /// let mut key1 = CircularDeque::new();
    /// key1.push_back(1);
    /// key1.push_back(2);
    ///
    /// let mut key2 = CircularDeque::new();
    /// key2.push_back(3);
    /// key2.push_back(4);
    ///
    /// map.insert(key1, "value1".to_string());
    /// map.insert(key2, "value2".to_string());
    ///
    /// assert_eq!(map.len(), 2);
    /// ```
    ///
    /// Order matters for hashing:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// use std::collections::hash_map::DefaultHasher;
    /// use std::hash::{Hash, Hasher};
    ///
    /// let mut deque1 = CircularDeque::new();
    /// deque1.push_back(1);
    /// deque1.push_back(2);
    ///
    /// let mut deque2 = CircularDeque::new();
    /// deque2.push_back(2);
    /// deque2.push_back(1);
    ///
    /// let mut hasher1 = DefaultHasher::new();
    /// let mut hasher2 = DefaultHasher::new();
    ///
    /// deque1.hash(&mut hasher1);
    /// deque2.hash(&mut hasher2);
    ///
    /// // Different order should produce different hashes
    /// assert_ne!(hasher1.finish(), hasher2.finish());
    /// ```
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash the length first to distinguish between deques with different lengths
        self.len().hash(state);

        // Hash each element in order
        for i in 0..self.len() {
            unsafe {
                let element = &*self.ptr_at(i);
                element.hash(state);
            }
        }
    }
}

impl<T> PartialOrd for CircularDeque<T>
where
    T: PartialOrd,
{
    /// Compares two `CircularDeque`s lexicographically.
    ///
    /// The comparison is performed element by element from front to back.
    /// If all compared elements are equal, the shorter deque is considered less than the longer one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque1 = CircularDeque::new();
    /// deque1.push_back(1);
    /// deque1.push_back(2);
    /// deque1.push_back(3);
    ///
    /// let mut deque2 = CircularDeque::new();
    /// deque2.push_back(1);
    /// deque2.push_back(2);
    /// deque2.push_back(4);
    ///
    /// assert!(deque1 < deque2);
    /// ```
    ///
    /// Length-based comparison when elements are equal:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut short = CircularDeque::new();
    /// short.push_back(1);
    /// short.push_back(2);
    ///
    /// let mut long = CircularDeque::new();
    /// long.push_back(1);
    /// long.push_back(2);
    /// long.push_back(3);
    ///
    /// assert!(short < long);
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let min_len = self.len().min(other.len());

        // Compare elements lexicographically
        for i in 0..min_len {
            unsafe {
                let self_elem = &*self.ptr_at(i);
                let other_elem = &*other.ptr_at(i);

                match self_elem.partial_cmp(other_elem) {
                    Some(Ordering::Equal) => continue,
                    other => return other,
                }
            }
        }

        // If all compared elements are equal, compare lengths
        Some(self.len().cmp(&other.len()))
    }
}

impl<T> Ord for CircularDeque<T>
where
    T: Ord + Debug,
{
    /// Total ordering for `CircularDeque`s.
    ///
    /// This implementation provides a total ordering based on lexicographic comparison
    /// of elements followed by length comparison if all elements are equal.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// use std::cmp::Ordering;
    ///
    /// let mut deque1 = CircularDeque::new();
    /// deque1.push_back(1);
    /// deque1.push_back(2);
    ///
    /// let mut deque2 = CircularDeque::new();
    /// deque2.push_back(1);
    /// deque2.push_back(3);
    ///
    /// assert_eq!(deque1.cmp(&deque2), Ordering::Less);
    /// ```
    ///
    /// Sorting deques:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deques = vec![];
    ///
    /// let mut deque1 = CircularDeque::new();
    /// deque1.push_back(3);
    /// deques.push(deque1);
    ///
    /// let mut deque2 = CircularDeque::new();
    /// deque2.push_back(1);
    /// deques.push(deque2);
    ///
    /// let mut deque3 = CircularDeque::new();
    /// deque3.push_back(2);
    /// deques.push(deque3);
    ///
    /// deques.sort();
    ///
    /// assert_eq!(deques[0][0], 1);
    /// assert_eq!(deques[1][0], 2);
    /// assert_eq!(deques[2][0], 3);
    /// ```
    fn cmp(&self, other: &Self) -> Ordering {
        let min_len = self.len().min(other.len());

        // Compare elements lexicographically
        for i in 0..min_len {
            unsafe {
                let self_elem = &*self.ptr_at(i);
                let other_elem = &*other.ptr_at(i);

                match self_elem.cmp(other_elem) {
                    Ordering::Equal => continue,
                    other => return other,
                }
            }
        }

        // If all compared elements are equal, compare lengths
        self.len().cmp(&other.len())
    }
}

impl<T> Drop for CircularDeque<T> {
    /// Drops the `CircularDeque`, cleaning up resources.
    ///
    /// This implementation:
    /// 1. Drops all contained elements in order from front to back
    /// 2. Deallocates the underlying memory buffer
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// {
    ///     let mut deque = CircularDeque::new();
    ///     deque.push_back(String::from("hello"));
    ///     deque.push_back(String::from("world"));
    ///     // Drop is called automatically when deque goes out of scope
    /// } // Memory and String objects are cleaned up here
    /// ```
    ///
    /// Drop is also called when explicitly using `drop()`:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let mut deque = CircularDeque::new();
    /// deque.push_back(42);
    /// drop(deque); // Explicit drop
    /// // deque is no longer accessible
    /// ```
    fn drop(&mut self) {
        // First, drop all elements in the deque
        self.clear();

        // Then deallocate the memory if we have any allocated
        if self.capacity > 0 {
            unsafe {
                use alloc::alloc::{dealloc, Layout};
                let layout = Layout::array::<T>(self.capacity).unwrap();
                dealloc(self.p_idxz as *mut u8, layout);
            }
        }
    }
}

impl<T, const N: usize> From<[T; N]> for CircularDeque<T> {
    /// Creates a `CircularDeque` from an array.
    ///
    /// This conversion moves all elements from the array into the deque.
    /// The order of elements is preserved.
    ///
    /// # Examples
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let arr = [1, 2, 3, 4, 5];
    /// let deque = CircularDeque::from(arr);
    ///
    /// assert_eq!(deque.len(), 5);
    /// assert_eq!(deque[0], 1);
    /// assert_eq!(deque[4], 5);
    /// ```
    ///
    /// Using with complex types:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let arr = ["hello".to_string(), "world".to_string()];
    /// let deque = CircularDeque::from(arr);
    ///
    /// assert_eq!(deque.len(), 2);
    /// assert_eq!(deque[0], "hello");
    /// assert_eq!(deque[1], "world");
    /// ```
    ///
    /// Empty arrays:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let arr: [i32; 0] = [];
    /// let deque = CircularDeque::from(arr);
    ///
    /// assert_eq!(deque.len(), 0);
    /// assert!(deque.is_empty());
    /// ```
    ///
    /// Automatic conversion with Into:
    ///
    /// ```
    /// # use deepmesa_collections::CircularDeque;
    /// let arr = [1, 2, 3];
    /// let deque: CircularDeque<i32> = arr.into();
    ///
    /// assert_eq!(deque.len(), 3);
    /// ```
    fn from(arr: [T; N]) -> Self {
        if N == 0 {
            CircularDeque::new()
        } else {
            let mut deque = CircularDeque::with_capacity(N);
            for item in arr {
                deque.push_back(item);
            }
            deque
        }
    }
}
