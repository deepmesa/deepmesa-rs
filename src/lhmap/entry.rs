/*
   LinkedHashMap: A fast and flexible linked HashMap that allows for
   O(1) inserts and removes with a predictable iteration order.

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

use core::hash::Hash;
use core::hash::Hasher;

pub(crate) struct PtrKey<T: Hash + Eq>(*const T);

impl<T: Hash + Eq> PtrKey<T> {
    pub(crate) fn new(t: &T) -> PtrKey<T> {
        return PtrKey(t as *const T);
    }

    pub(crate) fn from_ptr(ptr: *const T) -> PtrKey<T> {
        return PtrKey(ptr);
    }
}

impl<T> Hash for PtrKey<T>
where
    T: Hash + Eq,
{
    fn hash<H>(&self, h: &mut H)
    where
        H: Hasher,
    {
        unsafe {
            (*self.0).hash(h);
        }
    }
}

impl<T> PartialEq for PtrKey<T>
where
    T: Hash + Eq,
{
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            return (*(self.0)).eq(&(*other.0));
        }
    }
}

impl<T> Eq for PtrKey<T> where T: Hash + Eq {}

/// A view into a single entry in a map. The entry is used in the
/// evict_eldest function if one if provided. See
/// [`eviction`](crate::map::lhmap::LinkedHashMap#evicting-elements) in the
/// module level documentation.
#[derive(Debug)]
pub struct Entry<K, V> {
    pub(crate) key: K,
    pub(crate) val: V,
}

impl<K, V> Entry<K, V> {
    pub(crate) fn new(k: K, v: V) -> Entry<K, V> {
        return Entry { key: k, val: v };
    }

    pub(crate) unsafe fn key_ptr(&self) -> *const K {
        return &self.key as *const K;
    }
}

/// An enum used to specify the iteration order for the LinkedHashMap.
///
/// [`InsertionOrder`](#variant.InsertionOrder) is the order in which the
/// keys were inserted into the map from least recently inserted
/// (oldest) to most recently inserted (newest).
///
/// [`AccessOrder`](#variant.AccessOrder) is the order in which the
/// keys in the map were last accessed from least-recently accessed
/// (oldest) to most recently accessed (newest).
#[derive(Debug, PartialEq, Eq)]
pub enum Order {
    /// LinkedHashMap iteration order from least-recently accessed to
    /// most-recently accessed.
    AccessOrder,

    /// LinkedHashMap iteration order from least-recently inserted to
    /// most-recently inserted.
    InsertionOrder,
}
