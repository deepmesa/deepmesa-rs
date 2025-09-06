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

use crate::linkedlist::node::NodeHandle;
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

impl<K, V> PartialEq for Entry<K, V>
where
    K: PartialEq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key && self.val == other.val
    }
}

impl<K, V> Eq for Entry<K, V>
where
    K: Eq,
    V: Eq,
{}

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

/// A handle to an entry in a [`LinkedHashMap`](crate::LinkedHashMap).
///
/// This handle wraps a [`NodeHandle`] from the underlying linked list and
/// provides methods to manipulate the position of entries within the map's
/// iteration order. Handles can be copied and passed around by value
/// regardless of the lifetime of the map.
///
/// Once an entry is removed from the map, its handle becomes invalid.
/// Using an invalid handle is safe - methods will return `false` or `None`
/// to indicate the handle is no longer valid.
///
/// # Examples
/// ```
/// use deepmesa_collections::LinkedHashMap;
/// use deepmesa_collections::lhmap::Order;
///
/// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
/// lhm.put(1, "a");
/// lhm.put(2, "b");
///
/// if let Some(handle) = lhm.entry_handle(&1) {
///     // Move entry with key 1 to the end of iteration order
///     handle.move_to_end(&mut lhm);
/// }
/// ```
#[derive(Debug, Clone)]
pub struct EntryHandle<K, V> {
    pub(crate) node_handle: NodeHandle<Entry<K, V>>,
}

unsafe impl<K, V> Send for EntryHandle<K, V> where K: Hash + Eq {}
unsafe impl<K, V> Sync for EntryHandle<K, V> where K: Hash + Eq {}

impl<K, V> PartialEq for EntryHandle<K, V>
where
    K: PartialEq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.node_handle == other.node_handle
    }
}

impl<K, V> Eq for EntryHandle<K, V>
where
    K: Eq,
    V: Eq,
{}

impl<K, V> Default for EntryHandle<K, V> {
    /// Creates a default (invalid) entry handle.
    fn default() -> Self {
        Self {
            node_handle: NodeHandle::default(),
        }
    }
}

impl<K, V> EntryHandle<K, V>
where
    K: Hash + Eq,
{
    /// Creates a new EntryHandle wrapping the given NodeHandle.
    pub(crate) fn new(node_handle: NodeHandle<Entry<K, V>>) -> Self {
        Self { node_handle }
    }

    /// Moves the entry associated with this handle to the end of the 
    /// LinkedHashMap's iteration order.
    ///
    /// If the entry is already at the end of the iteration order, this 
    /// operation has no effect. This method works regardless of whether the
    /// map uses InsertionOrder or AccessOrder.
    ///
    /// Returns `true` if the entry was successfully moved to the end (or was
    /// already at the end), and `false` if this handle is invalid.
    ///
    /// This operation completes in O(1) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    /// lhm.put(3, "c");
    ///
    /// if let Some(handle) = lhm.entry_handle(&1) {
    ///     assert!(handle.move_to_end(&mut lhm));
    ///     
    ///     // Now key 1 will be the last in iteration order
    ///     let keys: Vec<_> = lhm.keys().copied().collect();
    ///     assert_eq!(keys, vec![2, 3, 1]);
    /// }
    /// ```
    pub fn move_to_end(&self, map: &mut crate::LinkedHashMap<K, V>) -> bool {
        map.ll.make_head(&self.node_handle)
    }
}
