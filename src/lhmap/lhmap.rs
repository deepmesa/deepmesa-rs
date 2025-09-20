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

use crate::lhmap::entry::Entry;
use crate::lhmap::entry::EntryHandle;
use crate::lhmap::entry::Order;
use crate::lhmap::entry::PtrKey;
use crate::lhmap::iter::Iter;
use crate::lhmap::iter::IterMut;
use crate::lhmap::iter::Keys;
use crate::lhmap::iter::Values;
use crate::lhmap::iter::ValuesMut;
use crate::linkedlist::list::LinkedList;
use crate::linkedlist::node::NodeHandle;
use core::hash::Hash;
use std::collections::HashMap;

/// A fast and flexible LinkedHashMap that combines a [`std::collections::HashMap`] and a
/// [`LinkedList`](LinkedList) for *O*(*1*) inserts, lookups and deletes along with a
/// predictable iteration order.
///
/// All the basic functions - [`get()`](#method.get),
/// [`get_mut()`](#method.get_mut),
/// [`get_key_value()`](#method.get_key_value),
/// [`put()`](#method.put), [`insert()`](#method.insert),
/// [`remove()`](#method.remove),
/// [`remove_entry()`](#method.remove_entry) - provide constant time
/// performance which is expected to be lower than that of the Hashmap
/// given the added expense of of maintaining and updating the
/// underlying linked list.
///
/// # Getting Started
/// ```
/// use deepmesa_collections::LinkedHashMap;
/// use deepmesa_collections::lhmap::Order;
///
/// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
/// lhm.put(1, "a");
/// lhm.put(2, "b");
///
/// assert_eq!(lhm.get(&1), Some(&"a"));
/// assert_eq!(lhm.get(&2), Some(&"b"));
///
/// if let Some(val) = lhm.get_mut(&1) {
///     *val = "d";
/// }
///
/// assert_eq!(lhm.get(&1), Some(&"d"));
///
/// ```
///
/// # Iteration Order
///
/// This map holds a LinkedList of all the elements that defines the
/// iteration order. The order is either [`InsertionOrder`](Order) or
/// [`AccessOrder`](Order). InsertionOrder is the order in which the
/// keys were inserted into the map from least recently inserted
/// (oldest) to most recently inserted (newest). ReInserting a key
/// (via the insert or put methods) will change the insertion order to
/// make the re-inserted key the most recently inserted (newest) in
/// the order.
///
/// AccessOrder is the order in which the keys in the map were last
/// accessed (via the [`get()`](#method.get),
/// [`get_key_value()`](#method.get_key_value),
/// [`get_mut()`](#method.get_mut) methods) from least-recently
/// accessed (oldest) to most recently accessed (newest). Iterating
/// over the map using one of the iterators -
/// [`iter()`](#method.iter), [`iter_mut()`](#method.iter_mut),
/// [`keys()`](#method.keys), [`values()`](#method.values),
/// [`values_mut()`](#method.values_mut) - does not affect the order.
///
/// Iteration over the map requires time proportional to the length of
/// the map (*O*(*len*)) regardless of the capacity because it
/// iterates over the elements of the underlying linked list. The
/// iteration order of the map is always from oldest entry (accessed
/// or inserted) to the newest entry (accessed or inserted).
///
/// The map offers iterators over the [`elements`](#method.iter),
/// [`keys`](#method.keys) and [`values`](#method.values) with mutable
/// iterators for [`elements`](#method.iter_mut) and
/// [`values`](#method.values_mut). The iterators can also be
/// reversed.
///
/// ```
/// // Construct a map in InsertionOrder
/// use deepmesa_collections::LinkedHashMap;
/// use deepmesa_collections::lhmap::Order;
///
/// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
/// lhm.put(1, "a");
/// lhm.put(2, "b");
///
/// lhm.get(&1);
///
/// let mut iter = lhm.iter();
/// assert_eq!(iter.next(), Some((&1, &"a")));
/// assert_eq!(iter.next(), Some((&2, &"b")));
/// assert_eq!(iter.next(), None);
/// iter = iter.reverse();
/// assert_eq!(iter.next(), Some((&2, &"b")));
/// assert_eq!(iter.next(), Some((&1, &"a")));
/// assert_eq!(iter.next(), None);
///
///
/// // Construct a map in AccessOrder
/// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
/// lhm.put(1, "a");
/// lhm.put(2, "b");
///
/// lhm.get(&1);
///
/// let mut iter = lhm.iter();
/// assert_eq!(iter.next(), Some((&2, &"b")));
/// assert_eq!(iter.next(), Some((&1, &"a")));
/// assert_eq!(iter.next(), None);
/// iter = iter.reverse();
/// assert_eq!(iter.next(), Some((&1, &"a")));
/// assert_eq!(iter.next(), Some((&2, &"b")));
/// assert_eq!(iter.next(), None);
///
/// ```
///
/// # Evicting Elements
///
/// The Map also supports construction with an
/// [`evict_eldest`](#method.new) function that can be provided to
/// implement a policy for removing entries when new elements are
/// added to the map. A LinkedHashMap with [`AccessOrder`](Order) and
/// an eviction function is well suited to building an LRU Cache.
///
/// ```
/// use deepmesa_collections::lhmap::Entry;
/// pub fn evict<K,V>(len: usize, capacity: usize, e: &Entry<K, V>) -> bool {
///     if len > capacity {
///         return true;
///     }
///     return false;
/// }
///
/// use deepmesa_collections::LinkedHashMap;
/// use deepmesa_collections::lhmap::Order;
///
/// let mut lhm = LinkedHashMap::<u16, &str>::new(3, Order::AccessOrder, Some(evict));
/// lhm.put(1, "a");
/// lhm.put(2, "b");
/// lhm.put(3, "c");
///
/// assert_eq!(lhm.get(&2), Some(&"b"));
/// lhm.put(4, "d");
/// assert_eq!(lhm.get(&1), None);
///
/// ```
/// 
/// # Head/Tail Semantics
/// 
/// This LinkedHashMap uses the following head/tail semantics:
/// - **Head**: Contains the oldest elements (least recently inserted/accessed)
/// - **Tail**: Contains the newest elements (most recently inserted/accessed)
/// - **Iteration**: Always proceeds from head to tail (oldest to newest)
/// - **Eviction**: Removes elements from the head (oldest elements first)
/// 
/// New elements are added to the tail, and in AccessOrder mode, accessed 
/// elements are moved to the tail (marking them as most recently used).
pub struct LinkedHashMap<K, V>
where
    K: Hash + Eq,
{
    pub(crate) evict_eldest: Option<fn(len: usize, capacity: usize, e: &Entry<K, V>) -> bool>,
    pub(crate) order: Order,
    pub(crate) cap: usize,
    pub(crate) ll: LinkedList<Entry<K, V>>,
    pub(crate) map: HashMap<PtrKey<K>, NodeHandle<Entry<K, V>>>,
}

unsafe impl<K, V> Send for LinkedHashMap<K, V> where K: Hash + Eq {}
unsafe impl<K, V> Sync for LinkedHashMap<K, V> where K: Hash + Eq {}

impl<'a, K, V> IntoIterator for &'a LinkedHashMap<K, V>
where
    K: Hash + Eq,
{
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut LinkedHashMap<K, V>
where
    K: Hash + Eq,
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<K, V> LinkedHashMap<K, V>
where
    K: Hash + Eq,
{
    /// Creates an empty LinkedHashMap with the specified capacity and
    /// iteration order. The evict_eldest function can be supplied
    /// that is called everytime a new entry is inserted into the map
    /// with the current length, capacity and the first entry in the
    /// linkedlist (least recently inserted or accessed).
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    /// let lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// ```
    pub fn new(
        capacity: usize,
        order: Order,
        evict_eldest: Option<fn(len: usize, capacity: usize, e: &Entry<K, V>) -> bool>,
    ) -> LinkedHashMap<K, V> {
        return LinkedHashMap {
            evict_eldest,
            order,
            cap: capacity,
            map: HashMap::with_capacity(capacity),
            ll: LinkedList::with_capacity(capacity),
        };
    }

    /// Creates an empty LinkedHashMap with the specified capacity and
    /// InsertionOrder. The underlying list will continue to
    /// reallocate additional memory by doubling the capacity
    /// everytime the capacity is exceeded. However the list will not
    /// deallocate memory when keys are removed.
    ///
    /// If the capacity is set to 0, and the underlying list is full,
    /// then new memory will be allocated for one new element
    /// everytime an element is added to the list.
    ///
    /// The underlying hashmap will only allocate memory if the
    /// capacity is greater than zero.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// let lhm = LinkedHashMap::<u16, &str>::with_capacity(10);
    /// assert_eq!(lhm.capacity(), 10);
    /// assert_eq!(lhm.len(), 0);
    ///
    /// ```
    pub fn with_capacity(capacity: usize) -> LinkedHashMap<K, V> {
        return Self::new(capacity, Order::InsertionOrder, None);
    }

    /// Returns the number of elements the map can hold before new
    /// memory is allocated.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// assert_eq!(10, lhm.capacity());
    /// assert_eq!(0, lhm.len());
    /// ```
    pub fn capacity(&self) -> usize {
        return self.cap;
    }

    /// Returns the number or elements in the map.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// assert_eq!(lhm.len(), 0);
    /// lhm.insert(1, "a");
    /// assert_eq!(lhm.len(), 1);
    ///
    /// ```
    pub fn len(&self) -> usize {
        return self.map.len();
    }

    /// Removes and drops all the key-value pairs this map. This has
    /// no effect on the allocated capacity of the map or the underlying list.
    ///
    /// This method should complete in *O*(*n*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.insert(1, "a");
    /// lhm.clear();
    /// assert!(lhm.is_empty());
    ///
    /// ```
    pub fn clear(&mut self) {
        self.map.clear();
        self.ll.clear();
    }

    /// Returns true if the map contains no elements and false otherwise.
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// assert!(lhm.is_empty());
    /// lhm.insert(1, "a");
    /// assert!(!lhm.is_empty());
    ///
    /// ```
    pub fn is_empty(&self) -> bool {
        return self.map.len() == 0;
    }

    /// Returns true if the map contains a value for the specified
    /// key. This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.insert(1, "a");
    /// assert_eq!(lhm.contains_key(&1), true);
    /// assert_eq!(lhm.contains_key(&2), false);
    /// ```
    pub fn contains_key(&self, key: &K) -> bool {
        return self.map.contains_key(&PtrKey::new(key));
    }

    /// Returns a handle to the entry corresponding to the key, or None
    /// if the key is not present in the map.
    ///
    /// The returned handle can be used to manipulate the position of the
    /// entry within the map's iteration order without affecting the
    /// iteration order of access methods like `get()`, `get_mut()`, etc.
    ///
    /// This method should complete in *O*(*1*) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
    /// lhm.insert(1, "a");
    /// lhm.insert(2, "b");
    /// lhm.insert(3, "c");
    ///
    /// // Get handle for key 1
    /// if let Some(handle) = lhm.entry_handle(&1) {
    ///     // Move it to the end of iteration order
    ///     lhm.make_tail(handle);
    /// }
    ///
    /// // Now iteration order will be: 2, 3, 1
    /// let keys: Vec<_> = lhm.keys().copied().collect();
    /// assert_eq!(keys, vec![2, 3, 1]);
    ///
    /// // Non-existent key returns None
    /// assert_eq!(lhm.entry_handle(&99), None);
    /// ```
    pub fn entry_handle(&self, key: &K) -> Option<EntryHandle<K, V>> {
        if let Some(node_handle) = self.map.get(&PtrKey::new(key)) {
            return Some(EntryHandle::new(node_handle.clone()));
        }
        None
    }

    /// Moves the entry associated with the given handle to the tail of the 
    /// LinkedHashMap's iteration order (making it the most recently used).
    ///
    /// If the entry is already at the tail of the iteration order, this 
    /// operation has no effect. This method works regardless of whether the
    /// map uses InsertionOrder or AccessOrder.
    ///
    /// Returns `true` if the entry was successfully moved to the tail (or was
    /// already at the tail), and `false` if the handle is invalid.
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
    ///     assert!(lhm.make_tail(handle));
    ///     
    ///     // Now key 1 will be the last in iteration order
    ///     let keys: Vec<_> = lhm.keys().copied().collect();
    ///     assert_eq!(keys, vec![2, 3, 1]);
    /// }
    /// ```
    pub fn make_tail(&mut self, eh: EntryHandle<K, V>) -> bool {
        self.ll.make_tail(&eh.node_handle)
    }

    /// Moves the entry associated with the given handle to the head of the 
    /// LinkedHashMap's iteration order (making it the least recently used).
    ///
    /// If the entry is already at the head of the iteration order, this 
    /// operation has no effect. This method works regardless of whether the
    /// map uses InsertionOrder or AccessOrder.
    ///
    /// Returns `true` if the entry was successfully moved to the head (or was
    /// already at the head), and `false` if the handle is invalid.
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
    /// if let Some(handle) = lhm.entry_handle(&3) {
    ///     assert!(lhm.make_head(handle));
    ///     
    ///     // Now key 3 will be the first in iteration order
    ///     let keys: Vec<_> = lhm.keys().copied().collect();
    ///     assert_eq!(keys, vec![3, 1, 2]);
    /// }
    /// ```
    pub fn make_head(&mut self, eh: EntryHandle<K, V>) -> bool {
        self.ll.make_head(&eh.node_handle)
    }

    /// Returns a reference to the key-value pair associated with the given EntryHandle.
    ///
    /// This method provides O(1) access to an entry using its handle, without affecting
    /// the iteration order (unlike [`get()`](#method.get) which may move accessed entries
    /// to the tail in AccessOrder mode).
    ///
    /// Returns `Some((key, value))` if the handle is valid, or `None` if the handle
    /// is invalid (e.g., the entry was removed from the map).
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
    /// if let Some(handle) = lhm.entry_handle(&2) {
    ///     // Get the entry without affecting iteration order
    ///     assert_eq!(lhm.get_entry(&handle), Some((&2, &"b")));
    ///     
    ///     // Verify order is unchanged
    ///     let keys: Vec<_> = lhm.keys().copied().collect();
    ///     assert_eq!(keys, vec![1, 2, 3]);
    /// }
    ///
    /// // Invalid handle returns None
    /// let invalid_handle = deepmesa_collections::lhmap::EntryHandle::default();
    /// assert_eq!(lhm.get_entry(&invalid_handle), None);
    /// ```
    pub fn get_entry(&self, handle: &EntryHandle<K, V>) -> Option<(&K, &V)> {
        if let Some(entry) = handle.node_handle.val(&self.ll) {
            Some((&entry.key, &entry.val))
        } else {
            None
        }
    }

    /// Returns a reference to the key associated with the given EntryHandle.
    ///
    /// This method provides O(1) access to just the key of an entry using its handle, 
    /// without affecting the iteration order. This is useful when you only need the key
    /// and want to avoid destructuring the result of [`get_entry()`](#method.get_entry).
    ///
    /// Returns `Some(key)` if the handle is valid, or `None` if the handle
    /// is invalid (e.g., the entry was removed from the map).
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
    /// if let Some(handle) = lhm.entry_handle(&2) {
    ///     // Get just the key without affecting iteration order
    ///     assert_eq!(lhm.get_key(&handle), Some(&2));
    ///     
    ///     // Verify order is unchanged
    ///     let keys: Vec<_> = lhm.keys().copied().collect();
    ///     assert_eq!(keys, vec![1, 2, 3]);
    /// }
    ///
    /// // Invalid handle returns None
    /// let invalid_handle = deepmesa_collections::lhmap::EntryHandle::default();
    /// assert_eq!(lhm.get_key(&invalid_handle), None);
    /// ```
    pub fn get_key(&self, handle: &EntryHandle<K, V>) -> Option<&K> {
        handle.node_handle.val(&self.ll).map(|entry| &entry.key)
    }

    /// Returns a reference to the value associated with the given EntryHandle.
    ///
    /// This method provides O(1) access to just the value of an entry using its handle, 
    /// without affecting the iteration order. This is useful when you only need the value
    /// and want to avoid destructuring the result of [`get_entry()`](#method.get_entry).
    ///
    /// Returns `Some(value)` if the handle is valid, or `None` if the handle
    /// is invalid (e.g., the entry was removed from the map).
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
    /// if let Some(handle) = lhm.entry_handle(&2) {
    ///     // Get just the value without affecting iteration order
    ///     assert_eq!(lhm.get_value(&handle), Some(&"b"));
    ///     
    ///     // Verify order is unchanged
    ///     let keys: Vec<_> = lhm.keys().copied().collect();
    ///     assert_eq!(keys, vec![1, 2, 3]);
    /// }
    ///
    /// // Invalid handle returns None
    /// let invalid_handle = deepmesa_collections::lhmap::EntryHandle::default();
    /// assert_eq!(lhm.get_value(&invalid_handle), None);
    /// ```
    pub fn get_value(&self, handle: &EntryHandle<K, V>) -> Option<&V> {
        handle.node_handle.val(&self.ll).map(|entry| &entry.val)
    }

    /// Returns a mutable reference to the value associated with the given EntryHandle.
    ///
    /// This method provides O(1) mutable access to the value of an entry using its handle, 
    /// without affecting the iteration order. This allows you to modify the value in-place
    /// while preserving the entry's position in the map.
    ///
    /// Returns `Some(value)` if the handle is valid, or `None` if the handle
    /// is invalid (e.g., the entry was removed from the map).
    ///
    /// This operation completes in O(1) time.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, String>::new(10, Order::InsertionOrder, None);
    /// lhm.put(1, "a".to_string());
    /// lhm.put(2, "b".to_string());
    /// lhm.put(3, "c".to_string());
    ///
    /// if let Some(handle) = lhm.entry_handle(&2) {
    ///     // Mutate the value without affecting iteration order
    ///     if let Some(value) = lhm.get_value_mut(&handle) {
    ///         value.push_str("_modified");
    ///     }
    ///     
    ///     // Verify the change
    ///     assert_eq!(lhm.get_value(&handle), Some(&"b_modified".to_string()));
    ///     
    ///     // Verify order is unchanged
    ///     let keys: Vec<_> = lhm.keys().copied().collect();
    ///     assert_eq!(keys, vec![1, 2, 3]);
    /// }
    ///
    /// // Invalid handle returns None
    /// let invalid_handle = deepmesa_collections::lhmap::EntryHandle::default();
    /// assert_eq!(lhm.get_value_mut(&invalid_handle), None);
    /// ```
    pub fn get_value_mut(&mut self, handle: &EntryHandle<K, V>) -> Option<&mut V> {
        handle.node_handle.val_mut(&mut self.ll).map(|entry| &mut entry.val)
    }

    /// Removes and returns the head (oldest) entry from the LinkedHashMap.
    ///
    /// The head entry is the least recently inserted or accessed entry depending 
    /// on the map's order mode. This is the same entry that would be removed by 
    /// the eviction policy.
    ///
    /// Returns `Some((key, value))` if an entry was removed, or `None` if the 
    /// map is empty.
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
    /// // Remove the head (oldest entry)
    /// assert_eq!(lhm.remove_head(), Some((1, "a")));
    /// assert_eq!(lhm.remove_head(), Some((2, "b")));
    /// assert_eq!(lhm.remove_head(), Some((3, "c")));
    /// assert_eq!(lhm.remove_head(), None);
    /// ```
    /// Returns a reference to the head (oldest) entry in the LinkedHashMap.
    ///
    /// The head entry is the least recently inserted or accessed entry depending
    /// on the map's order mode. This is the entry that would be removed by the
    /// eviction policy.
    ///
    /// Returns `Some((&key, &value))` if the map is not empty, or `None` if the
    /// map is empty.
    ///
    /// This operation completes in O(1) time and does not modify the map.
    ///
    /// Returns a reference to the entry at the head of the LinkedHashMap.
    ///
    /// This method does not change the access order and works the same
    /// regardless of whether the map uses InsertionOrder or AccessOrder.
    /// Unlike insertion operations, this method is purely a read operation
    /// and will not affect the ordering of entries.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
    /// assert_eq!(lhm.head(), None);
    ///
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    /// lhm.put(3, "c");
    ///
    /// // Head is the oldest entry
    /// assert_eq!(lhm.head(), Some((&1, &"a")));
    /// ```
    pub fn head(&self) -> Option<(&K, &V)> {
        if let Some(entry) = self.ll.head() {
            Some((&entry.key, &entry.val))
        } else {
            None
        }
    }

    pub fn remove_head(&mut self) -> Option<(K, V)> {
        if let Some(entry) = self.ll.pop_head() {
            self.map.remove(&PtrKey::new(&entry.key));
            Some((entry.key, entry.val))
        } else {
            None
        }
    }

    /// Removes and returns the tail (newest) entry from the LinkedHashMap.
    ///
    /// The tail entry is the most recently inserted or accessed entry depending 
    /// on the map's order mode. This is the opposite of the entry that would be 
    /// removed by the eviction policy.
    ///
    /// Returns `Some((key, value))` if an entry was removed, or `None` if the 
    /// map is empty.
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
    /// // Remove the tail (newest entry)
    /// assert_eq!(lhm.remove_tail(), Some((3, "c")));
    /// assert_eq!(lhm.remove_tail(), Some((2, "b")));
    /// assert_eq!(lhm.remove_tail(), Some((1, "a")));
    /// assert_eq!(lhm.remove_tail(), None);
    /// ```
    /// Returns a reference to the tail (newest) entry in the LinkedHashMap.
    ///
    /// The tail entry is the most recently inserted or accessed entry depending
    /// on the map's order mode. This is the opposite of the entry that would be
    /// removed by the eviction policy.
    ///
    /// Returns `Some((&key, &value))` if the map is not empty, or `None` if the
    /// map is empty.
    ///
    /// This operation completes in O(1) time and does not modify the map.
    ///
    /// Returns a reference to the entry at the tail of the LinkedHashMap.
    ///
    /// This method does not change the access order and works the same
    /// regardless of whether the map uses InsertionOrder or AccessOrder.
    /// Unlike insertion operations, this method is purely a read operation
    /// and will not affect the ordering of entries.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
    /// assert_eq!(lhm.tail(), None);
    ///
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    /// lhm.put(3, "c");
    ///
    /// // Tail is the newest entry
    /// assert_eq!(lhm.tail(), Some((&3, &"c")));
    /// ```
    pub fn tail(&self) -> Option<(&K, &V)> {
        if let Some(entry) = self.ll.tail() {
            Some((&entry.key, &entry.val))
        } else {
            None
        }
    }

    pub fn remove_tail(&mut self) -> Option<(K, V)> {
        if let Some(entry) = self.ll.pop_tail() {
            self.map.remove(&PtrKey::new(&entry.key));
            Some((entry.key, entry.val))
        } else {
            None
        }
    }

    /// Returns a reference to the value corresponding to the key. If
    /// the Map was created with AccessOrder then the key accessed is
    /// moved to the tail of the underlying linked list (most
    /// recently used).
    ///
    /// If the key is not present then this method returns None and
    /// the order is unaffected.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.insert(1, "a");
    /// lhm.insert(2, "b");
    ///
    /// let mut iter = lhm.iter();
    /// assert_eq!(iter.next(), Some((&1, &"a")));
    /// assert_eq!(iter.next(), Some((&2, &"b")));
    ///
    /// assert_eq!(lhm.get(&1), Some(&"a"));
    /// assert_eq!(lhm.get(&3), None);
    ///
    /// let mut iter = lhm.iter();
    /// assert_eq!(iter.next(), Some((&2, &"b")));
    /// assert_eq!(iter.next(), Some((&1, &"a")));
    /// assert_eq!(iter.next(), None);
    ///
    /// ```
    pub fn get(&mut self, key: &K) -> Option<&V> {
        if let Some(llnode) = self.map.get(&PtrKey::new(key)) {
            if self.order == Order::AccessOrder {
                if !self.ll.make_tail(llnode) {
                    panic!("failed to make tail!");
                }
            }

            match llnode.val(&self.ll) {
                None => panic!("List does not doesn't contain expected value!"),
                Some(entry) => {
                    return Some(&entry.val);
                }
            }
        }
        None
    }

    /// Returns the key-value pair corresponding to the supplied key.
    /// the Map was created with AccessOrder then the key accessed is
    /// moved to the tail of the underlying linked list (most
    /// recently accessed).
    ///
    /// If the key is not present then this method returns None and
    /// the order is unaffected.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.insert(1, "a");
    /// lhm.insert(2, "b");
    ///
    /// let mut iter = lhm.iter();
    /// assert_eq!(iter.next(), Some((&1, &"a")));
    /// assert_eq!(iter.next(), Some((&2, &"b")));
    ///
    /// assert_eq!(lhm.get_key_value(&1), Some((&1, &"a")));
    /// assert_eq!(lhm.get(&3), None);
    ///
    /// let mut iter = lhm.iter();
    /// assert_eq!(iter.next(), Some((&2, &"b")));
    /// assert_eq!(iter.next(), Some((&1, &"a")));
    /// assert_eq!(iter.next(), None);
    ///
    /// ```
    pub fn get_key_value(&mut self, key: &K) -> Option<(&K, &V)> {
        if let Some(llnode) = self.map.get(&PtrKey::new(key)) {
            if self.order == Order::AccessOrder {
                if !self.ll.make_tail(llnode) {
                    panic!("failed to make tail!");
                }
            }

            match llnode.val(&self.ll) {
                None => panic!("List does not doesn't contain expected value!"),
                Some(entry) => {
                    return Some((&entry.key, &entry.val));
                }
            }
        }
        None
    }

    /// Returns a mutable reference to the value corresponding to the key. If
    /// the Map was created with AccessOrder then the key accessed is
    /// moved to the tail of the underlying linked list (most
    /// recently used).
    ///
    /// If the key is not present then this method returns None and
    /// the order is unaffected.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.insert(1, "a");
    /// lhm.insert(2, "b");
    ///
    /// let mut iter = lhm.iter();
    /// assert_eq!(iter.next(), Some((&1, &"a")));
    /// assert_eq!(iter.next(), Some((&2, &"b")));
    ///
    /// if let Some(val) = lhm.get_mut(&1) {
    ///     *val = "d";
    /// }
    ///
    /// let mut iter = lhm.iter();
    /// assert_eq!(iter.next(), Some((&2, &"b")));
    /// assert_eq!(iter.next(), Some((&1, &"d")));
    /// assert_eq!(iter.next(), None);
    ///
    /// ```
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if let Some(llnode) = self.map.get(&PtrKey::new(key)) {
            if self.order == Order::AccessOrder {
                if !self.ll.make_tail(llnode) {
                    panic!("failed to make tail!");
                }
            }

            match llnode.val_mut(&mut self.ll) {
                None => panic!("List does not doesn't contain expected value!"),
                Some(entry) => {
                    return Some(&mut entry.val);
                }
            }
        }
        None
    }

    /// Removes a key from the map, returning the value at the key if
    /// the key was previously in the map. If the key was not present
    /// then this method returns None. The iteration order is not
    /// affected by this method except to remove the specified key
    /// from the underlying linked list.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.insert(1, "a");
    /// assert_eq!(lhm.remove(&1), Some("a"));
    /// assert_eq!(lhm.remove(&1), None);
    /// ```
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if let Some(llnode) = self.map.remove(&PtrKey::new(key)) {
            match self.ll.pop_node(&llnode) {
                None => panic!("List doesn't contain expected value!"),
                Some(entry) => return Some(entry.val),
            }
        }

        None
    }

    /// Removes a key from the map, returning the key value pair at
    /// the key if the key was previously in the map. If the key was
    /// not present then this method returns None. The iteration order
    /// is not affected by this method except to remove the specified
    /// key from the underlying linked list.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.insert(1, "a");
    /// assert_eq!(lhm.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(lhm.remove(&1), None);
    /// ```
    pub fn remove_entry(&mut self, key: &K) -> Option<(K, V)> {
        if let Some(llnode) = self.map.remove(&PtrKey::new(key)) {
            match self.ll.pop_node(&llnode) {
                None => panic!("List doesn't contain expected value!"),
                Some(entry) => return Some((entry.key, entry.val)),
            }
        }

        None
    }

    /// Inserts a key-value pair into the map. Unlike the insert
    /// method this does not return the old value previously stored.
    /// The new value inserted is placed at the tail of the underlying
    /// linked list (most recently used).
    ///
    /// #Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.put(1, "a");
    /// assert_eq!(lhm.is_empty(), false);
    /// ```
    pub fn put(&mut self, k: K, v: V) {
        match self.map.get(&PtrKey::new(&k)) {
            Some(llnode) => match llnode.val_mut(&mut self.ll) {
                None => panic!("Value not found in LL"),
                Some(entry) => {
                    (*entry).val = v;
                    if !self.ll.make_tail(llnode) {
                        panic!("failed to make tail!");
                    }
                }
            },
            None => {
                let ll_node = self.ll.push_tail(Entry::new(k, v));

                match self.ll.node(&ll_node) {
                    None => panic!("Value not found in LL"),
                    Some(entry_ref) => unsafe {
                        let key_ptr = entry_ref.key_ptr();
                        self.map.insert(PtrKey::from_ptr(key_ptr), ll_node);
                    },
                }
            }
        }

        self.evict_eldest();
    }

    /// Inserts a key-value pair into the map and returns the old
    /// value (if any). If a value was not present for this key then
    /// this method returns None.  The new value inserted is placed at
    /// the tail of the underlying linked list (most recently used).
    ///
    /// The key is not updated and only the value corresponding to the
    /// key is updated.
    ///
    /// #Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// assert_eq!(lhm.insert(1, "a"), None);
    /// assert_eq!(lhm.is_empty(), false);
    ///
    /// lhm.insert(2, "b");
    /// assert_eq!(lhm.insert(2, "c"), Some("b"));
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let mut retval: Option<V> = None;

        match self.map.get(&PtrKey::new(&k)) {
            None => {
                let ll_node = self.ll.push_tail(Entry::new(k, v));

                match self.ll.node(&ll_node) {
                    None => panic!("Value not found in LL"),
                    Some(entry_ref) => unsafe {
                        let key_ptr = entry_ref.key_ptr();
                        self.map.insert(PtrKey::from_ptr(key_ptr), ll_node);
                    },
                }
            }
            Some(llnode) => match llnode.val_mut(&mut self.ll) {
                None => panic!("value not found in linkedlist"),
                Some(entry) => {
                    retval = Some(std::mem::replace(&mut (*entry).val, v));
                    if !self.ll.make_tail(llnode) {
                        panic!("failed to make tail!");
                    }
                }
            },
        }

        self.evict_eldest();
        return retval;
    }

    /// An Iterator that vists all key value pairs in a predictable
    /// order.
    ///
    /// Iteration over the map requires time proportional to the
    /// length of the map (*O*(*len*)) regardless of the capacity
    /// because it iterates over the elements of the underlying linked
    /// list. If the map is constructed with [`InsertionOrder`](Order)
    /// then the iteration order is from oldest entry inserted to the
    /// newest entry inserted. If the map is constructed with
    /// [`AccessOrder`](Order) then the iteration order is from oldest
    /// entry accessed to the newest entry accessed.
    ///
    /// The iterator element type is (&'a K, &'a V).
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// // Construct a map in InsertionOrder
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    ///
    /// lhm.get(&1);
    ///
    /// let mut iter = lhm.iter();
    /// assert_eq!(iter.next(), Some((&1, &"a")));
    /// assert_eq!(iter.next(), Some((&2, &"b")));
    ///
    /// // Construct a map in AccessOrder
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    ///
    /// lhm.get(&1);
    ///
    /// let mut iter = lhm.iter();
    /// assert_eq!(iter.next(), Some((&2, &"b")));
    /// assert_eq!(iter.next(), Some((&1, &"a")));
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        return Iter::new(self);
    }

    /// An Iterator that vists all key value pairs in a predictable
    /// order with mutable references to the values.
    ///
    /// Iteration over the map requires time proportional to the
    /// length of the map (*O*(*len*)) regardless of the capacity
    /// because it iterates over the elements of the underlying linked
    /// list. If the map is constructed with [`InsertionOrder`](Order)
    /// then the iteration order is from oldest entry inserted to the
    /// newest entry inserted. If the map is constructed with
    /// [`AccessOrder`](Order) then the iteration order is from oldest
    /// entry accessed to the newest entry accessed
    ///
    /// The iterator element type is (&'a K, &'a mut V).
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// // Construct a map in InsertionOrder
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    ///
    /// lhm.get(&1);
    ///
    /// for (_, val) in lhm.iter_mut() {
    ///     *val = "d";
    /// }
    ///
    /// assert_eq!(lhm.get(&1), Some(&"d"));
    /// assert_eq!(lhm.get(&2), Some(&"d"));
    ///
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        return IterMut::new(self);
    }

    /// An Iterator that vists all keys in a predictable order.
    ///
    /// Iteration over the map requires time proportional to the
    /// length of the map (*O*(*len*)) regardless of the capacity
    /// because it iterates over the elements of the underlying linked
    /// list. If the map is constructed with [`InsertionOrder`](Order)
    /// then the iteration order is from oldest entry inserted to the
    /// newest entry inserted. If the map is constructed with
    /// [`AccessOrder`](Order) then the iteration order is from oldest
    /// entry accessed to the newest entry accessed.
    ///
    /// The iterator element type is &'a K.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// // Construct a map in InsertionOrder
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    ///
    /// lhm.get(&1);
    ///
    /// let mut iter = lhm.keys();
    /// assert_eq!(iter.next(), Some((&1)));
    /// assert_eq!(iter.next(), Some((&2)));
    ///
    /// // Construct a map in AccessOrder
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    ///
    /// lhm.get(&1);
    ///
    /// let mut iter = lhm.keys();
    /// assert_eq!(iter.next(), Some((&2)));
    /// assert_eq!(iter.next(), Some((&1)));
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        return Keys::new(self);
    }

    /// An Iterator that vists all values in a predictable order.
    ///
    /// Iteration over the map requires time proportional to the
    /// length of the map (*O*(*len*)) regardless of the capacity
    /// because it iterates over the elements of the underlying linked
    /// list. If the map is constructed with [`InsertionOrder`](Order)
    /// then the iteration order is from oldest entry inserted to the
    /// newest entry inserted. If the map is constructed with
    /// [`AccessOrder`](Order) then the iteration order is from oldest
    /// entry accessed to the newest entry accessed.
    ///
    /// The iterator element type is &'a V.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;

    ///
    /// // Construct a map in InsertionOrder
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    ///
    /// lhm.get(&1);
    ///
    /// let mut iter = lhm.values();
    /// assert_eq!(iter.next(), Some((&"a")));
    /// assert_eq!(iter.next(), Some((&"b")));
    ///
    /// // Construct a map in AccessOrder
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    ///
    /// lhm.get(&1);
    ///
    /// let mut iter = lhm.values();
    /// assert_eq!(iter.next(), Some((&"b")));
    /// assert_eq!(iter.next(), Some((&"a")));
    /// ```
    pub fn values(&self) -> Values<'_, K, V> {
        return Values::new(self);
    }

    /// An Iterator that vists all values in a predictable order with
    /// mutable references to the values.
    ///
    /// Iteration over the map requires time proportional to the
    /// length of the map (*O*(*len*)) regardless of the capacity
    /// because it iterates over the elements of the underlying linked
    /// list. If the map is constructed with [`InsertionOrder`](Order)
    /// then the iteration order is from oldest entry inserted to the
    /// newest entry inserted. If the map is constructed with
    /// [`AccessOrder`](Order) then the iteration order is from oldest
    /// entry accessed to the newest entry accessed.
    ///
    /// The iterator element type is &'a mut V.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::lhmap::Order;
    ///
    /// // Construct a map in InsertionOrder
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
    /// lhm.put(1, "a");
    /// lhm.put(2, "b");
    ///
    /// lhm.get(&1);
    ///
    /// for val in lhm.values_mut() {
    ///     *val = "d";
    /// }
    ///
    /// assert_eq!(lhm.get(&1), Some(&"d"));
    /// assert_eq!(lhm.get(&2), Some(&"d"));
    ///
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        return ValuesMut::new(self);
    }

    fn evict_eldest(&mut self) {
        if let Some(ee_fn) = self.evict_eldest {
            if let Some(entry) = self.ll.head() {
                if ee_fn(self.len(), self.cap, entry) {
                    match self.ll.pop_head() {
                        None => panic!("pop head unexpectedly returned None"),
                        Some(entry) => {
                            self.map.remove(&PtrKey::new(&entry.key));
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Order;
    use crate::lhmap::entry::Entry;
    use crate::lhmap::lhmap::LinkedHashMap;

    #[derive(Debug)]
    struct ValObject {
        int_v: u16,
    }

    impl ValObject {
        fn new(val: u16) -> ValObject {
            return ValObject { int_v: val };
        }
    }

    #[test]
    fn test_iter() {
        let mut lhm: LinkedHashMap<String, ValObject> =
            LinkedHashMap::new(10, Order::AccessOrder, None);

        for i in 0u16..10 {
            lhm.put(format!("Hello-{}", i), ValObject::new(i));
            assert_eq!((i + 1) as usize, lhm.len());
        }

        lhm.get(&"Hello-3".to_string());

        let mut iter = lhm.iter();
        while let Some((key, val)) = iter.next() {
            println!("Key: {:?}, Val: {:?}", key, val);
        }

        println!("Now using IntoIterator!");

        for (key, val) in lhm.iter() {
            println!("Key: {:?}, Val: {:?}", key, val);
        }

        println!("Now using Keys!");

        let mut keys = lhm.keys();
        while let Some(key) = keys.next() {
            println!("Key: {:?}", key);
        }

        println!("Now using Values!");

        let mut values = lhm.values();
        while let Some(val) = values.next() {
            println!("Value: {:?}", val);
        }
    }

    #[test]
    fn test_put_get_remove() {
        let mut lhm: LinkedHashMap<String, ValObject> =
            LinkedHashMap::new(10, Order::AccessOrder, None);

        for i in 0u16..10 {
            lhm.put(format!("Hello-{}", i), ValObject::new(i));
            assert_eq!((i + 1) as usize, lhm.len());
        }

        for i in 0u16..10 {
            match lhm.get(&format!("Hello-{}", i)) {
                None => {
                    assert!(false, "Unexpected None for Key Hello-{}", i);
                    assert_eq!(10, lhm.len());
                }
                Some(val_o) => {
                    assert_eq!(val_o.int_v, i);
                }
            }
        }

        for i in 0u16..10 {
            match lhm.remove(&format!("Hello-{}", i)) {
                None => {
                    assert!(false, "Unexpected None for removed Key Hello-{}", i);
                }
                Some(val_o) => {
                    assert_eq!(val_o.int_v, i);
                }
            }

            match lhm.get(&format!("Hello-{}", i)) {
                None => {
                    assert!(true);
                }
                Some(val_o) => {
                    assert!(false, "Unexpected Some with val: {}", val_o.int_v);
                }
            }
        }
    }

    #[test]
    fn test_put_overwrite() {
        let mut lhm: LinkedHashMap<String, ValObject> =
            LinkedHashMap::new(10, Order::AccessOrder, None);
        lhm.put("Hello-0".to_string(), ValObject::new(0));
        assert_eq!(lhm.len(), 1);

        match lhm.get(&"Hello-0".to_string()) {
            None => {
                assert!(false, "Unexpected None for Key Hello-0");
            }
            Some(val_o) => {
                assert_eq!(val_o.int_v, 0);
                assert_eq!(lhm.len(), 1);
            }
        }

        lhm.put("Hello-0".to_string(), ValObject::new(10));
        match lhm.get(&"Hello-0".to_string()) {
            None => {
                assert!(false, "Unexpected None for Key Hello-0");
            }
            Some(val_o) => {
                assert_eq!(val_o.int_v, 10);
                assert_eq!(lhm.len(), 1);
            }
        }
    }

    fn evict_fn<K, V>(len: usize, capacity: usize, _e: &Entry<K, V>) -> bool {
        if len > capacity {
            return true;
        }
        return false;
    }

    #[test]
    fn test_eviction() {
        let mut lhm: LinkedHashMap<String, ValObject> =
            LinkedHashMap::new(10, Order::AccessOrder, Some(evict_fn));

        for i in 0u16..20 {
            lhm.put(format!("Hello-{}", i), ValObject::new(i));
            if i >= 10 {
                assert_eq!(10, lhm.len());
            } else {
                assert_eq!((i + 1) as usize, lhm.len());
            }
        }
    }

    #[test]
    fn test_foo() {
        use crate::lhmap::entry::Entry;
        pub fn evict<K, V>(len: usize, capacity: usize, _e: &Entry<K, V>) -> bool {
            if len > capacity {
                return true;
            }
            return false;
        }

        use crate::lhmap::entry::Order;
        use crate::lhmap::lhmap::LinkedHashMap;

        let mut lhm = LinkedHashMap::<u16, &str>::new(2, Order::AccessOrder, Some(evict));
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        assert_eq!(lhm.get(&2), Some(&"b"));
        lhm.put(4, "d");
        assert_eq!(lhm.get(&1), None);

        // let mut lhm = LinkedHashMap::<&str, u16>::with_capacity(10);
        // lhm.put("a", 1);
        // lhm.put("b", 2);
        // lhm.put("c", 3);
        // lhm.put("d", 4);

        // let mut iter = lhm.iter();
        // println!("{:?}", iter.next());
        // println!("{:?}", iter.next());
        // println!("{:?}", iter.next());
        // println!("{:?}", iter.next());
        // println!("{:?}", iter.next());
        // println!("{:?}", iter.next());
        // println!("Now in reverse!");
        // iter = iter.reverse();
        // println!("{:?}", iter.next());
        // println!("{:?}", iter.next());

        // println!("Now in reverse!");

        // //assert_eq!(lhm.get(&"a"), Some(&1));
        // let mut iter = lhm.iter().reverse();
        // println!("{:?}", iter.next());
        // println!("{:?}", iter.next());
        // println!("{:?}", iter.next());
    }

    #[test]
    fn test_entry_handle_basic() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Test getting valid handle
        let handle1 = lhm.entry_handle(&1);
        assert!(handle1.is_some());
        
        // Test getting invalid handle
        let handle_invalid = lhm.entry_handle(&99);
        assert!(handle_invalid.is_none());
    }


    #[test]
    fn test_entry_handle_make_tail_insertion_order() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Initial order should be 1, 2, 3
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3]);

        // Move key 1 to end
        if let Some(handle) = lhm.entry_handle(&1) {
            assert!(lhm.make_tail(handle));
        }

        // Order should now be 2, 3, 1
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![2, 3, 1]);

        // Values should remain unchanged (use mutable reference for get)
        assert_eq!(lhm.get(&1), Some(&"a"));
        assert_eq!(lhm.get(&2), Some(&"b"));
        assert_eq!(lhm.get(&3), Some(&"c"));
    }

    #[test]
    fn test_entry_handle_make_tail_access_order() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Initial order should be 1, 2, 3 (insertion order)
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3]);

        // Move key 1 to end using handle (should work regardless of AccessOrder)
        if let Some(handle) = lhm.entry_handle(&1) {
            assert!(lhm.make_tail(handle));
        }

        // Order should now be 2, 3, 1
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![2, 3, 1]);
    }

    #[test]
    fn test_entry_handle_make_tail_already_at_end() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Move key 3 to end first to make it actually at the end
        if let Some(handle) = lhm.entry_handle(&3) {
            assert!(lhm.make_tail(handle));
        }
        
        // Now 3 should be at the end: [1, 2, 3]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3]);

        // Move key 3 to end again (it's already at the end)
        if let Some(handle) = lhm.entry_handle(&3) {
            assert!(lhm.make_tail(handle));
        }

        // Order should remain the same: 1, 2, 3
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3]);
    }

    #[test]
    fn test_entry_handle_invalid_handle() {
        let mut lhm1 = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        let mut lhm2 = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        
        lhm1.put(1, "a");
        lhm2.put(1, "b");

        // Get handle from lhm1
        let handle = lhm1.entry_handle(&1).unwrap();
        
        // Remove the entry from lhm1 to invalidate the handle
        lhm1.remove(&1);
        
        // Try to use invalid handle - should return false
        assert_eq!(lhm1.make_tail(handle), false);
    }

    #[test]
    fn test_entry_handle_multiple_operations() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");
        lhm.put(4, "d");

        // Initial order: [1, 2, 3, 4]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3, 4]);

        // Move key 2 to end: [1, 3, 4, 2]
        if let Some(handle) = lhm.entry_handle(&2) {
            assert!(lhm.make_tail(handle));
        }
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 3, 4, 2]);

        // Move key 1 to end: [3, 4, 2, 1]
        if let Some(handle) = lhm.entry_handle(&1) {
            assert!(lhm.make_tail(handle));
        }
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![3, 4, 2, 1]);
    }

    #[test]
    fn test_entry_handle_with_access_operations() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Initial order: [1, 2, 3]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3]);

        // Access key 1 (should move it to head in AccessOrder, making it last in iteration)
        lhm.get(&1);
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![2, 3, 1]); // 1 moved to most recently accessed (end)

        // Use handle to move key 2 to end (should move it to head of list, end of iteration)
        if let Some(handle) = lhm.entry_handle(&2) {
            assert!(lhm.make_tail(handle));
        }
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![3, 1, 2]); // 2 moved to end
    }

    #[test]
    fn test_entry_handle_default() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");

        // Create a default handle (invalid)
        let default_handle = crate::lhmap::entry::EntryHandle::<u16, &str>::default();
        
        // Try to use it - should return false
        assert_eq!(lhm.make_tail(default_handle), false);
    }

    #[test]
    fn test_get_entry_basic() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Test getting valid entries
        if let Some(handle1) = lhm.entry_handle(&1) {
            assert_eq!(lhm.get_entry(&handle1), Some((&1, &"a")));
        } else {
            panic!("Expected valid handle for key 1");
        }

        if let Some(handle2) = lhm.entry_handle(&2) {
            assert_eq!(lhm.get_entry(&handle2), Some((&2, &"b")));
        } else {
            panic!("Expected valid handle for key 2");
        }

        if let Some(handle3) = lhm.entry_handle(&3) {
            assert_eq!(lhm.get_entry(&handle3), Some((&3, &"c")));
        } else {
            panic!("Expected valid handle for key 3");
        }

        // Test invalid handle
        let invalid_handle = crate::lhmap::entry::EntryHandle::<u16, &str>::default();
        assert_eq!(lhm.get_entry(&invalid_handle), None);
    }

    #[test]
    fn test_get_entry_does_not_affect_order() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Initial order: [1, 2, 3]
        let keys_before: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys_before, vec![1, 2, 3]);

        // Get entry using handle - should NOT affect AccessOrder
        if let Some(handle1) = lhm.entry_handle(&1) {
            assert_eq!(lhm.get_entry(&handle1), Some((&1, &"a")));
        }

        // Order should remain the same
        let keys_after: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys_after, vec![1, 2, 3]);
        assert_eq!(keys_before, keys_after);

        // Compare with regular get() which DOES affect AccessOrder
        assert_eq!(lhm.get(&1), Some(&"a"));
        let keys_after_get: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys_after_get, vec![2, 3, 1]); // 1 moved to tail
    }

    #[test]
    fn test_get_entry_invalid_after_removal() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");

        // Get handle for key 1
        let handle1 = lhm.entry_handle(&1).expect("Expected valid handle");
        
        // Verify handle works initially
        assert_eq!(lhm.get_entry(&handle1), Some((&1, &"a")));

        // Remove the entry
        assert_eq!(lhm.remove(&1), Some("a"));

        // Now the handle should be invalid
        assert_eq!(lhm.get_entry(&handle1), None);
    }

    #[test]
    fn test_get_entry_insertion_order() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Get all handles
        let handle1 = lhm.entry_handle(&1).unwrap();
        let handle2 = lhm.entry_handle(&2).unwrap();
        let handle3 = lhm.entry_handle(&3).unwrap();

        // Access entries in different order - should not affect iteration order
        assert_eq!(lhm.get_entry(&handle3), Some((&3, &"c")));
        assert_eq!(lhm.get_entry(&handle1), Some((&1, &"a")));
        assert_eq!(lhm.get_entry(&handle2), Some((&2, &"b")));

        // Iteration order should remain unchanged
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3]);
    }

    #[test]
    fn test_get_entry_with_handle_operations() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Get handle and verify initial state
        let handle2 = lhm.entry_handle(&2).unwrap();
        assert_eq!(lhm.get_entry(&handle2), Some((&2, &"b")));

        // Move entry to tail using handle
        assert!(lhm.make_tail(handle2.clone()));
        
        // Handle should still be valid and return same data
        assert_eq!(lhm.get_entry(&handle2), Some((&2, &"b")));
        
        // But iteration order should have changed
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 3, 2]);

        // Move entry to head using handle
        assert!(lhm.make_head(handle2.clone()));
        
        // Handle should still be valid
        assert_eq!(lhm.get_entry(&handle2), Some((&2, &"b")));
        
        // Iteration order should have changed again
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![2, 1, 3]);
    }

    #[test]
    fn test_get_key_basic() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Test getting valid keys
        if let Some(handle1) = lhm.entry_handle(&1) {
            assert_eq!(lhm.get_key(&handle1), Some(&1));
        } else {
            panic!("Expected valid handle for key 1");
        }

        if let Some(handle2) = lhm.entry_handle(&2) {
            assert_eq!(lhm.get_key(&handle2), Some(&2));
        } else {
            panic!("Expected valid handle for key 2");
        }

        if let Some(handle3) = lhm.entry_handle(&3) {
            assert_eq!(lhm.get_key(&handle3), Some(&3));
        } else {
            panic!("Expected valid handle for key 3");
        }

        // Test invalid handle
        let invalid_handle = crate::lhmap::entry::EntryHandle::<u16, &str>::default();
        assert_eq!(lhm.get_key(&invalid_handle), None);
    }

    #[test]
    fn test_get_key_does_not_affect_order() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Initial order: [1, 2, 3]
        let keys_before: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys_before, vec![1, 2, 3]);

        // Get key using handle - should NOT affect AccessOrder
        if let Some(handle1) = lhm.entry_handle(&1) {
            assert_eq!(lhm.get_key(&handle1), Some(&1));
        }

        // Order should remain the same
        let keys_after: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys_after, vec![1, 2, 3]);
        assert_eq!(keys_before, keys_after);
    }

    #[test]
    fn test_get_key_invalid_after_removal() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");

        // Get handle for key 1
        let handle1 = lhm.entry_handle(&1).expect("Expected valid handle");
        
        // Verify handle works initially
        assert_eq!(lhm.get_key(&handle1), Some(&1));

        // Remove the entry
        assert_eq!(lhm.remove(&1), Some("a"));

        // Now the handle should be invalid
        assert_eq!(lhm.get_key(&handle1), None);
    }

    #[test]
    fn test_get_value_basic() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Test getting valid values
        if let Some(handle1) = lhm.entry_handle(&1) {
            assert_eq!(lhm.get_value(&handle1), Some(&"a"));
        } else {
            panic!("Expected valid handle for key 1");
        }

        if let Some(handle2) = lhm.entry_handle(&2) {
            assert_eq!(lhm.get_value(&handle2), Some(&"b"));
        } else {
            panic!("Expected valid handle for key 2");
        }

        if let Some(handle3) = lhm.entry_handle(&3) {
            assert_eq!(lhm.get_value(&handle3), Some(&"c"));
        } else {
            panic!("Expected valid handle for key 3");
        }

        // Test invalid handle
        let invalid_handle = crate::lhmap::entry::EntryHandle::<u16, &str>::default();
        assert_eq!(lhm.get_value(&invalid_handle), None);
    }

    #[test]
    fn test_get_value_does_not_affect_order() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Initial order: [1, 2, 3]
        let keys_before: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys_before, vec![1, 2, 3]);

        // Get value using handle - should NOT affect AccessOrder
        if let Some(handle1) = lhm.entry_handle(&1) {
            assert_eq!(lhm.get_value(&handle1), Some(&"a"));
        }

        // Order should remain the same
        let keys_after: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys_after, vec![1, 2, 3]);
        assert_eq!(keys_before, keys_after);
    }

    #[test]
    fn test_get_value_invalid_after_removal() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");

        // Get handle for key 1
        let handle1 = lhm.entry_handle(&1).expect("Expected valid handle");
        
        // Verify handle works initially
        assert_eq!(lhm.get_value(&handle1), Some(&"a"));

        // Remove the entry
        assert_eq!(lhm.remove(&1), Some("a"));

        // Now the handle should be invalid
        assert_eq!(lhm.get_value(&handle1), None);
    }

    #[test]
    fn test_get_value_mut_basic() {
        let mut lhm = LinkedHashMap::<u16, String>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a".to_string());
        lhm.put(2, "b".to_string());
        lhm.put(3, "c".to_string());

        // Test getting and modifying valid values
        if let Some(handle1) = lhm.entry_handle(&1) {
            if let Some(value) = lhm.get_value_mut(&handle1) {
                assert_eq!(value, &"a".to_string());
                value.push_str("_modified");
                assert_eq!(value, &"a_modified".to_string());
            } else {
                panic!("Expected valid mutable value for key 1");
            }
        } else {
            panic!("Expected valid handle for key 1");
        }

        // Verify the change persisted
        if let Some(handle1) = lhm.entry_handle(&1) {
            assert_eq!(lhm.get_value(&handle1), Some(&"a_modified".to_string()));
        }

        // Test invalid handle
        let invalid_handle = crate::lhmap::entry::EntryHandle::<u16, String>::default();
        assert_eq!(lhm.get_value_mut(&invalid_handle), None);
    }

    #[test]
    fn test_get_value_mut_does_not_affect_order() {
        let mut lhm = LinkedHashMap::<u16, String>::new(10, Order::AccessOrder, None);
        lhm.put(1, "a".to_string());
        lhm.put(2, "b".to_string());
        lhm.put(3, "c".to_string());

        // Initial order: [1, 2, 3]
        let keys_before: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys_before, vec![1, 2, 3]);

        // Modify value using handle - should NOT affect AccessOrder
        if let Some(handle1) = lhm.entry_handle(&1) {
            if let Some(value) = lhm.get_value_mut(&handle1) {
                value.push_str("_modified");
            }
        }

        // Order should remain the same even after mutation
        let keys_after: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys_after, vec![1, 2, 3]);
        assert_eq!(keys_before, keys_after);

        // Verify the modification worked
        if let Some(handle1) = lhm.entry_handle(&1) {
            assert_eq!(lhm.get_value(&handle1), Some(&"a_modified".to_string()));
        }
    }

    #[test]
    fn test_get_value_mut_invalid_after_removal() {
        let mut lhm = LinkedHashMap::<u16, String>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a".to_string());
        lhm.put(2, "b".to_string());

        // Get handle for key 1
        let handle1 = lhm.entry_handle(&1).expect("Expected valid handle");
        
        // Verify handle works initially
        if let Some(value) = lhm.get_value_mut(&handle1) {
            value.push_str("_test");
        }
        assert_eq!(lhm.get_value(&lhm.entry_handle(&1).unwrap()), Some(&"a_test".to_string()));

        // Remove the entry
        assert_eq!(lhm.remove(&1), Some("a_test".to_string()));

        // Now the handle should be invalid
        assert_eq!(lhm.get_value_mut(&handle1), None);
    }

    #[test]
    fn test_get_key_value_mut_integration() {
        let mut lhm = LinkedHashMap::<u16, String>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a".to_string());
        lhm.put(2, "b".to_string());
        lhm.put(3, "c".to_string());

        // Get handle and test all access methods
        if let Some(handle2) = lhm.entry_handle(&2) {
            // Test key access
            assert_eq!(lhm.get_key(&handle2), Some(&2));
            
            // Test value access
            assert_eq!(lhm.get_value(&handle2), Some(&"b".to_string()));
            
            // Test mutable value access and modification
            if let Some(value) = lhm.get_value_mut(&handle2) {
                value.push_str("_updated");
            }
            
            // Verify modification through immutable access
            assert_eq!(lhm.get_value(&handle2), Some(&"b_updated".to_string()));
            
            // Test handle operations still work after mutations
            assert!(lhm.make_tail(handle2.clone()));
            
            // Verify all access methods still work after repositioning
            assert_eq!(lhm.get_key(&handle2), Some(&2));
            assert_eq!(lhm.get_value(&handle2), Some(&"b_updated".to_string()));
        } else {
            panic!("Expected valid handle for key 2");
        }

        // Verify final state
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 3, 2]); // 2 moved to tail
        
        let values: Vec<_> = lhm.values().cloned().collect();
        assert_eq!(values, vec!["a".to_string(), "c".to_string(), "b_updated".to_string()]);
    }

    #[test]
    fn test_make_head_basic() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Initial order: [1, 2, 3]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3]);

        // Move key 3 to head
        if let Some(handle) = lhm.entry_handle(&3) {
            assert!(lhm.make_head(handle));
        }

        // Order should now be [3, 1, 2]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![3, 1, 2]);

        // Values should remain unchanged
        assert_eq!(lhm.get(&1), Some(&"a"));
        assert_eq!(lhm.get(&2), Some(&"b"));
        assert_eq!(lhm.get(&3), Some(&"c"));
    }

    #[test]
    fn test_make_head_already_at_head() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Move key 1 to head (it's already at head)
        if let Some(handle) = lhm.entry_handle(&1) {
            assert!(lhm.make_head(handle));
        }

        // Order should remain the same: [1, 2, 3]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3]);
    }

    #[test]
    fn test_make_head_access_order() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Initial order: [1, 2, 3]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3]);

        // Move key 2 to head using handle
        if let Some(handle) = lhm.entry_handle(&2) {
            assert!(lhm.make_head(handle));
        }

        // Order should now be [2, 1, 3]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![2, 1, 3]);
    }

    #[test]
    fn test_make_head_invalid_handle() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");

        // Create a default handle (invalid)
        let default_handle = crate::lhmap::entry::EntryHandle::<u16, &str>::default();
        
        // Try to use it - should return false
        assert_eq!(lhm.make_head(default_handle), false);
    }

    #[test]
    fn test_remove_head_basic() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Remove head entries in order
        assert_eq!(lhm.remove_head(), Some((1, "a")));
        assert_eq!(lhm.len(), 2);
        
        assert_eq!(lhm.remove_head(), Some((2, "b")));
        assert_eq!(lhm.len(), 1);
        
        assert_eq!(lhm.remove_head(), Some((3, "c")));
        assert_eq!(lhm.len(), 0);
        
        // Empty map returns None
        assert_eq!(lhm.remove_head(), None);
    }

    #[test]
    fn test_remove_head_access_order() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Access key 2, making it most recently used (moves to tail)
        lhm.get(&2);

        // Order should now be [1, 3, 2]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 3, 2]);

        // Remove head should remove 1 (least recently used)
        assert_eq!(lhm.remove_head(), Some((1, "a")));
        
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![3, 2]);
    }

    #[test]
    fn test_remove_tail_basic() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Remove tail entries in reverse order
        assert_eq!(lhm.remove_tail(), Some((3, "c")));
        assert_eq!(lhm.len(), 2);
        
        assert_eq!(lhm.remove_tail(), Some((2, "b")));
        assert_eq!(lhm.len(), 1);
        
        assert_eq!(lhm.remove_tail(), Some((1, "a")));
        assert_eq!(lhm.len(), 0);
        
        // Empty map returns None
        assert_eq!(lhm.remove_tail(), None);
    }

    #[test]
    fn test_remove_tail_access_order() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Access key 1, making it most recently used (moves to tail)
        lhm.get(&1);

        // Order should now be [2, 3, 1]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![2, 3, 1]);

        // Remove tail should remove 1 (most recently used)
        assert_eq!(lhm.remove_tail(), Some((1, "a")));
        
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![2, 3]);
    }

    #[test]
    fn test_remove_empty_map() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        
        // Both methods should return None for empty map
        assert_eq!(lhm.remove_head(), None);
        assert_eq!(lhm.remove_tail(), None);
    }

    #[test]
    fn test_remove_single_element() {
        // Test remove_head with single element
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        assert_eq!(lhm.remove_head(), Some((1, "a")));
        assert!(lhm.is_empty());

        // Test remove_tail with single element
        let mut lhm2 = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm2.put(1, "a");
        assert_eq!(lhm2.remove_tail(), Some((1, "a")));
        assert!(lhm2.is_empty());
    }

    #[test]
    fn test_make_head_and_tail_integration() {
        let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::InsertionOrder, None);
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");
        lhm.put(4, "d");

        // Initial order: [1, 2, 3, 4]
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3, 4]);

        // Move 3 to head: [3, 1, 2, 4]
        if let Some(handle) = lhm.entry_handle(&3) {
            assert!(lhm.make_head(handle));
        }
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![3, 1, 2, 4]);

        // Move 1 to tail: [3, 2, 4, 1]
        if let Some(handle) = lhm.entry_handle(&1) {
            assert!(lhm.make_tail(handle));
        }
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![3, 2, 4, 1]);

        // Remove head and tail
        assert_eq!(lhm.remove_head(), Some((3, "c")));
        assert_eq!(lhm.remove_tail(), Some((1, "a")));

        // Should have [2, 4] left
        let keys: Vec<_> = lhm.keys().copied().collect();
        assert_eq!(keys, vec![2, 4]);
    }

    #[test]
    fn test_head() {
        let mut lhm: LinkedHashMap<u16, &str> = LinkedHashMap::new(10, Order::InsertionOrder, None);

        // Empty map should return None
        assert_eq!(lhm.head(), None);

        // Add some entries
        lhm.put(1, "a");
        assert_eq!(lhm.head(), Some((&1, &"a")));

        lhm.put(2, "b");
        assert_eq!(lhm.head(), Some((&1, &"a"))); // Head should still be first inserted

        lhm.put(3, "c");
        assert_eq!(lhm.head(), Some((&1, &"a"))); // Head should still be first inserted

        // Remove head and check next becomes head
        assert_eq!(lhm.remove_head(), Some((1, "a")));
        assert_eq!(lhm.head(), Some((&2, &"b")));

        assert_eq!(lhm.remove_head(), Some((2, "b")));
        assert_eq!(lhm.head(), Some((&3, &"c")));

        assert_eq!(lhm.remove_head(), Some((3, "c")));
        assert_eq!(lhm.head(), None);
    }

    #[test]
    fn test_head_access_order() {
        let mut lhm: LinkedHashMap<u16, &str> = LinkedHashMap::new(10, Order::AccessOrder, None);

        // Add entries
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Head should be least recently accessed (first inserted)
        assert_eq!(lhm.head(), Some((&1, &"a")));

        // Access element 1 - it should move to tail, making 2 the new head
        lhm.get(&1);
        assert_eq!(lhm.head(), Some((&2, &"b")));

        // Access element 2 - it should move to tail, making 3 the new head
        lhm.get(&2);
        assert_eq!(lhm.head(), Some((&3, &"c")));
    }

    #[test]
    fn test_tail() {
        let mut lhm: LinkedHashMap<u16, &str> = LinkedHashMap::new(10, Order::InsertionOrder, None);

        // Empty map should return None
        assert_eq!(lhm.tail(), None);

        // Add some entries
        lhm.put(1, "a");
        assert_eq!(lhm.tail(), Some((&1, &"a")));

        lhm.put(2, "b");
        assert_eq!(lhm.tail(), Some((&2, &"b"))); // Tail should be last inserted

        lhm.put(3, "c");
        assert_eq!(lhm.tail(), Some((&3, &"c"))); // Tail should be last inserted

        // Remove tail and check previous becomes tail
        assert_eq!(lhm.remove_tail(), Some((3, "c")));
        assert_eq!(lhm.tail(), Some((&2, &"b")));

        assert_eq!(lhm.remove_tail(), Some((2, "b")));
        assert_eq!(lhm.tail(), Some((&1, &"a")));

        assert_eq!(lhm.remove_tail(), Some((1, "a")));
        assert_eq!(lhm.tail(), None);
    }

    #[test]
    fn test_tail_access_order() {
        let mut lhm: LinkedHashMap<u16, &str> = LinkedHashMap::new(10, Order::AccessOrder, None);

        // Add entries
        lhm.put(1, "a");
        lhm.put(2, "b");
        lhm.put(3, "c");

        // Tail should be most recently accessed (last inserted)
        assert_eq!(lhm.tail(), Some((&3, &"c")));

        // Access element 1 - it should move to tail
        lhm.get(&1);
        assert_eq!(lhm.tail(), Some((&1, &"a")));

        // Access element 2 - it should move to tail
        lhm.get(&2);
        assert_eq!(lhm.tail(), Some((&2, &"b")));
    }
}
