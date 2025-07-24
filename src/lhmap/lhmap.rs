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
/// use deepmesa_collections::map::Order;
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
/// use deepmesa_collections::map::Order;
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
/// use deepmesa_collections::map::Entry;
/// pub fn evict<K,V>(len: usize, capacity: usize, e: &Entry<K, V>) -> bool {
///     if len > capacity {
///         return true;
///     }
///     return false;
/// }
///
/// use deepmesa_collections::LinkedHashMap;
/// use deepmesa_collections::map::Order;
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
    /// with the current length, capacity and the last entry in the
    /// linkedlist (most recently inserted or accessed).
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::map::Order;
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
    /// use deepmesa_collections::map::Order;
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
    /// use deepmesa_collections::map::Order;
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
    /// use deepmesa_collections::map::Order;
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
    /// use deepmesa_collections::map::Order;
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
    /// use deepmesa_collections::map::Order;
    ///
    /// let mut lhm = LinkedHashMap::<u16, &str>::new(10, Order::AccessOrder, None);
    /// lhm.insert(1, "a");
    /// assert_eq!(lhm.contains_key(&1), true);
    /// assert_eq!(lhm.contains_key(&2), false);
    /// ```
    pub fn contains_key(&self, key: &K) -> bool {
        return self.map.contains_key(&PtrKey::new(key));
    }

    /// Returns a reference to the value corresponding to the key. If
    /// the Map was created with AccessOrder then the key accessed is
    /// moved to the head of the underlying linked list (least
    /// recently used).
    ///
    /// If the key is not present then this method returns None and
    /// the order is unaffected.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::map::Order;
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
                if !self.ll.make_head(llnode) {
                    panic!("failed to make head!");
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
    /// moved to the head of the underlying linked list (most
    /// recently accessed).
    ///
    /// If the key is not present then this method returns None and
    /// the order is unaffected.
    ///
    /// # Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::map::Order;
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
                if !self.ll.make_head(llnode) {
                    panic!("failed to make head!");
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
    /// moved to the head of the underlying linked list (least
    /// recently used).
    ///
    /// If the key is not present then this method returns None and
    /// the order is unaffected.
    ///
    /// # Examples
    ///
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::map::Order;
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
                if !self.ll.make_head(llnode) {
                    panic!("failed to make head!");
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
    /// use deepmesa_collections::map::Order;
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
    /// use deepmesa_collections::map::Order;
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
    /// The new value inserted is placed at the head of the underlying
    /// linked list (least recently used).
    ///
    /// #Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::map::Order;
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
                    if !self.ll.make_head(llnode) {
                        panic!("failed to make head!");
                    }
                }
            },
            None => {
                let ll_node = self.ll.push_head(Entry::new(k, v));

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
    /// the head of the underlying linked list (least recently used).
    ///
    /// The key is not updated and only the value corresponding to the
    /// key is updated.
    ///
    /// #Examples
    /// ```
    /// use deepmesa_collections::LinkedHashMap;
    /// use deepmesa_collections::map::Order;
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
                let ll_node = self.ll.push_head(Entry::new(k, v));

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
                    if !self.ll.make_head(llnode) {
                        panic!("failed to make head!");
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
    /// use deepmesa_collections::map::Order;
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
    /// use deepmesa_collections::map::Order;
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
    /// use deepmesa_collections::map::Order;
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
    /// use deepmesa_collections::map::Order;

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
    /// use deepmesa_collections::map::Order;
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
            if let Some(entry) = self.ll.tail() {
                if ee_fn(self.len(), self.cap, entry) {
                    match self.ll.pop_tail() {
                        None => panic!("pop tail unexpectedly returned None"),
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
}
