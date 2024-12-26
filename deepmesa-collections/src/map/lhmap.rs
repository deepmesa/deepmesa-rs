use crate::linkedlist::list::LinkedList;
use crate::linkedlist::node::Node;
use crate::map::entry::Entry;
use crate::map::entry::Order;
use crate::map::entry::PtrKey;
use core::hash::Hash;
use std::collections::HashMap;

/*
Methods to implement

 * capacity() - DONE
 * clear() - DONE
 * contains_key() - DONE
 * get() - DONE
 * get_key_value() - DONE
 * get_mut() - DONE
 * remove() - DONE
 * len() - DONE
 * new() - DONE
 * insert() - DONE
 * is_empty() - DONE
 * remove_entry() - DONE
 * with_capacity() - DONE

 * drain()?
 * into_keys()
 * into_values()

 * iter()
 * iter_mut()
 * keys()

 * reserve()
 * retain()
 * try_reserve()
 * values()
 * values_mut()

Tests to implement
 * test_insert()
 * test_remove_entry()
 * test_get_key_value
 * test_get_mut()
 * test_len() - DONE
 * test_clear()
 * test_contains_key()
 * test_is_empty()
 */

pub struct LinkedHashMap<K, V>
where
    K: Hash + Eq,
{
    evict_eldest: Option<fn(len: usize, capacity: usize, e: &Entry<K, V>) -> bool>,
    order: Order,
    cap: usize,
    ll: LinkedList<Entry<K, V>>,
    map: HashMap<PtrKey<K>, Node<Entry<K, V>>>,
}

impl<K, V> LinkedHashMap<K, V>
where
    K: Hash + Eq,
{
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

    pub fn with_capacity(capacity: usize) -> LinkedHashMap<K, V> {
        return Self::new(capacity, Order::InsertionOrder, None);
    }

    pub fn capacity(&self) -> usize {
        return self.cap;
    }

    pub fn len(&self) -> usize {
        return self.map.len();
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.ll.clear();
    }

    pub fn is_empty(&self) -> bool {
        return self.map.len() == 0;
    }

    pub fn contains_key(&self, key: &K) -> bool {
        return self.map.contains_key(&PtrKey::new(key));
    }

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

    pub fn remove(&mut self, key: &K) -> Option<V> {
        if let Some(llnode) = self.map.remove(&PtrKey::new(key)) {
            match self.ll.pop_node(&llnode) {
                None => panic!("List doesn't contain expected value!"),
                Some(entry) => return Some(entry.val),
            }
        }

        None
    }

    pub fn remove_entry(&mut self, key: &K) -> Option<(K, V)> {
        if let Some(llnode) = self.map.remove(&PtrKey::new(key)) {
            match self.ll.pop_node(&llnode) {
                None => panic!("List doesn't contain expected value!"),
                Some(entry) => return Some((entry.key, entry.val)),
            }
        }

        None
    }

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

    //Return the old value or None if the key didn't exist
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

    // GOOD VERSION WITH POINTER
    // pub fn put(&mut self, k: K, v: V) {
    //     match self.map.get(&PtrKey(&k as *const K)) {
    //         Some(llnode) => match llnode.val_mut(&mut self.ll) {
    //             None => panic!("Value not found in LL"),
    //             Some(entry) => {
    //                 (*entry).val = v;
    //             }
    //         },
    //         None => {
    //             let ll_node = self.ll.push_head(Entry::new(k, v));
    //             unsafe {
    //                 let entry_ptr = self.ll.as_ptr(&ll_node);
    //                 let v_ptr = (*entry_ptr).key_ptr();
    //                 self.map.insert(PtrKey(v_ptr), ll_node);
    //             }
    //         }
    //     }
    // }

    // OLD PUT Method
    // pub fn put(&mut self, k: K, v: V) {
    //     match self.map.get(&(&k as *const K)) {
    //         None => {
    //             //                let map_key = Arc::new(k);
    //             let new_node = self.ll.push_head(Entry::new(k, v));
    //             unsafe {
    //                 let entry_ptr = self.ll.head_ptr();
    //                 self.map.insert((*entry_ptr).key_ptr(), new_node);
    //             }
    //         }
    //         Some(llnode) => {
    //             match llnode.val_mut(&mut self.ll) {
    //                 None => panic!("value not found in linkedlist"),
    //                 Some(ce) => {
    //                     (*ce).val = v;
    //                 }
    //             };

    //             if !llnode.make_head(&mut self.ll) {
    //                 panic!("failed to make head!");
    //             }
    //         }
    //     }

    //     //        self.evict_eldest();
    // }

    // //Return the old value or None if the key didn't exist
    // pub fn insert(&mut self, k: K, v: V) -> Option<V> {
    //     let mut retval: Option<V> = None;

    //     match self.map.get(&k) {
    //         None => {
    //             let map_key = Arc::new(k);
    //             let new_node = self.ll.push_head(Entry::new(Arc::clone(&map_key), v));
    //             self.map.insert(map_key, new_node);
    //         }
    //         Some(llnode) => {
    //             match llnode.val_mut(&mut self.ll) {
    //                 None => panic!("value not found in linkedlist"),
    //                 Some(ce) => {
    //                     retval = Some(std::mem::replace(&mut (*ce).val, v));
    //                 }
    //             };

    //             if !llnode.make_head(&mut self.ll) {
    //                 panic!("failed to make head!");
    //             }
    //         }
    //     }

    //     self.evict_eldest();
    //     return retval;
    // }

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
    use crate::map::entry::Entry;
    use crate::map::lhmap::LinkedHashMap;

    struct ValObject {
        int_v: u16,
    }

    impl ValObject {
        fn new(val: u16) -> ValObject {
            return ValObject { int_v: val };
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

    fn evict_fn<K, V>(len: usize, capacity: usize, e: &Entry<K, V>) -> bool {
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
}
