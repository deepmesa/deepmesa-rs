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
use crate::map::entry::Entry;
use crate::map::lhmap::LinkedHashMap;
use core::hash::Hash;

pub struct Iter<'a, K, V> {
    ll_iter: crate::linkedlist::iter::Iter<'a, Entry<K, V>>,
}

impl<'a, K, V> Iter<'a, K, V>
where
    K: Hash + Eq,
{
    pub(crate) fn new(lhmap: &'a LinkedHashMap<K, V>) -> Iter<K, V> {
        Iter {
            ll_iter: lhmap.ll.iter().reverse(),
        }
    }

    pub fn reverse(self) -> Iter<'a, K, V> {
        return Iter {
            ll_iter: self.ll_iter.reverse(),
        };
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        match self.ll_iter.next() {
            Some(entry) => return Some((&entry.key, &entry.val)),
            None => {
                return None;
            }
        }
    }
}

pub struct IterMut<'a, K, V> {
    ll_iter: crate::linkedlist::iter::IterMut<'a, Entry<K, V>>,
}

impl<'a, K, V> IterMut<'a, K, V>
where
    K: Hash + Eq,
{
    pub(crate) fn new(lhmap: &'a mut LinkedHashMap<K, V>) -> IterMut<K, V> {
        IterMut {
            ll_iter: lhmap.ll.iter_mut().reverse(),
        }
    }

    pub fn reverse(self) -> IterMut<'a, K, V> {
        return IterMut {
            ll_iter: self.ll_iter.reverse(),
        };
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        match self.ll_iter.next() {
            Some(entry) => return Some((&entry.key, &mut entry.val)),
            None => {
                return None;
            }
        }
    }
}

pub struct Keys<'a, K, V> {
    ll_iter: crate::linkedlist::iter::Iter<'a, Entry<K, V>>,
}

impl<'a, K, V> Keys<'a, K, V>
where
    K: Hash + Eq,
{
    pub(crate) fn new(lhmap: &'a LinkedHashMap<K, V>) -> Keys<'a, K, V> {
        Keys {
            ll_iter: lhmap.ll.iter().reverse(),
        }
    }

    pub fn reverse(self) -> Keys<'a, K, V> {
        return Keys {
            ll_iter: self.ll_iter.reverse(),
        };
    }
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;
    fn next(&mut self) -> Option<&'a K> {
        match self.ll_iter.next() {
            Some(entry) => return Some(&entry.key),
            None => {
                return None;
            }
        }
    }
}

pub struct Values<'a, K, V> {
    ll_iter: crate::linkedlist::iter::Iter<'a, Entry<K, V>>,
}

impl<'a, K, V> Values<'a, K, V>
where
    K: Hash + Eq,
{
    pub(crate) fn new(lhmap: &'a LinkedHashMap<K, V>) -> Values<'a, K, V> {
        Values {
            ll_iter: lhmap.ll.iter().reverse(),
        }
    }

    pub fn reverse(self) -> Values<'a, K, V> {
        return Values {
            ll_iter: self.ll_iter.reverse(),
        };
    }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<&'a V> {
        match self.ll_iter.next() {
            Some(entry) => return Some(&entry.val),
            None => {
                return None;
            }
        }
    }
}

//
pub struct ValuesMut<'a, K, V> {
    ll_iter: crate::linkedlist::iter::IterMut<'a, Entry<K, V>>,
}

impl<'a, K, V> ValuesMut<'a, K, V>
where
    K: Hash + Eq,
{
    pub(crate) fn new(lhmap: &'a mut LinkedHashMap<K, V>) -> ValuesMut<'a, K, V> {
        ValuesMut {
            ll_iter: lhmap.ll.iter_mut().reverse(),
        }
    }

    pub fn reverse(self) -> ValuesMut<'a, K, V> {
        return ValuesMut {
            ll_iter: self.ll_iter.reverse(),
        };
    }
}

impl<'a, K, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;
    fn next(&mut self) -> Option<&'a mut V> {
        match self.ll_iter.next() {
            Some(entry) => return Some(&mut entry.val),
            None => {
                return None;
            }
        }
    }
}
