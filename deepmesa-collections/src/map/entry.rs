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

#[derive(Debug, PartialEq, Eq)]
pub enum Order {
    AccessOrder,
    InsertionOrder,
}
