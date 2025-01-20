//queue implmentation backed by contiguous memory
extern crate alloc;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::dealloc;
use alloc::alloc::Layout;
use core::ptr;
use std::ptr::null_mut;

pub struct ContiguousDeque<T> {
    len: usize,
    capacity: usize,
    p_idxz: *mut T,
    p_idxc: *mut T,
    p_head: *mut T,
    p_tail: *mut T,
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
    ($ptr:expr, $ptr_start: expr, $ptr_end: expr) => {
        if $ptr == $ptr_start {
            $ptr = $ptr_end;
        } else {
            unsafe {
                $ptr = $ptr.sub(1);
            }
        }
    };
}

macro_rules! inc_ptr {
    ($ptr:expr, $p_start: expr, $p_end: expr) => {
        if $ptr == $p_end {
            $ptr = $p_start;
        } else {
            unsafe {
                $ptr = $ptr.add(1);
            }
        }
    };
}

macro_rules! grow_if_full {
    ($len: expr, $cap: expr, $grow: expr) => {
        if $len == $cap {
            $grow;
        }
    };
}

impl<T> ContiguousDeque<T> {
    //    pub fn try_with_capacity(capacity: usize) -> Result<VecDeque<T>, TryReserveError> {}
    //    pub fn with_capacity_in(capacity: usize, alloc: A) -> VecDeque<T, A> {}
    //    pub fn get(&self, index: usize) -> Option<&T> {}
    //    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {}
    //    pub fn swap(&mut self, i: usize, j: usize) {}
    //    pub fn capacity(&self) -> usize {}
    //    pub fn reserve_exact(&mut self, additional: usize) {}
    //    pub fn reserve(&mut self, additional: usize) {}
    //    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {}
    //    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {}
    //    pub fn shrink_to_fit(&mut self) {}
    //    pub fn shrink_to(&mut self, min_capacity: usize) {}
    //    pub fn truncate(&mut self, len: usize) {}
    //    pub fn allocator(&self) -> &A {}
    //    pub fn iter(&self) -> Iter<'_, T> {}
    //    pub fn iter_mut(&mut self) -> IterMut<'_, T> {}
    //    pub fn as_slices(&self) -> (&[T], &[T]) {}
    //    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {}
    //    pub fn len(&self) -> usize {}
    //    pub fn is_empty(&self) -> bool {}
    //    pub fn range<R>(&self, range: R) -> Iter<'_, T>}
    //    pub fn range_mut<R>(&mut self, range: R) -> IterMut<'_, T>}
    //    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, A>}
    //    pub fn clear(&mut self) {}
    //    pub fn contains(&self, x: &T) -> bool}
    //    pub fn front(&self) -> Option<&T> {}
    //    pub fn front_mut(&mut self) -> Option<&mut T> {}
    //    pub fn back(&self) -> Option<&T> {}
    //    pub fn back_mut(&mut self) -> Option<&mut T> {}
    //    pub fn pop_front(&mut self) -> Option<T> {}
    //    pub fn pop_back(&mut self) -> Option<T> {}
    //    pub fn push_front(&mut self, value: T) {}
    //    pub fn push_back(&mut self, value: T) {}
    //    pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {}
    //    pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {}
    //    pub fn insert(&mut self, index: usize, value: T) {}
    //    pub fn remove(&mut self, index: usize) -> Option<T> {}
    //    pub fn split_off(&mut self, at: usize) -> Self}
    //    pub fn append(&mut self, other: &mut Self) {}
    //    pub fn retain<F>(&mut self, mut f: F)}
    //    pub fn retain_mut<F>(&mut self, mut f: F)}
    //    pub fn resize_with(&mut self, new_len: usize, generator: impl FnMut() -> T) {}
    //    pub fn make_contiguous(&mut self) -> &mut [T] {}
    //    pub fn rotate_left(&mut self, n: usize) {}
    //    pub fn rotate_right(&mut self, n: usize) {}
    //    pub fn binary_search(&self, x: &T) -> Result<usize, usize>}
    //    pub fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>}
    //    pub fn binary_search_by_key<'a, B, F>(&'a self, b: &B, mut f: F) -> Result<usize, usize>}
    //    pub fn partition_point<P>(&self, mut pred: P) -> usize}
    //    pub fn resize(&mut self, new_len: usize, value: T) {}

    pub fn new() -> ContiguousDeque<T> {
        return ContiguousDeque {
            len: 0,
            capacity: 0,
            p_idxz: null_mut(),
            p_idxc: null_mut(),
            p_head: null_mut(),
            p_tail: null_mut(),
        };
    }

    pub fn with_capacity(capacity: usize) -> ContiguousDeque<T> {
        let p_idxz = Self::alloc(capacity);
        unsafe {
            return ContiguousDeque {
                len: 0,
                capacity,
                p_idxz,
                p_idxc: p_idxz.add(capacity - 1),
                p_head: p_idxz,
                p_tail: p_idxz,
            };
        }
    }

    pub fn is_empty(&self) -> bool {
        return self.len == 0;
    }

    pub fn is_full(&self) -> bool {
        return self.len == self.capacity;
    }

    pub fn len(&self) -> usize {
        return self.len;
    }

    pub fn capacity(&self) -> usize {
        return self.capacity;
    }

    pub fn push_back(&mut self, val: T) {
        grow_if_full!(self.len, self.capacity, self.grow());
        unsafe {
            ptr::write(self.p_tail, val);
        }

        inc_ptr!(self.p_tail, self.p_idxz, self.p_idxc);
        self.len += 1;
    }

    pub fn pop_front(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        let val: T;
        unsafe {
            val = ptr::read(self.p_head);
        }

        inc_ptr!(self.p_head, self.p_idxz, self.p_idxc);
        self.len -= 1;
        return Some(val);
    }

    pub fn pop_back(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        dec_ptr!(self.p_tail, self.p_idxz, self.p_idxc);
        let val: T;
        unsafe {
            val = ptr::read(self.p_tail);
        }
        self.len -= 1;
        return Some(val);
    }

    pub fn push_front(&mut self, val: T) {
        grow_if_full!(self.len, self.capacity, self.grow());
        dec_ptr!(self.p_head, self.p_idxz, self.p_idxc);
        unsafe {
            ptr::write(self.p_head, val);
        }
        self.len += 1;
    }

    fn grow(&mut self) {
        if self.capacity == 0 {
            let new_mem = Self::alloc(1);
            self.expand(new_mem, 1);
        } else {
            let new_mem = Self::alloc(self.capacity);
            self.expand(new_mem, self.capacity);
        }
    }

    //Copies the data from the old to the new memory allocated and
    // drops the old memory
    fn expand(&mut self, p_new: *mut T, alloc_size: usize) {
        let mut cur: *mut T = self.p_head;
        let mut idx: usize = 0;
        loop {
            if idx >= self.len {
                break;
            }
            unsafe {
                let val: T = ptr::read(cur);
                ptr::write(p_new, val);
            }
            inc_ptr!(cur, self.p_idxz, self.p_idxc);
            idx += 1;
        }

        self.capacity += alloc_size;
        let p_old = self.p_idxz;
        self.p_idxz = p_new;
        unsafe {
            self.p_idxc = self.p_idxz.add(self.capacity - 1);
            self.p_head = p_new;
            self.p_tail = self.p_head.add(self.len);
        }
        Self::dealloc(p_old, self.len);
    }

    fn dealloc(ptr: *mut T, len: usize) {
        //TODO: Remove this unwrap: check that len < isize::MAX
        let layout = Layout::array::<T>(len).unwrap();
        unsafe {
            dealloc(ptr as *mut u8, layout);
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

    //TODO: Remove
    fn print_mem(&self) {
        let mut cur = self.p_idxz;
        for i in 0..self.capacity {
            println!("[{:}]: {:?}", i, cur);
            unsafe {
                cur = cur.add(1);
            }
        }
        println!("p_head: {:?}", self.p_head);
        println!("p_tail: {:?}", self.p_tail);
        println!("p_idxz: {:?}", self.p_idxz);
        println!("p_idxc: {:?}", self.p_idxc);
    }
}

#[cfg(test)]
mod tests {
    use super::ContiguousDeque;

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

    // push_back and pop_front
    #[test]
    fn test_back2front() {
        let mut cdq = ContiguousDeque::<u8>::with_capacity(5);

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
        let mut cdq = ContiguousDeque::<u8>::with_capacity(5);
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
        let mut cdq = ContiguousDeque::<u8>::new();
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
}
