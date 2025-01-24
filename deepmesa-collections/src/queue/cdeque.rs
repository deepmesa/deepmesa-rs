//queue implmentation backed by contiguous memory
extern crate alloc;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::dealloc;
use alloc::alloc::Layout;
use core::ptr;
use std::fmt::Debug;
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
    ($ptr:expr, $p_start: expr, $p_end: expr) => {
        if $ptr == $p_start {
            $ptr = $p_end;
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

impl<T> ContiguousDeque<T> {
    //    pub fn shrink_to_fit(&mut self) {}
    //    pub fn shrink_to(&mut self, min_capacity: usize) {}
    //    pub fn truncate(&mut self, len: usize) {}
    //    pub fn iter(&self) -> Iter<'_, T> {}
    //    pub fn iter_mut(&mut self) -> IterMut<'_, T> {}
    //    pub fn as_slices(&self) -> (&[T], &[T]) {}
    //    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {}
    //    pub fn range<R>(&self, range: R) -> Iter<'_, T>}
    //    pub fn range_mut<R>(&mut self, range: R) -> IterMut<'_, T>}
    //    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, A>}
    //    pub fn clear(&mut self) {}
    //    pub fn contains(&self, x: &T) -> bool}
    //    pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {}
    //    pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {}
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
        if self.len == self.capacity {
            self.grow();
        }

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
        if self.len == self.capacity {
            self.grow();
        }

        dec_ptr!(self.p_head, self.p_idxz, self.p_idxc);
        unsafe {
            ptr::write(self.p_head, val);
        }
        self.len += 1;
    }

    pub fn front(&self) -> Option<&T> {
        if self.len == 0 {
            return None;
        }

        unsafe {
            return Some(&(*(self.p_head)));
        }
    }
    pub fn front_mut(&mut self) -> Option<&mut T> {
        if self.len == 0 {
            return None;
        }

        unsafe {
            return Some(&mut (*(self.p_head)));
        }
    }

    pub fn back(&self) -> Option<&T> {
        if self.len == 0 {
            return None;
        }

        unsafe {
            return Some(&(*(self.p_tail)));
        }
    }

    pub fn back_mut(&mut self) -> Option<&mut T> {
        if self.len == 0 {
            return None;
        }

        unsafe {
            return Some(&mut (*(self.p_tail)));
        }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }

        let ptr = self.ptr_at(index);
        unsafe {
            return Some(&(*ptr));
        }
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= self.len {
            return None;
        }

        let ptr = self.ptr_at(index);
        unsafe {
            return Some(&mut (*ptr));
        }
    }

    pub fn swap(&mut self, i: usize, j: usize) {
        if i >= self.len {
            panic!("index out of bounds: i={}, len={}", i, self.len);
        }

        if j >= self.len {
            panic!("index out of bounds: j={}, len={}", j, self.len);
        }

        let ptr_i = self.ptr_at(i);
        let ptr_j = self.ptr_at(j);

        if ptr_i == ptr_j {
            return;
        }

        unsafe {
            let val_i = ptr::read(ptr_i);
            let val_j = ptr::read(ptr_j);

            ptr::write(ptr_i, val_j);
            ptr::write(ptr_j, val_i);
        }
    }

    pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {
        if index > self.len {
            return None;
        }

        let ptr = self.ptr_at(index);
        unsafe {
            let val = ptr::read(ptr);
            let front = ptr::read(self.p_head);
            ptr::write(ptr, front);
            return Some(val);
        }
    }

    pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
        if index > self.len {
            return None;
        }

        let ptr = self.ptr_at(index);
        unsafe {
            let val = ptr::read(ptr);
            let back = ptr::read(self.p_tail);
            ptr::write(ptr, back);
            return Some(val);
        }
    }

    pub fn insert(&mut self, index: usize, value: T) {
        if index > self.len {
            //            println!("Index {:?} is >= len {:?}", index, self.len);
            panic!("index out of bounds: index={}, len={}", index, self.len);
        }
        let ptr = self.ptr_at(index);

        if self.len == self.capacity {
            self.grow();
        }

        let mut cur = self.p_tail;
        loop {
            if cur == ptr {
                break;
            }

            let mut prev = cur;
            dec_ptr!(prev, self.p_idxz, self.p_idxc);
            unsafe {
                let val = ptr::read(prev);
                ptr::write(cur, val);
                cur = prev;
            }
        }
        unsafe {
            ptr::write(ptr, value);
        }
        inc_ptr!(self.p_tail, self.p_idxz, self.p_idxc);
    }

    pub fn remove(&mut self, index: usize) -> Option<T> {
        if self.len == 0 {
            return None;
        }

        if index > self.len {
            //            println!("Index {:?} is >= len {:?}", index, self.len);
            panic!("index out of bounds: index={}, len={}", index, self.len);
        }

        unsafe {
            let ptr = self.ptr_at(index);
            let val = ptr::read(ptr);
            //index, head = 0, tail = len-1
            //left_len = index
            //right_len = len - index;
            if index > self.len - index {
                //move the elements from the tail one back
            } else {
                //move the elements from the head one forward
            }

            return Some(val);
        }
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return;
        }

        let alloc_size = new_len - self.capacity;
        let new_mem = Self::alloc(alloc_size);
        self.rebase(new_mem, alloc_size);
    }

    pub fn reserve(&mut self, additional: usize) {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return;
        }

        self.grow();
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return Ok(());
        }

        let alloc_size = new_len - self.capacity;
        match Self::try_alloc(alloc_size) {
            Ok(p_mem) => {
                self.rebase(p_mem, alloc_size);
                return Ok(());
            }
            Err(e) => {
                return Err(TryReserveError::new(e.code, e.msg));
            }
        }
    }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return Ok(());
        }

        if self.capacity == 0 {
            match Self::try_alloc(1) {
                Ok(p_mem) => {
                    self.rebase(p_mem, 1);
                    return Ok(());
                }
                Err(e) => {
                    return Err(TryReserveError::new(e.code, e.msg));
                }
            }
        } else {
            match Self::try_alloc(self.capacity) {
                Ok(p_mem) => {
                    self.rebase(p_mem, self.capacity);
                    return Ok(());
                }
                Err(e) => {
                    return Err(TryReserveError::new(e.code, e.msg));
                }
            }
        }
    }
}

pub enum ErrorCode {
    AllocError,
    MemLayoutError,
    CapacityOverflow,
}

pub struct TryReserveError {
    pub code: ErrorCode,
    pub msg: String,
}

impl TryReserveError {
    pub(crate) fn new(code: ErrorCode, msg: String) -> TryReserveError {
        return TryReserveError { code, msg };
    }
}

pub struct TryAllocError {
    code: ErrorCode,
    msg: String,
}

impl TryAllocError {
    pub(crate) fn new(code: ErrorCode, msg: String) -> TryAllocError {
        return TryAllocError { code, msg };
    }
}

//Private methods
impl<T> ContiguousDeque<T> {
    fn grow(&mut self) {
        if self.capacity == 0 {
            let new_mem = Self::alloc(1);
            self.rebase(new_mem, 1);
        } else {
            let new_mem = Self::alloc(self.capacity);
            self.rebase(new_mem, self.capacity);
        }
    }

    //Copies the data from the old to the new memory allocated and
    // drops the old memory.
    fn rebase(&mut self, p_new: *mut T, alloc_size: usize) {
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

    fn try_alloc(len: usize) -> Result<*mut T, TryAllocError> {
        unsafe {
            match Layout::array::<T>(len) {
                Ok(layout) => {
                    let arr = alloc_zeroed(layout) as *mut T;
                    if arr.is_null() {
                        return Err(TryAllocError::new(
                            ErrorCode::AllocError,
                            "Memory Allocation Failed".to_string(),
                        ));
                    }
                    return Ok(arr);
                }
                Err(_) => {
                    return Err(TryAllocError::new(
                        ErrorCode::CapacityOverflow,
                        "Memory Allocation Failed: Capacity Overflow".to_string(),
                    ));
                }
            }
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

    //if index is out of bounds then the behavior is undefined
    fn ptr_at(&self, index: usize) -> *mut T {
        // if index >= self.len {
        //     //            println!("Index {:?} is >= len {:?}", index, self.len);
        //     return null_mut();
        // }

        //        println!("Index {:?}, len {:?}", index, self.len);
        unsafe {
            let dist = self.p_idxc.offset_from(self.p_head) as usize;
            // println!(
            //     "Dist from Head: {:?} to p_cap: {:?} = {:?}",
            //     self.p_head, self.p_idxc, dist
            // );

            if dist < index {
                //                println!("dist: {:?} is < index: {:?}", dist, index);
                //                let diff = index - dist;
                //                println!("Diff = {:?}", diff);
                //                println!("Dist < index. index: {}, dist {}", index, dist);
                return self.p_idxz.add(index - dist - 1);
            //                println!("Target = {:?} val: {:?}", target, *target);
            } else if dist == index {
                //     println!("dist: {:?} is = index: {:?}", dist, index);
                return self.p_head.add(index);
                //     let target = self.p_head.add(index);
                //     println!("Target = {:?} val: {:?}", target, *target);
            } else {
                //dist > index
                //                println!("dist: {:?} is > index: {:?}", dist, index);
                return self.p_head.add(index);
                //                println!("Target = {:?} val: {:?}", target, *target);
            }
        }

        // let mut ptr = self.p_head;

        // //TODO: inc_ptr doesn't work. Need to use offset_from()
        // inc_ptr!(ptr, self.p_idxz, self.p_idxc);

        // unsafe {
        //     return Some(&*ptr);
        // }
    }
}

impl<T: Debug> ContiguousDeque<T> {
    // pub fn get(&self, index: usize) -> Option<&T> {
    //     if index >= self.len {
    //         println!("Index {:?} is >= len {:?}", index, self.len);
    //         return None;
    //     }

    //     println!("Index {:?}, len {:?}", index, self.len);
    //     unsafe {
    //         let dist = self.p_idxc.offset_from(self.p_head) as usize;
    //         println!(
    //             "Dist from Head: {:?} to p_cap: {:?} = {:?}",
    //             self.p_head, self.p_idxc, dist
    //         );

    //         if dist < index {
    //             println!("dist: {:?} is < index: {:?}", dist, index);
    //             let diff = index - dist;
    //             println!("Diff = {:?}", diff);
    //             let target = self.p_idxz.add(diff - 1);
    //             println!("Target = {:?} val: {:?}", target, *target);
    //         } else if dist == index {
    //             println!("dist: {:?} is = index: {:?}", dist, index);
    //             let target = self.p_head.add(index);
    //             println!("Target = {:?} val: {:?}", target, *target);
    //         } else {
    //             //dist > index
    //             println!("dist: {:?} is > index: {:?}", dist, index);
    //             let target = self.p_head.add(index);
    //             println!("Target = {:?} val: {:?}", target, *target);
    //         }
    //     }

    //     let mut ptr = self.p_head;

    //     //TODO: inc_ptr doesn't work. Need to use offset_from()
    //     inc_ptr!(ptr, self.p_idxz, self.p_idxc);

    //     unsafe {
    //         return Some(&*ptr);
    //     }
    // }

    //TODO: Remove
    fn print_mem(&self) {
        let mut cur = self.p_idxz;
        for i in 0..self.capacity {
            unsafe {
                let mut s = String::with_capacity(32);
                if cur == self.p_head {
                    s.push_str(&format!(" p_head [{}]", i));
                }
                if cur == self.p_tail {
                    s.push_str(&format!(" p_tail [{}]", i));
                }
                if cur == self.p_idxz {
                    s.push_str(&format!(" p_idxz [{}]", i));
                }
                if cur == self.p_idxc {
                    s.push_str(&format!(" p_idxc [{}]", i));
                }

                println!("[{:}]: {:?} = {:?} <-- {:}", i, cur, *cur, s);
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

    #[test]
    fn test_swap() {
        let mut cdq = ContiguousDeque::<u8>::with_capacity(10);
        assert_eq!(cdq.len(), 0);
        assert_eq!(cdq.capacity(), 10);

        cdq.push_front(4);
        cdq.push_front(3);
        cdq.push_front(2);
        cdq.push_front(1);
        cdq.push_back(7);
        cdq.push_back(8);
        cdq.push_back(9);

        cdq.print_mem();

        let val2 = cdq.get(2);
        assert_eq!(val2, Some(&3));
        let val5 = cdq.get(5);
        assert_eq!(val5, Some(&8));

        cdq.swap(2, 5);
        let val2 = cdq.get(2);
        assert_eq!(val2, Some(&8));
        let val5 = cdq.get(5);
        assert_eq!(val5, Some(&3));
    }

    #[test]
    fn test_get() {
        let mut cdq = ContiguousDeque::<u8>::with_capacity(10);
        assert_eq!(cdq.len(), 0);
        assert_eq!(cdq.capacity(), 10);
        cdq.push_front(4);
        cdq.push_front(3);
        cdq.push_front(2);
        cdq.push_front(1);
        cdq.push_back(7);
        cdq.push_back(8);
        cdq.push_back(9);

        cdq.print_mem();
        match cdq.get(6) {
            None => {
                println!("NOT FOUND!");
            }
            Some(v) => {
                println!("Val: {:?}", v);
            }
        }
    }

    #[test]
    fn test_get2() {
        let mut cdq = ContiguousDeque::<u8>::with_capacity(10);
        assert_eq!(cdq.len(), 0);
        assert_eq!(cdq.capacity(), 10);
        cdq.push_back(1);
        cdq.push_back(2);
        cdq.push_back(3);
        cdq.push_back(4);
        cdq.push_back(7);
        cdq.push_back(8);
        cdq.push_back(9);
        cdq.pop_front();
        cdq.pop_front();

        cdq.print_mem();
        match cdq.get(0) {
            None => {
                println!("NOT FOUND!");
            }
            Some(v) => {
                println!("Val: {:?}", v);
            }
        }
    }

    #[test]
    fn test_insert() {
        let mut cdq = ContiguousDeque::<u8>::with_capacity(10);
        assert_eq!(cdq.len(), 0);
        assert_eq!(cdq.capacity(), 10);
        cdq.push_front(4);
        cdq.push_front(3);
        cdq.push_front(2);
        cdq.push_front(1);
        cdq.push_back(7);
        cdq.push_back(8);
        cdq.push_back(9);
        cdq.print_mem();
        cdq.insert(7, 12);
        cdq.print_mem();
    }

    #[test]
    fn test_reserve() {
        assert!(false);
    }

    #[test]
    fn test_reserve_exact() {
        assert!(false);
    }
}
