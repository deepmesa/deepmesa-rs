//queue implmentation backed by contiguous memory
extern crate alloc;
use alloc::alloc::alloc_zeroed;
use alloc::alloc::dealloc;
use alloc::alloc::Layout;
use core::ptr;
use std::fmt::Debug;
use std::ops::Index;
use std::ops::IndexMut;
use std::ptr::null_mut;

macro_rules! bounds_check {
    ($self:ident, $idx:ident, $e:expr) => {
        if $idx >= $self.len {
            $e;
        }
    };
}

macro_rules! bounds_check_panic {
    ($self:ident, $idx:ident, $i:literal) => {
        bounds_check!(
            $self,
            $idx,
            panic!("index out of bounds: {}={}, len={}", $i, $idx, $self.len)
        );
    };
    ($self:ident, $idx:ident) => {
        bounds_check!(
            $self,
            $idx,
            panic!("index out of bounds: index={}, len={}", $idx, $self.len)
        );
    };
}

macro_rules! bounds_check_none {
    ($self:ident, $idx:ident) => {
        bounds_check!($self, $idx, return None);
    };
}

macro_rules! len_zero_none {
    ($self:ident) => {
        if $self.len == 0 {
            return None;
        }
    };
}

macro_rules! cdeque {
    () => {
        CircularDeque::new()
    };
    ($($x:literal),+) => {
        CircularDeque::from_slice(&[$($x,)*][..])
    };
}

pub struct CircularDeque<T> {
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
    ($self:ident, $ptr:expr) => {
        if $ptr == $self.p_idxz {
            $ptr = $self.p_idxc;
        } else {
            unsafe {
                $ptr = $ptr.sub(1);
            }
        }
    };
}

macro_rules! inc_ptr {
    ($self:ident, $ptr:expr) => {
        if $ptr == $self.p_idxc {
            $ptr = $self.p_idxz;
        } else {
            unsafe {
                $ptr = $ptr.add(1);
            }
        }
    };
}

macro_rules! inc_head {
    ($self:ident) => {
        inc_ptr!($self, $self.p_head);
    };
}

macro_rules! dec_head {
    ($self:ident) => {
        dec_ptr!($self, $self.p_head);
    };
}

macro_rules! inc_tail {
    ($self:ident) => {
        inc_ptr!($self, $self.p_tail);
    };
}

macro_rules! dec_tail {
    ($self:ident) => {
        dec_ptr!($self, $self.p_tail);
    };
}

impl<T> CircularDeque<T> {
    //    pub fn shrink_to_fit(&mut self) {}
    //    pub fn shrink_to(&mut self, min_capacity: usize) {}
    //    pub fn iter(&self) -> Iter<'_, T> {}
    //    pub fn iter_mut(&mut self) -> IterMut<'_, T> {}
    //    pub fn range<R>(&self, range: R) -> Iter<'_, T>}
    //    pub fn range_mut<R>(&mut self, range: R) -> IterMut<'_, T>}
    //    pub fn drain<R>(&mut self, range: R) -> Drain<'_, T, A>}
    //    pub fn split_off(&mut self, at: usize) -> Self{}
    //    pub fn resize_with(&mut self, new_len: usize, generator: impl FnMut() -> T) {}
    //    pub fn make_contiguous(&mut self) -> &mut [T] {}
    //    pub fn rotate_right(&mut self, n: usize) {}
    //    pub fn partition_point<P>(&self, mut pred: P) -> usize}
    //    pub fn resize(&mut self, new_len: usize, value: T) {}

    pub fn new() -> CircularDeque<T> {
        return CircularDeque {
            len: 0,
            capacity: 0,
            // Pointer to the first item of the allocated capacity
            // (index zero)
            p_idxz: null_mut(),
            // Pointer to the last item of the allocated capacity
            // (index capacity - 1)
            p_idxc: null_mut(),
            // Pointer to the head of the queue
            p_head: null_mut(),
            // Pointer to the tail of the queue
            p_tail: null_mut(),
        };
    }

    pub fn with_capacity(capacity: usize) -> CircularDeque<T> {
        let p_idxz = Self::alloc(capacity);
        unsafe {
            return CircularDeque {
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
            self.grow(0);
        }

        self.push_back_unchecked(val);
    }

    pub fn pop_front(&mut self) -> Option<T> {
        len_zero_none!(self);
        return Some(self.pop_front_unchecked());
    }

    pub fn pop_back(&mut self) -> Option<T> {
        len_zero_none!(self);
        return Some(self.pop_back_unchecked());
    }

    pub fn push_front(&mut self, val: T) {
        if self.len == self.capacity {
            self.grow(0);
        }
        self.push_front_unchecked(val);
    }

    pub fn front(&self) -> Option<&T> {
        len_zero_none!(self);

        unsafe {
            return Some(&(*(self.p_head)));
        }
    }
    pub fn front_mut(&mut self) -> Option<&mut T> {
        len_zero_none!(self);
        unsafe {
            return Some(&mut (*(self.p_head)));
        }
    }

    pub fn back(&self) -> Option<&T> {
        len_zero_none!(self);
        unsafe {
            return Some(&(*(self.p_tail)));
        }
    }

    pub fn back_mut(&mut self) -> Option<&mut T> {
        len_zero_none!(self);
        unsafe {
            return Some(&mut (*(self.p_tail)));
        }
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        bounds_check_none!(self, index);

        let ptr = self.ptr_at(index);
        unsafe {
            return Some(&(*ptr));
        }
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        bounds_check_none!(self, index);
        let ptr = self.ptr_at(index);
        unsafe {
            return Some(&mut (*ptr));
        }
    }

    pub fn swap(&mut self, i: usize, j: usize) {
        bounds_check_panic!(self, i, "i");
        bounds_check_panic!(self, j, "j");

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

    pub fn insert(&mut self, index: usize, value: T) {
        if index > self.len {
            panic!("index out of bounds: index={}, len={}", index, self.len)
        }

        if self.len == self.capacity {
            self.grow(0);
        }

        let ptr = self.ptr_at(index);
        let mut cur = self.p_tail;
        //TODO: Break up this loop into len and back_n
        loop {
            if cur == ptr {
                break;
            }

            let mut prev = cur;
            dec_ptr!(self, prev);
            unsafe {
                let val = ptr::read(prev);
                ptr::write(cur, val);
                cur = prev;
            }
        }
        unsafe {
            ptr::write(ptr, value);
        }
        inc_tail!(self);
        self.len += 1;
    }

    pub fn remove(&mut self, index: usize) -> Option<T> {
        len_zero_none!(self);
        bounds_check_none!(self, index);
        unsafe {
            let ptr = self.ptr_at(index);
            let val = ptr::read(ptr);
            let mut idx: usize = index;
            let mut p_dst = ptr;
            let mut p_src = ptr;
            if index > self.len - index {
                inc_ptr!(self, p_src);
                //move the elements from the tail one back
                loop {
                    if idx >= self.len {
                        break;
                    }
                    self.move_elem(p_src, p_dst);
                    inc_ptr!(self, p_src);
                    inc_ptr!(self, p_dst);
                    idx += 1;
                }

                dec_tail!(self);
            } else {
                dec_ptr!(self, p_src);
                //move the elements from the head one forward
                loop {
                    if idx <= 0 {
                        break;
                    }
                    self.move_elem(p_src, p_dst);
                    dec_ptr!(self, p_src);
                    dec_ptr!(self, p_dst);

                    idx -= 1;
                }

                inc_head!(self);
            }

            self.len -= 1;
            return Some(val);
        }
    }

    pub fn reserve_exact(&mut self, additional: usize) {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return;
        }

        let new_mem = Self::alloc(new_len);
        unsafe {
            self.rebase(new_mem, new_len);
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return;
        }

        self.grow(new_len);
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        let new_len = self.len + additional;
        if self.capacity >= new_len {
            return Ok(());
        }

        match Self::try_alloc(new_len) {
            Ok(p_mem) => {
                unsafe {
                    self.rebase(p_mem, new_len);
                }
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

        let mut new_capacity = 0;
        if self.capacity == 0 {
            new_capacity = 1;
        } else {
            new_capacity = 2 * self.capacity;
        }

        if new_len > new_capacity {
            new_capacity = new_len;
        }

        match Self::try_alloc(new_capacity) {
            Ok(p_mem) => {
                unsafe {
                    self.rebase(p_mem, new_capacity);
                }
                return Ok(());
            }
            Err(e) => {
                return Err(TryReserveError::new(e.code, e.msg));
            }
        }
    }

    pub fn swap_remove_front(&mut self, index: usize) -> Option<T> {
        len_zero_none!(self);
        bounds_check_none!(self, index);

        if index == 0 {
            return self.remove(index);
        }
        unsafe {
            let ptr = self.ptr_at(index);
            let val = ptr::read(ptr);
            self.move_elem(self.p_head, ptr);
            inc_head!(self);
            self.len -= 1;
            return Some(val);
        }
    }

    pub fn swap_remove_back(&mut self, index: usize) -> Option<T> {
        len_zero_none!(self);
        bounds_check_none!(self, index);

        if index == self.len - 1 {
            return self.remove(index);
        }
        unsafe {
            let ptr = self.ptr_at(index);
            let val = ptr::read(ptr);
            let p_last = self.ptr_at(self.len - 1);
            self.move_elem(p_last, ptr);
            dec_tail!(self);
            self.len -= 1;
            return Some(val);
        }
    }

    pub fn clear(&mut self) {
        self.truncate(0);
    }

    pub fn truncate(&mut self, len: usize) {
        if len >= self.len {
            return;
        }

        loop {
            if self.len == len {
                break;
            }

            self.pop_back();
        }
    }

    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        let s_ptrs = self.slice_ptrs();
        unsafe {
            return (&mut *s_ptrs.0, &mut *s_ptrs.1);
        }
    }

    pub fn as_slices(&self) -> (&[T], &[T]) {
        let s_ptrs = self.slice_ptrs();
        unsafe {
            return (&*(s_ptrs.0 as *const [T]), &*(s_ptrs.1 as *const [T]));
        }
    }

    fn slice_ptrs(&self) -> (*mut [T], *mut [T]) {
        unsafe {
            if self.len == 0 {
                return (
                    ptr::slice_from_raw_parts_mut(self.p_head, 0),
                    ptr::slice_from_raw_parts_mut(self.p_idxz, 0),
                );
            }

            let f_len = (self.p_idxc.offset_from(self.p_head) + 1) as usize;
            if f_len >= self.len {
                return (
                    ptr::slice_from_raw_parts_mut(self.p_head, self.len),
                    ptr::slice_from_raw_parts_mut(self.p_idxz, 0),
                );
            } else {
                return (
                    ptr::slice_from_raw_parts_mut(self.p_head, f_len),
                    ptr::slice_from_raw_parts_mut(self.p_idxz, self.len - f_len),
                );
            }
        }
    }

    pub fn append(&mut self, other: &mut CircularDeque<T>) {
        if other.len == 0 {
            return;
        }

        self.reserve(self.len + other.len);

        loop {
            let val = other.remove(0);
            match val {
                None => {
                    return;
                }
                Some(v) => {
                    self.push_back(v);
                }
            }
        }
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.retain_mut(|e| f(e));
    }

    pub fn retain_mut<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        //Index of the current item to examine
        let mut idx_c = 0;
        let mut idx_d = 0;
        let mut d_ct = 0;
        loop {
            if idx_c >= self.len {
                break;
            }

            unsafe {
                let ptr_c = self.ptr_at(idx_c);
                if f(&mut *ptr_c) {
                    if idx_c != idx_d {
                        //move the item from idx_c to idx_d
                        let ptr_d = self.ptr_at(idx_d);
                        let val = ptr::read(ptr_c);
                        ptr::write(ptr_d, val);
                    }
                    idx_d += 1;
                } else {
                    std::ptr::drop_in_place(ptr_c);
                    d_ct += 1;
                }
            }
            idx_c += 1;
        }
        self.p_tail = self.ptr_at(idx_d);
        self.len -= d_ct;
    }
}

impl<T> Index<usize> for CircularDeque<T> {
    type Output = T;

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
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        return self.get_mut(index).unwrap();
    }
}

impl<T: Debug> CircularDeque<T> {
    pub fn rotate_left(&mut self, n: usize) {
        if self.len == 0 || n == self.len || n == 0 {
            return;
        }

        if n > self.len {
            panic!("n={:?} cannot be greater than len = {:?}", n, self.len);
        }

        if self.len == self.capacity {
            self.p_head = self.ptr_at(n);
            self.p_tail = self.p_head;
        } else {
            let len_b = self.len - n;
            if n <= len_b {
                for i in 0..n {
                    let val = self.pop_front_unchecked();
                    self.push_back_unchecked(val);
                }
            } else {
                for i in 0..len_b {
                    let val = self.pop_back_unchecked();
                    self.push_front_unchecked(val);
                }
            }
        }
    }
}

impl<T: Copy> CircularDeque<T> {
    pub fn from_slice(src: &[T]) -> CircularDeque<T> {
        let mut cdq = CircularDeque::with_capacity(src.len());
        for i in 0..src.len() {
            cdq.push_back(src[i]);
        }
        return cdq;
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
impl<T> CircularDeque<T> {
    fn pop_back_unchecked(&mut self) -> T {
        dec_tail!(self);
        let val: T;
        unsafe {
            val = ptr::read(self.p_tail);
        }
        self.len -= 1;
        return val;
    }

    fn push_front_unchecked(&mut self, val: T) {
        dec_head!(self);
        unsafe {
            ptr::write(self.p_head, val);
        }
        self.len += 1;
    }

    fn push_back_unchecked(&mut self, val: T) {
        unsafe {
            ptr::write(self.p_tail, val);
        }

        inc_tail!(self);
        self.len += 1;
    }

    fn pop_front_unchecked(&mut self) -> T {
        let val: T;
        unsafe {
            val = ptr::read(self.p_head);
        }

        inc_head!(self);
        self.len -= 1;
        return val;
    }

    fn grow(&mut self, min_capacity: usize) {
        let mut new_capacity = 0;
        if self.capacity == 0 {
            new_capacity = 1;
        } else {
            new_capacity = 2 * self.capacity;
        }

        if min_capacity > new_capacity {
            new_capacity = min_capacity;
        }

        let new_mem = Self::alloc(new_capacity);
        unsafe {
            self.rebase(new_mem, new_capacity);
        }
    }

    //Move an element from the location p_src to the location
    // p_dst. p_src may or may not be overwritten / changed
    fn move_elem(&mut self, p_src: *mut T, p_dst: *mut T) {
        unsafe {
            let val: T = ptr::read(p_src);
            ptr::write(p_dst, val);
        }
    }

    //Copies the data from the old to the new memory allocated and
    // drops the old memory.
    unsafe fn rebase(&mut self, p_new: *mut T, alloc_size: usize) {
        debug_assert!(self.len <= alloc_size);
        let mut cur: *mut T = self.p_head;
        let mut idx: usize = 0;
        let mut p_dst = p_new;
        loop {
            if idx >= self.len {
                break;
            }
            self.move_elem(cur, p_dst);
            inc_ptr!(self, cur);
            p_dst = p_dst.add(1);
            idx += 1;
        }

        self.capacity = alloc_size;
        let p_old = self.p_idxz;
        self.p_idxz = p_new;
        self.p_idxc = self.p_idxz.add(self.capacity - 1);
        self.p_head = p_new;
        self.p_tail = self.p_head.add(self.len);

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

    // Returns the pointer for the given index (between 0 and len)
    // starting at the head of the deque. If the index is greater than
    // or equal to len then the behavior is undefined
    fn ptr_at(&self, index: usize) -> *mut T {
        unsafe {
            let dist = self.p_idxc.offset_from(self.p_head) as usize;
            if dist < index {
                return self.p_idxz.add(index - dist - 1);
            } else {
                return self.p_head.add(index);
            }
        }
    }
}

impl<T> CircularDeque<T>
where
    T: PartialEq,
{
    pub fn contains(&self, x: &T) -> bool {
        let mut idx: usize = 0;
        loop {
            if idx >= self.len() {
                break;
            }

            unsafe {
                let val = &*self.ptr_at(idx);
                if val.eq(x) {
                    return true;
                }
                idx += 1;
            }
        }
        return false;
    }
}

use std::cmp::PartialEq;

impl<T> Eq for CircularDeque<T> where T: Eq + Debug {}
impl<T> PartialEq<CircularDeque<T>> for CircularDeque<T>
where
    T: PartialEq,
{
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
                    write!(f, "{:?},", val);
                } else if idx == self.len - 1 {
                    write!(f, "{:?}", val);
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

impl<T: Debug> CircularDeque<T> {
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
        println!("len: {:?}", self.len);
        println!("p_head: {:?}", self.p_head);
        println!("p_tail: {:?}", self.p_tail);
        println!("p_idxz: {:?}", self.p_idxz);
        println!("p_idxc: {:?}", self.p_idxc);
    }
}

#[cfg(test)]
mod tests {
    use super::CircularDeque;

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

    #[test]
    fn test_contains() {
        let mut cdq = cdeque!(1, 2, 3);
        assert_eq!(cdq.contains(&9), false);
        assert_eq!(cdq.contains(&1), true);
        assert_eq!(cdq.contains(&2), true);
        assert_eq!(cdq.contains(&3), true);
    }

    #[test]
    fn test_eq() {
        let mut cdq = cdeque!(1, 2, 3);
        assert_eq!(cdq, cdeque!(1, 2, 3));
        assert_ne!(cdq, cdeque!(1, 2, 3, 5));
    }

    #[test]
    fn test_append() {
        let mut cdq = cdeque!(1, 2, 3);
        let mut other = cdeque!(5, 6, 7, 8);
        cdq.append(&mut other);
        assert_eq!(other, cdeque!());
        assert_eq!(cdq, cdeque!(1, 2, 3, 5, 6, 7, 8));

        let mut cdq = cdeque!();
        let mut other = cdeque!(5, 6, 7, 8);
        cdq.append(&mut other);
        assert_eq!(other, cdeque!());
        assert_eq!(cdq, cdeque!(5, 6, 7, 8));
    }

    #[test]
    fn test_remove() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
        assert_ptrs!(cdq);
        assert_eq!(cdq.len(), 10);
        let val = cdq.remove(3);
        assert_eq!(val, Some(4u8));
        assert_eq!(cdq, cdeque!(1, 2, 3, 5, 6, 7, 8, 9, 10));
        for i in 0..10 {
            cdq.remove(1);
        }
        assert_eq!(cdq.len(), 1);
        cdq.remove(0);
        assert_eq!(cdq.len(), 0);
    }

    #[test]
    fn test_swap_remove_back() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);

        let val = cdq.swap_remove_back(4);
        assert_eq!(val, Some(5));
        assert_eq!(cdq, cdeque!(1, 2, 3, 4));

        let val = cdq.swap_remove_back(1);
        assert_eq!(val, Some(2));
        assert_eq!(cdq, cdeque!(1, 4, 3));

        let val = cdq.swap_remove_back(1);
        assert_eq!(val, Some(4));
        assert_eq!(cdq, cdeque!(1, 3));

        let val = cdq.swap_remove_back(0);
        assert_eq!(val, Some(1));
        assert_eq!(cdq, cdeque!(3));

        let val = cdq.swap_remove_back(0);
        assert_eq!(val, Some(3));
        assert_eq!(cdq, cdeque!());
    }

    #[test]
    fn test_swap_remove_front() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        let val = cdq.swap_remove_front(0);
        assert_eq!(val, Some(1));
        assert_eq!(cdq, cdeque!(2, 3, 4, 5));

        let val = cdq.swap_remove_front(2);
        assert_eq!(val, Some(4));
        assert_eq!(cdq, cdeque!(3, 2, 5));

        let val = cdq.swap_remove_front(1);
        assert_eq!(val, Some(2));
        assert_eq!(cdq, cdeque!(3, 5));

        let val = cdq.swap_remove_front(1);
        assert_eq!(val, Some(5));
        assert_eq!(cdq, cdeque!(3));

        let val = cdq.swap_remove_front(0);
        assert_eq!(val, Some(3));
        assert_eq!(cdq, cdeque!());

        let val = cdq.swap_remove_front(10);
        assert_eq!(val, None);
        assert_eq!(cdq, cdeque!());
    }

    // push_back and pop_front
    #[test]
    fn test_back2front() {
        let mut cdq = CircularDeque::<u8>::with_capacity(5);

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
        let mut cdq = CircularDeque::<u8>::with_capacity(5);
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

    // #[test]
    // fn test_grow2() {
    //     let mut cdq = CircularDeque::<u8>::with_capacity(4);
    //     println!("{:?}", &cdq);
    //     cdq.print_mem();

    //     assert_eq!(cdq.capacity, 4);
    //     cdq.grow();
    //     println!("{:?}", &cdq);
    //     cdq.print_mem();
    //     assert_eq!(cdq.capacity, 8);
    //     for i in 0..8 {
    //         cdq.push_back(i);
    //     }
    //     cdq.print_mem();
    // }

    #[test]
    fn test_grow() {
        let mut cdq = CircularDeque::<u8>::new();
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
        let mut cdq = CircularDeque::<u8>::with_capacity(10);
        assert_eq!(cdq.len(), 0);
        assert_eq!(cdq.capacity(), 10);

        cdq.push_front(4);
        cdq.push_front(3);
        cdq.push_front(2);
        cdq.push_front(1);
        cdq.push_back(7);
        cdq.push_back(8);
        cdq.push_back(9);

        //        cdq.print_mem();

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
        let cdq: CircularDeque<u8> = cdeque!(1, 2, 3, 4, 7, 8, 9);
        assert_eq!(cdq.get(6).unwrap(), &9u8);
        assert_eq!(cdq.get(0).unwrap(), &1u8);
        assert_eq!(cdq.get(12), None);
    }

    #[test]
    fn test_insert() {
        let mut cdq: CircularDeque<u8> = cdeque!(1, 2, 3, 4, 7, 8, 9);
        cdq.insert(7, 12);
        assert_eq!(cdq, cdeque!(1, 2, 3, 4, 7, 8, 9, 12));
    }

    #[test]
    fn test_reserve() {
        let mut cdq = cdeque!(1, 2, 3, 4);
        assert_eq!(cdq.len, 4);
        assert_eq!(cdq.capacity, 4);
        cdq.reserve(8);
        assert_eq!(cdq, cdeque!(1, 2, 3, 4));
        assert_eq!(cdq.len, 4);
        assert_eq!(cdq.capacity, 12);
    }

    #[test]
    fn test_reserve_exact() {
        let mut cdq = cdeque!(1, 2, 3, 4);
        assert_eq!(cdq.len, 4);
        assert_eq!(cdq.capacity, 4);
        cdq.reserve_exact(2);
        assert_eq!(cdq, cdeque!(1, 2, 3, 4));
        assert_eq!(cdq.len, 4);
        assert_eq!(cdq.capacity, 6);
    }

    #[test]
    fn test_as_slices() {
        let mut cdq: CircularDeque<u8> = cdeque!();
        assert_eq!(cdq.as_slices(), (&[][..], &[][..]));

        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        let s = cdq.as_slices();
        assert_eq!(cdq.as_slices(), (&[1, 2, 3, 4, 5][..], &[][..]));

        cdq.push_front(9);
        cdq.push_front(8);

        let s = cdq.as_slices();
        assert_eq!(cdq.as_slices(), (&[8, 9][..], &[1, 2, 3, 4, 5][..]));
    }

    #[test]
    fn test_as_mut_slices() {
        let mut cdq: CircularDeque<u8> = cdeque!();
        assert_eq!(cdq.as_mut_slices(), (&mut [][..], &mut [][..]));

        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        let s = cdq.as_mut_slices();
        let front = s.0;
        let back = s.1;

        assert_eq!(front, &[1, 2, 3, 4, 5][..]);
        assert_eq!(back, &[][..]);

        front[2] = 9;
        assert_eq!(front, &[1, 2, 9, 4, 5][..]);
        assert_eq!(back, &[][..]);

        cdq.push_front(19);
        cdq.push_front(18);

        let s = cdq.as_mut_slices();
        let front = s.0;
        let back = s.1;

        assert_eq!(front, &[18, 19][..]);
        assert_eq!(back, &[1, 2, 9, 4, 5][..]);

        front[1] = 11;

        assert_eq!(front, &[18, 11][..]);
        assert_eq!(back, &[1, 2, 9, 4, 5][..]);
    }

    #[test]
    fn test_truncate() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.truncate(3);
        assert_eq!(cdq, cdeque!(1, 2, 3));
        cdq.truncate(1);
        assert_eq!(cdq, cdeque!(1));
        cdq.truncate(0);
        assert_eq!(cdq, cdeque!());
    }

    #[test]
    fn test_clear() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.clear();
        assert_eq!(cdq, cdeque!());
    }

    #[test]
    fn test_retain_mut() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.retain_mut(|x| {
            if *x % 2 == 0 {
                return false;
            } else {
                *x += 3;
                return true;
            }
        });

        assert_eq!(cdq, cdeque!(4, 6, 8));
    }

    #[test]
    fn test_retain() {
        let mut cdq = cdeque!(1, 2, 3, 4, 5);
        cdq.retain(|x| {
            if *x % 2 == 0 {
                return false;
            } else {
                return true;
            }
        });

        assert_eq!(cdq, cdeque!(1, 3, 5));
    }

    #[test]
    fn test_rotate_left() {
        let mut cdq = cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9);
        cdq.rotate_left(3);
        assert_eq!(cdq, cdeque!(3, 4, 5, 6, 7, 8, 9, 0, 1, 2));

        for i in 1..10 {
            assert_eq!(i * 3 % 10, cdq[0]);
            cdq.rotate_left(3);
        }
        assert_eq!(cdq, cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));

        //now test when the deque is not full
        cdq.reserve_exact(20);

        cdq.rotate_left(6);
        assert_eq!(cdq, cdeque!(6, 7, 8, 9, 0, 1, 2, 3, 4, 5));

        for i in 1..10 {
            assert_eq!(i * 6 % 10, cdq[0]);
            cdq.rotate_left(6);
        }
        assert_eq!(cdq, cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));

        cdq.rotate_left(3);
        assert_eq!(cdq, cdeque!(3, 4, 5, 6, 7, 8, 9, 0, 1, 2));

        for i in 1..10 {
            assert_eq!(i * 3 % 10, cdq[0]);
            cdq.rotate_left(3);
        }
        assert_eq!(cdq, cdeque!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9));
    }
}
