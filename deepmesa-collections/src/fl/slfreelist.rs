//A Singly LinkedFreeList

extern crate alloc;

macro_rules! fl_struct {
    ($fl_name: ident, $node: ident) => {
        pub(super) struct $fl_name<T> {
            capacity: usize,
            len: usize,
            head: *mut $node<T>,
        }
    };
}

macro_rules! fl_impl {
    ($fl_name: ident, $node:ident, $p_next:ident, $val:ident) => {
        impl<T> $fl_name<T> {
            pub(super) fn new(capacity: usize) -> $fl_name<T> {
                let mut fl = $fl_name {
                    capacity,
                    len: 0,
                    head: core::ptr::null_mut(),
                };
                fl.alloc(capacity);
                return fl;
            }

            fn alloc(&mut self, size: usize) {
                extern crate alloc;
                let layout = alloc::alloc::Layout::new::<$node<T>>();

                let mut count: usize = 0;
                unsafe {
                    while count < size {
                        let ptr: *mut $node<T> = alloc::alloc::alloc(layout) as *mut $node<T>;
                        if ptr.is_null() {
                            panic!("memory allocation failed!");
                        }
                        self.push_head(ptr);
                        count += 1;
                    }
                }
            }

            fn push_head(&mut self, ptr: *mut $node<T>) {
                unsafe {
                    //TODO Find another way to set these to null
                    //                    (*ptr).left = core::ptr::null_mut();
                    if self.head.is_null() {
                        (*ptr).$p_next = core::ptr::null_mut();
                    } else {
                        (*ptr).$p_next = self.head;
                    }
                    self.len += 1;
                    self.head = ptr;
                }
            }

            fn pop_head(&mut self) -> *mut $node<T> {
                if self.head.is_null() {
                    return core::ptr::null_mut();
                }

                unsafe {
                    let ptr: *mut $node<T> = self.head;
                    self.head = (*ptr).$p_next;
                    (*ptr).$p_next = core::ptr::null_mut();
                    self.len -= 1;
                    ptr
                }
            }

            pub(super) fn release(&mut self, ptr: *mut $node<T>) -> T {
                unsafe {
                    let node = core::ptr::read(ptr);
                    self.push_head(ptr);
                    node.$val
                }
            }

            pub(super) fn acquire(&mut self, val: T, nid: usize) -> *mut $node<T> {
                let mut ptr = self.pop_head();
                if ptr.is_null() {
                    self.grow();
                    ptr = self.pop_head();
                    if ptr.is_null() {
                        panic!("alloc failed on acquire");
                    }
                }
                let node = $node::new(val, nid);
                unsafe {
                    core::ptr::write(ptr, node);
                }
                return ptr;
            }

            fn grow(&mut self) {
                if self.capacity == 0 {
                    self.alloc(1);
                } else {
                    self.alloc(self.capacity);
                    self.capacity *= 2;
                }
            }
        }
    };
}

pub(crate) use fl_impl;
pub(crate) use fl_struct;
