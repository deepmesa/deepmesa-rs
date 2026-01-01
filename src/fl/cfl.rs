// A contiguous free list

use crate::fl::fl_node;
use crate::fl::fn_capacity;
use crate::fl::fn_cid;
use crate::fl::fn_len;
use crate::fl::next_cid;
use crate::fl::FreeList;
use crate::fl::NONE;
use core::ptr;
use std::alloc::{alloc, dealloc, Layout};
use std::mem::MaybeUninit;

fl_node!(CflNode, usize);

unsafe impl<T: Send> Send for ContiguousFreeList<T> {}
unsafe impl<T: Sync> Sync for ContiguousFreeList<T> {}

pub struct ContiguousFreeList<T> {
    nodes: *mut CflNode<T>,
    head: usize,
    capacity: usize,
    len: usize,
    cid: usize,
}

impl<T> FreeList<T> for ContiguousFreeList<T> {
    type FlNode = CflNode<T>;

    fn new(capacity: usize) -> Self {
        if capacity == 0 {
            panic!("capacity cannot be zero");
        }

        let layout = Layout::array::<CflNode<T>>(capacity)
            .expect("ContiguousFreeList: capacity too large, layout overflow");
        let nodes = unsafe { alloc(layout) as *mut CflNode<T> };

        if nodes.is_null() {
            panic!("memory allocation failed!");
        }

        unsafe {
            for i in 0..capacity - 1 {
                //Initialize all the nodes except the last one and
                // link them together
                let node = CflNode {
                    val: MaybeUninit::uninit(),
                    next: i + 1,
                    is_free: true,
                    gen_id: 0,
                };
                ptr::write(nodes.add(i), node);
            }

            //Now initialize the last node
            let node = CflNode {
                val: MaybeUninit::uninit(),
                next: NONE,
                is_free: true,
                gen_id: 0,
            };

            ptr::write(nodes.add(capacity - 1), node);
        }

        Self {
            nodes,
            head: 0,
            capacity,
            len: 0,
            cid: next_cid(),
        }
    }

    fn_capacity!();
    fn_len!();
    fn_cid!();

    fn acquire(&mut self, val: T) -> *mut CflNode<T> {
        if self.head == NONE {
            return ptr::null_mut();
        }

        unsafe {
            let node = &mut *self.nodes.add(self.head);
            self.head = node.next;
            node.val = MaybeUninit::new(val);
            node.is_free = false;
            node.gen_id += 1;
            self.len += 1;

            node
        }
    }

    fn release(&mut self, ptr: *mut CflNode<T>) -> T {
        debug_assert!(!ptr.is_null(), "release called with null pointer");
        debug_assert!(
            {
                let offset = unsafe { ptr.offset_from(self.nodes) };
                offset >= 0 && (offset as usize) < self.capacity
            },
            "pointer out of bounds"
        );
        debug_assert!(unsafe { !(*ptr).is_free }, "double release");

        unsafe {
            let node = &mut *ptr;
            let val = node.val.assume_init_read();

            node.next = self.head;
            node.is_free = true;
            self.head = ptr.offset_from(self.nodes) as usize;
            self.len -= 1;

            val
        }
    }

    fn val_ptr(node: *mut Self::FlNode) -> *mut T {
        unsafe { (*node).val.as_mut_ptr() }
    }
}

impl<T> crate::fl::FlNode for CflNode<T> {
    fn gen_id(&self) -> u32 {
        self.gen_id
    }

    fn is_free(&self) -> bool {
        self.is_free
    }
}

impl<T> Drop for ContiguousFreeList<T> {
    fn drop(&mut self) {
        // Guard that tracks progress and ensures all remaining elements
        // are dropped even if one element's Drop panics
        struct DropGuard<T> {
            nodes: *mut CflNode<T>,
            capacity: usize,
            current: usize,
        }

        impl<T> Drop for DropGuard<T> {
            fn drop(&mut self) {
                unsafe {
                    // Drop remaining acquired elements (starting from current)
                    for i in self.current..self.capacity {
                        let node = &mut *self.nodes.add(i);
                        if !node.is_free {
                            node.val.assume_init_drop();
                        }
                    }
                    // Deallocate the memory
                    let layout = Layout::array::<CflNode<T>>(self.capacity).unwrap();
                    dealloc(self.nodes as *mut u8, layout);
                }
            }
        }

        let mut guard = DropGuard {
            nodes: self.nodes,
            capacity: self.capacity,
            current: 0,
        };

        unsafe {
            for i in 0..self.capacity {
                // Update current BEFORE drop - if drop panics, guard resumes from i+1
                guard.current = i + 1;
                let node = &mut *self.nodes.add(i);
                if !node.is_free {
                    node.val.assume_init_drop();
                }
            }
        }

        // All elements dropped successfully.
        // Set current to capacity so guard only runs dealloc
        guard.current = self.capacity;
    }
}
