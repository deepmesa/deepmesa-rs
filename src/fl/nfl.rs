//A No-op freelist

use crate::fl::fl_node;
use crate::fl::fn_cid;
use crate::fl::next_cid;
use crate::fl::FreeList;
use core::ptr;
use std::alloc::{alloc, dealloc, Layout};
use std::marker::PhantomData;
use std::mem::MaybeUninit;

fl_node!(NflNode, *mut NflNode<T>);

unsafe impl<T: Send> Send for NoOpFreeList<T> {}
unsafe impl<T: Sync> Sync for NoOpFreeList<T> {}

// The NoOpFreeList doesn't actually manage any memory. It simply
// allocates new memory in acquire and deallocates memory in release
// effectively not implementing a freelist at all
pub struct NoOpFreeList<T> {
    cid: usize,
    len: usize,
    next_gen: u32,
    _phantom: PhantomData<T>,
}

impl<T> FreeList<T> for NoOpFreeList<T> {
    type FlNode = NflNode<T>;

    fn new(_capacity: usize) -> Self {
        Self {
            cid: next_cid(),
            len: 0,
            next_gen: 0,
            _phantom: PhantomData,
        }
    }

    fn_cid!();

    fn capacity(&self) -> usize {
        usize::MAX // Unlimited - allocates on demand
    }

    fn len(&self) -> usize {
        self.len
    }

    fn acquire(&mut self, val: T) -> *mut NflNode<T> {
        let layout = Layout::new::<NflNode<T>>();
        let ptr = unsafe { alloc(layout) as *mut NflNode<T> };

        if ptr.is_null() {
            return ptr::null_mut();
        }

        self.next_gen += 1;
        unsafe {
            ptr::write(
                ptr,
                NflNode {
                    val: MaybeUninit::new(val),
                    next: ptr::null_mut(),
                    is_free: false,
                    gen_id: self.next_gen,
                },
            );
        }

        self.len += 1;
        ptr
    }

    fn release(&mut self, ptr: *mut NflNode<T>) -> T {
        debug_assert!(!ptr.is_null(), "release called with null pointer");

        unsafe {
            let node = &mut *ptr;
            let val = node.val.assume_init_read();

            let layout = Layout::new::<NflNode<T>>();
            dealloc(ptr as *mut u8, layout);

            self.len -= 1;
            val
        }
    }

    fn val_ptr(node: *mut Self::FlNode) -> *mut T {
        unsafe { (*node).val.as_mut_ptr() }
    }

    fn node_from_val_ptr(val_ptr: *mut T) -> *mut Self::FlNode {
        let offset = std::mem::offset_of!(NflNode<T>, val);
        unsafe { (val_ptr as *mut u8).sub(offset) as *mut Self::FlNode }
    }
}

impl<T> crate::fl::FlNode for NflNode<T> {
    fn gen_id(&self) -> u32 {
        self.gen_id
    }

    fn is_free(&self) -> bool {
        self.is_free
    }
}
