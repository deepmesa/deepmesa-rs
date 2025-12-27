//A Segmented FreeList

use crate::fl::fn_capacity;
use crate::fl::fn_cid;
use crate::fl::fn_len;
use crate::fl::next_cid;
use crate::fl::FreeList;
use crate::fl::NONE;
use core::ptr;
use std::alloc::{alloc, dealloc, realloc, Layout};
use std::mem::MaybeUninit;

pub(crate) struct SflNode<T> {
    pub(crate) val: MaybeUninit<T>,
    pub(crate) next: usize,
    // The global index of this node across all segments, as if they were
    // one contiguous array. Stored in the node for O(1) release.
    pub(crate) idx: usize,
    pub(crate) is_free: bool,
    pub(crate) gen_id: u32,
}

const SEGMENT_SIZE: usize = 256;

const _: () = assert!(
    SEGMENT_SIZE.is_power_of_two(),
    "SEGMENT_SIZE must be a power of 2"
);

// Bit shift for fast division: idx >> SEGMENT_SHIFT = idx / SEGMENT_SIZE
const SEGMENT_SHIFT: u32 = SEGMENT_SIZE.trailing_zeros();

// Bit mask for fast modulo: idx & SEGMENT_MASK = idx % SEGMENT_SIZE
const SEGMENT_MASK: usize = SEGMENT_SIZE - 1;

// Segmented freelist
pub struct SegmentedFreeList<T> {
    segments: *mut *mut SflNode<T>,
    segment_count: usize,
    capacity: usize, // total nodes (rounded up to segment boundary)
    head: usize,     // global index of free list head
    len: usize,
    cid: usize,
    next_gen: u32,
}

impl<T> FreeList<T> for SegmentedFreeList<T> {
    type FlNode = SflNode<T>;

    fn new(capacity: usize) -> Self {
        if capacity == 0 {
            panic!("capacity cannot be zero");
        }

        // Round up capacity to next multiple of SEGMENT_SIZE
        // e.g., capacity=500, SEGMENT_SIZE=256 -> actual_capacity=512
        let segment_count = (capacity + SEGMENT_SIZE - 1) >> SEGMENT_SHIFT;
        let actual_capacity = segment_count << SEGMENT_SHIFT;

        // Allocate the segment pointer array
        let segments_layout = Layout::array::<*mut SflNode<T>>(segment_count)
            .expect("SegmentedFreeList: segment array layout overflow");
        let segments = unsafe { alloc(segments_layout) as *mut *mut SflNode<T> };

        if segments.is_null() {
            panic!("segment pointer array allocation failed");
        }

        // Allocate each segment and initialize nodes
        let segment_layout = Layout::array::<SflNode<T>>(SEGMENT_SIZE)
            .expect("SegmentedFreeList: segment layout overflow");

        for seg_idx in 0..segment_count {
            let segment = unsafe { alloc(segment_layout) as *mut SflNode<T> };

            if segment.is_null() {
                // Cleanup already allocated segments
                for i in 0..seg_idx {
                    unsafe {
                        dealloc(*segments.add(i) as *mut u8, segment_layout);
                    }
                }
                unsafe {
                    dealloc(segments as *mut u8, segments_layout);
                }
                panic!("segment allocation failed");
            }

            // Store segment pointer
            unsafe {
                *segments.add(seg_idx) = segment;
            }

            // Initialize all nodes in this segment and link them together
            unsafe {
                for local_idx in 0..SEGMENT_SIZE {
                    let global_idx = (seg_idx << SEGMENT_SHIFT) | local_idx;
                    let is_last_node =
                        seg_idx == segment_count - 1 && local_idx == SEGMENT_SIZE - 1;
                    let next_idx = if is_last_node { NONE } else { global_idx + 1 };

                    ptr::write(
                        segment.add(local_idx),
                        SflNode {
                            val: MaybeUninit::uninit(),
                            next: next_idx,
                            idx: global_idx,
                            is_free: true,
                            gen_id: 0,
                        },
                    );
                }
            }
        }

        Self {
            segments,
            segment_count,
            capacity: actual_capacity,
            head: 0,
            len: 0,
            cid: next_cid(),
            next_gen: 0,
        }
    }

    fn acquire(&mut self, val: T) -> *mut SflNode<T> {
        if self.head == NONE {
            self.grow();
        }

        unsafe {
            // Translate global index to segment + local index
            let seg_idx = self.head >> SEGMENT_SHIFT;
            let local_idx = self.head & SEGMENT_MASK;

            // Get pointer to the node
            let segment = *self.segments.add(seg_idx);
            let node = &mut *segment.add(local_idx);

            // Update head to next free node
            self.head = node.next;

            // Initialize the node
            node.val = MaybeUninit::new(val);
            node.is_free = false;
            node.gen_id += 1;
            self.len += 1;

            node
        }
    }
    fn release(&mut self, ptr: *mut SflNode<T>) -> T {
        debug_assert!(!ptr.is_null(), "release called with null pointer");
        debug_assert!(unsafe { !(*ptr).is_free }, "double release");

        unsafe {
            let node = &mut *ptr;
            let val = node.val.assume_init_read();

            node.next = self.head;
            node.is_free = true;
            self.head = node.idx;
            self.len -= 1;

            val
        }
    }
    fn_capacity!();
    fn_len!();
    fn_cid!();
}

impl<T> SegmentedFreeList<T> {
    fn grow(&mut self) {
        let new_segment_count = self.segment_count + 1;

        // Reallocate the segment pointer array
        let old_segments_layout = Layout::array::<*mut SflNode<T>>(self.segment_count)
            .expect("SegmentedFreeList: old segment array layout overflow");
        let new_segments_layout = Layout::array::<*mut SflNode<T>>(new_segment_count)
            .expect("SegmentedFreeList: new segment array layout overflow");

        let new_segments = unsafe {
            realloc(
                self.segments as *mut u8,
                old_segments_layout,
                new_segments_layout.size(),
            ) as *mut *mut SflNode<T>
        };

        if new_segments.is_null() {
            panic!("segment pointer array reallocation failed");
        }

        self.segments = new_segments;

        // Allocate the new segment
        let segment_layout = Layout::array::<SflNode<T>>(SEGMENT_SIZE)
            .expect("SegmentedFreeList: segment layout overflow");
        let new_segment = unsafe { alloc(segment_layout) as *mut SflNode<T> };

        if new_segment.is_null() {
            panic!("segment allocation failed");
        }

        // Store the new segment pointer
        unsafe {
            *self.segments.add(self.segment_count) = new_segment;
        }

        // Initialize all nodes in the new segment and link them together
        let new_seg_idx = self.segment_count;
        unsafe {
            for local_idx in 0..SEGMENT_SIZE {
                let global_idx = (new_seg_idx << SEGMENT_SHIFT) | local_idx;
                let is_last_node = local_idx == SEGMENT_SIZE - 1;
                let next_idx = if is_last_node { NONE } else { global_idx + 1 };

                ptr::write(
                    new_segment.add(local_idx),
                    SflNode {
                        val: MaybeUninit::uninit(),
                        next: next_idx,
                        idx: global_idx,
                        is_free: true,
                        gen_id: 0,
                    },
                );
            }
        }

        // Update head to point to the first node of the new segment
        self.head = new_seg_idx << SEGMENT_SHIFT;

        // Update counts
        self.segment_count = new_segment_count;
        self.capacity += SEGMENT_SIZE;
    }
}
