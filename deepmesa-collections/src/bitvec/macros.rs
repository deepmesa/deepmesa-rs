/*
   BitVector: A fast contiguous growable array of bits allocated
   on the heap that allows storing and manipulating an arbitrary
   number of bits. This collection is backed by a Vector<u8> which
   manages the underlying memory.

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

macro_rules! debug_assert_bounds_check {
    ($v: ident, $l: expr) => {
        debug_assert!(
            $v <= $l,
            concat!(stringify!($v), " ({}) ", "exceeds {}"),
            $v,
            $l
        );
    };
}

macro_rules! index_range_fn {
    ($bits:expr, $start: expr, $end:expr, $len:expr) => {
        unsafe {
            let ptr = $bits.as_ptr().add($start / 8);
            let slice: &[u8] =
                core::slice::from_raw_parts(ptr, slice_pack!($end - $start, $start % 8));
            return core::mem::transmute(slice);
        }
    };
}

macro_rules! index_range_mut_fn {
    ($bits:expr, $start: expr, $end:expr) => {
        unsafe {
            let ptr = $bits.as_mut_ptr().add($start / 8);
            let slice: &mut [u8] =
                core::slice::from_raw_parts_mut(ptr, slice_pack!($end - $start, $start % 8));

            return core::mem::transmute(slice);
        }
    };
}

macro_rules! impl_index_range {
    ($for:ty, $self:ident, $bits:tt) => {
        impl Index<Range<usize>> for $for {
            type Output = BitSlice;
            fn index(&self, range: Range<usize>) -> &Self::Output {
                slice_bounds_check!(range.start, range.end, self.len());
                index_range_fn!(self.$bits, range.start, range.end, self.len());
            }
        }

        impl Index<RangeFrom<usize>> for $for {
            type Output = BitSlice;
            fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
                slice_start_bounds_check!(range.start, self.len(), self.len());
                index_range_fn!(self.$bits, range.start, self.len(), self.len());
            }
        }

        impl Index<RangeInclusive<usize>> for $for {
            type Output = BitSlice;
            fn index(&self, range: RangeInclusive<usize>) -> &Self::Output {
                slice_bounds_check!(*range.start(), *range.end() + 1, self.len());
                index_range_fn!(self.$bits, *range.start(), *range.end() + 1, self.len());
            }
        }

        impl Index<RangeToInclusive<usize>> for $for {
            type Output = BitSlice;
            fn index(&self, range: RangeToInclusive<usize>) -> &Self::Output {
                slice_end_bounds_check!(range.end + 1, self.len());
                index_range_fn!(self.$bits, 0, range.end + 1, self.len());
            }
        }

        impl Index<RangeTo<usize>> for $for {
            type Output = BitSlice;
            fn index(&self, range: RangeTo<usize>) -> &Self::Output {
                slice_end_bounds_check!(range.end, self.len());
                index_range_fn!(self.$bits, 0, range.end, self.len());
            }
        }

        impl Index<RangeFull> for $for {
            type Output = BitSlice;
            fn index(&self, _: RangeFull) -> &Self::Output {
                index_range_fn!(self.$bits, 0, self.len(), self.len());
            }
        }
    };
}

macro_rules! impl_index_range_mut {
    ($for:ty, $self:ident, $bits:tt) => {
        impl IndexMut<Range<usize>> for $for {
            fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
                slice_bounds_check!(range.start, range.end, self.len());
                index_range_mut_fn!(self.$bits, range.start, range.end);
            }
        }

        impl IndexMut<RangeFrom<usize>> for $for {
            fn index_mut(&mut self, range: RangeFrom<usize>) -> &mut Self::Output {
                slice_start_bounds_check!(range.start, self.len(), self.len());
                index_range_mut_fn!(self.$bits, range.start, self.len());
            }
        }

        impl IndexMut<RangeTo<usize>> for $for {
            fn index_mut(&mut self, range: RangeTo<usize>) -> &mut Self::Output {
                slice_end_bounds_check!(range.end, self.len());
                index_range_mut_fn!(self.$bits, 0, range.end);
            }
        }

        impl IndexMut<RangeInclusive<usize>> for $for {
            fn index_mut(&mut self, range: RangeInclusive<usize>) -> &mut Self::Output {
                slice_bounds_check!(*range.start(), *range.end() + 1, self.len());
                index_range_mut_fn!(self.$bits, *range.start(), *range.end() + 1);
            }
        }

        impl IndexMut<RangeToInclusive<usize>> for $for {
            fn index_mut(&mut self, range: RangeToInclusive<usize>) -> &mut Self::Output {
                slice_end_bounds_check!(range.end + 1, self.len());
                index_range_mut_fn!(self.$bits, 0, range.end + 1);
            }
        }

        impl IndexMut<RangeFull> for $for {
            fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
                index_range_mut_fn!(self.$bits, 0, self.len());
            }
        }
    };
}

macro_rules! start_bounds_check {
    ($start: expr, $len:expr) => {
        if $start >= $len {
            panic!("start index {} out of range for length {}", $start, $len);
        }
    };
}

macro_rules! slice_start_bounds_check {
    ($start: expr, $end: expr, $len:expr) => {
        if $start >= $len {
            panic!("start index {} out of range for length {}", $start, $len);
        }
        if $start > $end {
            panic!(
                "slice range start index {} out of range for end at {}",
                $start, $end
            );
        }
    };
}

macro_rules! slice_end_bounds_check {
    ($end: expr, $len: expr) => {
        if $end > $len {
            panic!("end index {} out of range for length {}", $end, $len);
        }
    };
}

macro_rules! slice_bounds_check {
    ($start:expr, $end: expr, $len: expr) => {
        slice_start_bounds_check!($start, $end, $len);
        slice_end_bounds_check!($end, $len);
    };
}

macro_rules! slice_offset_bits {
    () => {
        3
    };
}

macro_rules! slice_pack {
    ($len: expr, $offset: expr) => {
        bitops::msb_set_usize($len, $offset, slice_offset_bits!())
    };
}

macro_rules! slice_unpack_len {
    ($val: expr) => {
        bitops::clr_msb_usize($val, slice_offset_bits!())
    };
}

macro_rules! slice_unpack_offset {
    ($val: expr) => {
        bitops::msbn_usize($val, slice_offset_bits!())
    };
}

macro_rules! try_from_bitslice {
    ($i:ident, $b: literal) => {
        impl TryFrom<&BitSlice> for $i {
            type Error = String;
            fn try_from(bitslice: &BitSlice) -> Result<Self, Self::Error> {
                let len = bitslice.len();
                if len > $b {
                    return Err(format!(
                        concat!(
                            "slice of len {} bits is too big to fit into a ",
                            stringify!($i)
                        ),
                        len
                    ));
                }
                let offset = bitslice.offset();
                Ok(bytes::read_bits(&bitslice.0, offset, len + offset, $b, BitOrder::Lsb0).0 as $i)
            }
        }
    };
}

macro_rules! b_expr {
    ($e: expr) => {
        $e
    };
}

macro_rules! bit_at_unchecked {
    ($index:expr, $bits: expr) => {
        bitops::is_msb_nset($bits[$index / 8], ($index % 8) as u8);
    };
}

macro_rules! set_unchecked {
    ($index: expr, $value: expr, $bits: expr) => {
        if $value {
            bitops::set_msb_n(&mut $bits[$index / 8], ($index % 8) as u8);
        } else {
            $bits[$index / 8].clear_msb_nth_assign(($index % 8) as u8);
        }
    };
}

macro_rules! flip_bits {
    ($b:expr, IterOnes) => {};
    ($b:ident, last_one) => {};
    ($b:ident, first_one) => {};
    ($b:ident, count_ones) => {};
    ($b:ident, first_zero) => {
        $b = !$b
    };
    ($b:ident, last_zero) => {
        $b = !$b
    };
    ($b:ident, count_zeros) => {
        $b = !$b
    };
    ($b:expr, IterZeros) => {
        $b = !$b
    };
}
