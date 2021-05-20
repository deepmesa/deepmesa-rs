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

macro_rules! impl_index_range {
    ($for:ty, $self:ident) => {
        impl Index<Range<usize>> for $for {
            type Output = BitSlice;
            fn index(&self, range: Range<usize>) -> &Self::Output {
                $self::index_range(self, range.start, range.end)
            }
        }

        impl Index<RangeFrom<usize>> for $for {
            type Output = BitSlice;
            fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
                $self::index_range(self, range.start, self.len())
            }
        }

        impl Index<RangeInclusive<usize>> for $for {
            type Output = BitSlice;
            fn index(&self, range: RangeInclusive<usize>) -> &Self::Output {
                $self::index_range(self, *range.start(), *range.end() + 1)
            }
        }

        impl Index<RangeToInclusive<usize>> for $for {
            type Output = BitSlice;
            fn index(&self, range: RangeToInclusive<usize>) -> &Self::Output {
                $self::index_range(self, 0, range.end + 1)
            }
        }

        impl Index<RangeTo<usize>> for $for {
            type Output = BitSlice;
            fn index(&self, range: RangeTo<usize>) -> &Self::Output {
                $self::index_range(self, 0, range.end)
            }
        }

        impl Index<RangeFull> for $for {
            type Output = BitSlice;
            fn index(&self, _: RangeFull) -> &Self::Output {
                $self::index_range(self, 0, self.len())
            }
        }
    };
}

macro_rules! impl_index_range_mut {
    ($for:ty, $self:ident) => {
        //TOO2
        impl IndexMut<Range<usize>> for $for {
            fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
                $self::index_range_mut(self, range.start, range.end)
            }
        }

        impl IndexMut<RangeFrom<usize>> for $for {
            fn index_mut(&mut self, range: RangeFrom<usize>) -> &mut Self::Output {
                $self::index_range_mut(self, range.start, self.len())
            }
        }

        impl IndexMut<RangeTo<usize>> for $for {
            fn index_mut(&mut self, range: RangeTo<usize>) -> &mut Self::Output {
                $self::index_range_mut(self, 0, range.end)
            }
        }

        impl IndexMut<RangeInclusive<usize>> for $for {
            fn index_mut(&mut self, range: RangeInclusive<usize>) -> &mut Self::Output {
                $self::index_range_mut(self, *range.start(), *range.end() + 1)
            }
        }

        impl IndexMut<RangeToInclusive<usize>> for $for {
            fn index_mut(&mut self, range: RangeToInclusive<usize>) -> &mut Self::Output {
                $self::index_range_mut(self, 0, range.end + 1)
            }
        }

        impl IndexMut<RangeFull> for $for {
            fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
                $self::index_range_mut(self, 0, self.len())
            }
        }
    };
}

macro_rules! index_range_fn {
    ($b:tt) => {
        pub(super) fn index_range(&self, start: usize, end: usize) -> &BitSlice {
            BitSlice::check_bounds(start, end, self.len());
            unsafe {
                let ptr = self.$b.as_ptr().add(start / 8);
                let slice: &[u8] =
                    core::slice::from_raw_parts(ptr, BitSlice::pack(end - start, start % 8));
                core::mem::transmute(slice)
            }
        }
    };
}

macro_rules! index_range_mut_fn {
    ($b:tt) => {
        pub(super) fn index_range_mut(&mut self, start: usize, end: usize) -> &mut BitSlice {
            BitSlice::check_bounds(start, end, self.len());
            unsafe {
                let ptr = self.$b.as_mut_ptr().add(start / 8);
                let slice: &mut [u8] =
                    core::slice::from_raw_parts_mut(ptr, BitSlice::pack(end - start, start % 8));

                core::mem::transmute(slice)
            }
        }
    };
}

macro_rules! try_from_bitslice {
    ($i:ident, $b: literal) => {
        impl TryFrom<&BitSlice> for $i {
            type Error = String;
            fn try_from(bitslice: &BitSlice) -> Result<Self, Self::Error> {
                let len = bitslice.len();
                if len > $b {
                    return Err(format!("len {} bits is too big to fit into a $i", len));
                }
                let offset = bitslice.offset();
                Ok(BitSlice::read_bits_lsb0(&bitslice.0, offset, len + offset, $b).0 as $i)
            }
        }
    };
}

macro_rules! b_expr {
    ($e: expr) => {
        $e
    };
}
