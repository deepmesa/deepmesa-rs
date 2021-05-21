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

use crate::bitvec::{bitops, bitslice::BitSlice, bitvec::BitVector, BitCount};

macro_rules! iter_unsigned {
    ($iter_name: ident, $i:ident, $b: literal) => {
        pub struct $iter_name<'a> {
            bits: &'a [u8],
            cursor: usize,
            bit_len: usize,
            slice_offset: usize,
        }

        impl<'a> $iter_name<'a> {
            pub(super) fn new(
                bits: &'a [u8],
                slice_offset: usize,
                bit_len: usize,
            ) -> $iter_name<'a> {
                $iter_name {
                    bits,
                    cursor: 0,
                    bit_len,
                    slice_offset,
                }
            }
        }

        impl<'a> Iterator for $iter_name<'a> {
            type Item = ($i, BitCount);
            fn next(&mut self) -> Option<Self::Item> {
                if self.cursor >= self.bit_len {
                    return None;
                }

                let offset = self.slice_offset;
                let len = self.bit_len + offset;
                let st_index = self.cursor + offset;

                let (val, bit_count) = BitSlice::read_bits_lsb0(&self.bits, st_index, len, $b);
                self.cursor += bit_count;
                Some((val as $i, bit_count))
            }
        }
    };
}

iter_unsigned!(IterU8, u8, 8);
iter_unsigned!(IterU16, u16, 16);
iter_unsigned!(IterU32, u32, 32);
iter_unsigned!(IterU64, u64, 64);
iter_unsigned!(IterU128, u128, 128);

pub struct Iter<'a> {
    bits: &'a [u8],
    cursor: usize,
    bit_len: usize,
    slice_offset: usize,
}

impl<'a> Iter<'a> {
    pub(super) fn new(bits: &'a [u8], slice_offset: usize, bit_len: usize) -> Iter<'a> {
        Iter {
            bits,
            cursor: 0,
            bit_len,
            slice_offset,
        }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = bool;
    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor >= self.bit_len {
            return None;
        }

        let index = self.cursor + self.slice_offset;
        self.cursor += 1;
        get_unchecked!(index, self.bits);
    }
}

impl<'a> IntoIterator for &'a BitSlice {
    type Item = bool;
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a BitVector {
    type Item = bool;
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use crate::bitvec::bitvec::BitVector;

    #[test]
    fn test_iter_slice() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1100_1010, None);

        let slice = &bv[2..6];
        let mut iter = slice.iter();
        assert_eq!(&iter.next(), &Some(false));
        assert_eq!(&iter.next(), &Some(false));
        assert_eq!(&iter.next(), &Some(true));
        assert_eq!(&iter.next(), &Some(false));
        assert_eq!(&iter.next(), &None);

        let mut i = 0;
        for v in slice {
            assert_eq!(v, slice.get(i).unwrap());
            i += 1;
        }
    }

    #[test]
    fn test_iter_bitvec() {
        let mut bv = BitVector::with_capacity(128);
        bv.push(false);
        bv.push(true);
        bv.push(false);
        bv.push(false);

        let mut iter = bv.iter();
        assert_eq!(&iter.next(), &Some(false));
        assert_eq!(&iter.next(), &Some(true));
        assert_eq!(&iter.next(), &Some(false));
        assert_eq!(&iter.next(), &Some(false));
        assert_eq!(&iter.next(), &None);

        let mut i = 0;
        for v in &bv {
            assert_eq!(v, bv.get(i).unwrap());
            i += 1;
        }
    }

    #[test]
    fn test_iter_u16_bitvec() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1100_1010_0011_0101, None);
        bv.push_u16(0b1000_1100_0011_1111, None);
        bv.push_u8(0b0000_0011, None);
        assert_eq!(bv.len(), 34);
        let mut iter = bv.iter_u16();
        assert_eq!(iter.next(), Some((0b1100_1010_0011_0101, 16)));
        assert_eq!(iter.next(), Some((0b1000_1100_0011_1111, 16)));
        assert_eq!(iter.next(), Some((0b0000_0000_0000_0011, 2)));
        assert_eq!(&iter.next(), &None);
    }
}
