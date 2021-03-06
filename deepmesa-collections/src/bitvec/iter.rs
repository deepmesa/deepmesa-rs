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

use crate::bitvec::{
    bitops, bitref::BitRefMut, bitslice::BitSlice, bitvec::BitVector, bytes,
    traits::BitwiseClearAssign, BitCount, BitOrder,
};

macro_rules! iter_unsigned {
    (
        $(#[$outer:meta])*
        $iter_name: ident, $i:ident, $max_bits: literal
    ) => {
        $(#[$outer])*
        #[derive(Debug)]
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

                let (val, bit_count) =
                    bytes::read_bits(&self.bits, st_index, len, $max_bits, BitOrder::Lsb0);
                self.cursor += bit_count;
                Some((val as $i, bit_count))
            }
        }
    };
}

iter_unsigned!(
    /// An iterator that iterates over the bits of the
    /// [`BitVector`](../struct.BitVector.html) 8 bits at a time.
    ///
    /// This struct is created by the
    /// [`.iter_u8()`](BitVector#method.iter_u8)
    /// method of [`BitVector`](../struct.BitVector.html) and
    /// [`BitSlice`](BitSlice)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// use deepmesa::collections::bitvec::IterU8;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u16(0b0101_1101_0011_1010, Some(16));
    ///
    /// let mut iter: IterU8 = bv.iter_u8();
    /// assert_eq!(iter.next(), Some((0b0101_1101, 8)));
    /// assert_eq!(iter.next(), Some((0b0011_1010, 8)));
    /// assert_eq!(iter.next(), None);
    /// ```
    IterU8,
    u8,
    8
);
iter_unsigned!(
    /// An iterator that iterates over the bits of the
    /// [`BitVector`](../struct.BitVector.html) 16 bits at a time.
    ///
    /// This struct is created by the
    /// [`.iter_u16()`](BitVector#method.iter_u16)
    /// method of [`BitVector`](../struct.BitVector.html) and
    /// [`BitSlice`](BitSlice)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// use deepmesa::collections::bitvec::IterU16;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u16(0b0101_1101_0011_1010, Some(16));
    ///
    /// let mut iter:IterU16 = bv.iter_u16();
    /// assert_eq!(iter.next(), Some((0b0101_1101_0011_1010, 16)));
    /// assert_eq!(iter.next(), None);
    /// ```
    IterU16,
    u16,
    16
);
iter_unsigned!(
    /// An iterator that iterates over the bits of the
    /// [`BitVector`](../struct.BitVector.html) 32 bits at a time.
    ///
    /// This struct is created by the
    /// [`.iter_u32()`](BitVector#method.iter_u32)
    /// method of [`BitVector`](../struct.BitVector.html) and
    /// [`BitSlice`](BitSlice)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// use deepmesa::collections::bitvec::IterU32;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u16(0b0101_1101_0011_1010, Some(16));
    /// bv.push_u16(0b1111_0011_1100_0000, Some(16));
    ///
    /// let mut iter:IterU32 = bv.iter_u32();
    /// assert_eq!(iter.next(), Some((0b0101_1101_0011_1010_1111_0011_1100_0000, 32)));
    /// assert_eq!(iter.next(), None);
    /// ```
    IterU32,
    u32,
    32
);
iter_unsigned!(
    /// An iterator that iterates over the bits of the
    /// [`BitVector`](../struct.BitVector.html) 64 bits at a time.
    ///
    /// This struct is created by the
    /// [`.iter_u64()`](BitVector#method.iter_u64)
    /// method of [`BitVector`](../struct.BitVector.html) and
    /// [`BitSlice`](BitSlice)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// use deepmesa::collections::bitvec::IterU64;
    /// let mut bv = BitVector::new();
    /// bv.push_u64(u64::MAX, Some(64));
    ///
    /// let mut iter:IterU64 = bv.iter_u64();
    /// assert_eq!(iter.next(), Some((u64::MAX, 64)));
    /// assert_eq!(iter.next(), None);
    /// ```
    IterU64,
    u64,
    64
);
iter_unsigned!(
    /// An iterator that iterates over the bits of the
    /// [`BitVector`](../struct.BitVector.html) 128 bits at a time.
    ///
    /// This struct is created by the
    /// [`.iter_u128()`](BitVector#method.iter_u128)
    /// method of [`BitVector`](../struct.BitVector.html) and
    /// [`BitSlice`](BitSlice)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// use deepmesa::collections::bitvec::IterU128;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u64(u64::MAX, Some(64));
    /// bv.push_u64(u64::MAX, Some(64));
    ///
    /// let mut iter = bv.iter_u128();
    /// assert_eq!(iter.next(), Some((u128::MAX, 128)));
    /// assert_eq!(iter.next(), None);
    /// ```
    IterU128,
    u128,
    128
);

/// An immutable iterator over the bits of the
/// [`BitVector`](../struct.BitVector.html) or [`BitSlice`](BitSlice).
///
/// This struct is created by the [`.iter()`](BitVector#method.iter)
/// method of [`BitVector`](../struct.BitVector.html) and
/// [`BitSlice`](BitSlice)
///
/// # Examples
/// ```
/// use deepmesa::collections::BitVector;
/// use deepmesa::collections::bitvec::Iter;
///
/// let mut bv = BitVector::new();
/// bv.push_u8(0b101, None);
///
/// let mut iter:Iter = bv.iter();
/// assert_eq!(iter.next(), Some(true));
/// assert_eq!(iter.next(), Some(false));
/// assert_eq!(iter.next(), Some(true));
/// assert_eq!(iter.next(), None);
/// ```
#[derive(Debug)]
pub struct Iter<'a> {
    bits: &'a [u8],
    cursor: usize,
    bit_len: usize,
    slice_offset: usize,
}

/// A mutable iterator over the bits of the
/// [`BitVector`](../struct.BitVector.html) or [`BitSlice`](BitSlice).
///
/// This struct is created by the
/// [`.iter_mut()`](BitVector#method.iter_mut) method of
/// [`BitVector`](../struct.BitVector.html) and [`BitSlice`](BitSlice)
///
/// # Examples
/// ```
/// use deepmesa::collections::BitVector;
/// use deepmesa::collections::bitvec::IterMut;
///
/// let mut bv = BitVector::with_capacity(20);
/// bv.push_u8(0b1011_1100, Some(8));
/// bv.push_u8(0b0011_1001, Some(8));
/// let iter: IterMut = bv.iter_mut();
/// for mut bit in iter {
///     *bit = true;
/// }
/// assert_eq!(bv.read_u16(0), (0b1111_1111_1111_1111, 16));
/// ```
#[derive(Debug)]
pub struct IterMut<'a> {
    bits: &'a mut [u8],
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

impl<'a> IterMut<'a> {
    pub(super) fn new(bits: &'a mut [u8], slice_offset: usize, bit_len: usize) -> IterMut<'a> {
        IterMut {
            bits,
            cursor: 0,
            bit_len,
            slice_offset,
        }
    }
}

macro_rules! iter_bits {
    (
        $(#[$outer:meta])*
        $iter_name: ident
    ) => {
        $(#[$outer])*
        #[derive(Debug)]
        pub struct $iter_name<'a> {
            bits: &'a [u8],
            cur_byte: u8,
            byte_idx: usize,
            slice_offset: usize,
            bit_len: usize,
            eb_idx: usize,
            sb_idx: usize,
            l_bit: usize,
        }

        impl<'a> $iter_name<'a> {
            pub(super) fn new(
                bits: &'a [u8],
                slice_offset: usize,
                bit_len: usize,
            ) -> $iter_name<'a> {
                let byte_idx = slice_offset / 8;
                let eb_idx;
                #[allow(unused_mut)]
                let mut cur_byte: u8;
                let l_bit = slice_offset + bit_len;
                if bit_len == 0 {
                    eb_idx = 0;
                    cur_byte = 0;
                } else {
                    eb_idx = (l_bit - 1) / 8;
                    cur_byte = bits[byte_idx];
                    flip_bits!(cur_byte, $iter_name);
                };
                let sb_idx = byte_idx;

                $iter_name {
                    bits,
                    slice_offset,
                    bit_len,
                    byte_idx,
                    cur_byte,
                    eb_idx,
                    sb_idx,
                    l_bit,
                }
            }
        }
        impl<'a> Iterator for $iter_name<'a> {
            type Item = usize;
            fn next(&mut self) -> Option<Self::Item> {
                if self.byte_idx == self.sb_idx {
                    self.cur_byte
                        .clear_msb_assign((self.slice_offset % 8) as u8);
                }

                if self.cur_byte == 0 {
                    self.byte_idx += 1;
                    if self.byte_idx > self.eb_idx {
                        return None;
                    }
                    self.cur_byte = self.bits[self.byte_idx];
                    flip_bits!(self.cur_byte, $iter_name);
                }

                let bit_idx = self.cur_byte.leading_zeros() as usize;
                let idx = bit_idx + (self.byte_idx * 8);
                if idx >= self.l_bit {
                    return None;
                }
                self.cur_byte.clear_msb_assign((bit_idx + 1) as u8);

                return Some(idx - self.slice_offset);
            }
        }
    };
}

iter_bits!(
    /// An iterator that iterates over the `1` bits of the
    /// [`BitVector`](../struct.BitVector.html).
    ///
    /// This struct is created by the
    /// [`.iter_ones()`](BitVector#method.iter_ones)
    /// method of [`BitVector`](../struct.BitVector.html) and
    /// [`BitSlice`](BitSlice)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// use deepmesa::collections::bitvec::IterOnes;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0010_0101, Some(8));
    ///
    /// let mut iter:IterOnes = bv.iter_ones();
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(5));
    /// assert_eq!(iter.next(), Some(7));
    /// assert_eq!(iter.next(), None);
    /// ```
    IterOnes
);

iter_bits!(
    /// An iterator that iterates over the `0` bits of the
    /// [`BitVector`](../struct.BitVector.html).
    ///
    /// This struct is created by the
    /// [`.iter_zeros()`](BitVector#method.iter_zeros)
    /// method of [`BitVector`](../struct.BitVector.html) and
    /// [`BitSlice`](BitSlice)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// use deepmesa::collections::bitvec::IterZeros;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1101_1010, Some(8));
    ///
    /// let mut iter:IterZeros = bv.iter_zeros();
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(5));
    /// assert_eq!(iter.next(), Some(7));
    /// assert_eq!(iter.next(), None);
    /// ```
    IterZeros
);

impl<'a> Iterator for Iter<'a> {
    type Item = bool;
    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor >= self.bit_len {
            return None;
        }

        let index = self.cursor + self.slice_offset;
        self.cursor += 1;
        return Some(bit_at_unchecked!(index, self.bits));
    }
}

impl<'a> Iterator for IterMut<'a> {
    type Item = BitRefMut<'a, bool>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor >= self.bit_len {
            return None;
        }

        let slice_index = self.cursor / 8;
        let byte_ptr = self.bits[slice_index..slice_index].as_mut_ptr();
        let index = self.cursor + self.slice_offset;

        unsafe {
            let byte = *byte_ptr;
            let bit = bitops::is_msb_nset(byte, (index % 8) as u8);

            self.cursor += 1;
            return Some(BitRefMut::<bool>::new(bit, byte_ptr, index));
        }
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
    use super::*;
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

    #[test]
    fn test_iter_ones() {
        let mut bv = BitVector::with_capacity(128);
        let mut iter = IterOnes::new(&bv.bits, 0, bv.len());
        assert_eq!(iter.next(), None);

        bv.push_u16(0b1100_1010_0011_0101, None);
        bv.push_u16(0b1000_1100_0011_1111, None);

        let mut iter = IterOnes::new(&bv.bits, 0, bv.len());
        assert_eq!(iter.next(), Some(0));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(6));
        assert_eq!(iter.next(), Some(10));
        assert_eq!(iter.next(), Some(11));
        assert_eq!(iter.next(), Some(13));
        assert_eq!(iter.next(), Some(15));
        assert_eq!(iter.next(), Some(16));
        assert_eq!(iter.next(), Some(20));
        assert_eq!(iter.next(), Some(21));
        assert_eq!(iter.next(), Some(26));
        assert_eq!(iter.next(), Some(27));
        assert_eq!(iter.next(), Some(28));
        assert_eq!(iter.next(), Some(29));
        assert_eq!(iter.next(), Some(30));
        assert_eq!(iter.next(), Some(31));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_zeros() {
        let mut bv = BitVector::with_capacity(128);
        let mut iter = IterZeros::new(&bv.bits, 0, bv.len());
        assert_eq!(iter.next(), None);

        bv.push_u16(0b0011_0101_1100_1010, Some(16));
        bv.push_u16(0b0111_0011_1100_0000, Some(16));
        let mut iter = IterZeros::new(&bv.bits, 0, bv.len());
        assert_eq!(iter.next(), Some(0));
        assert_eq!(iter.next(), Some(1));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(6));
        assert_eq!(iter.next(), Some(10));
        assert_eq!(iter.next(), Some(11));
        assert_eq!(iter.next(), Some(13));
        assert_eq!(iter.next(), Some(15));
        assert_eq!(iter.next(), Some(16));
        assert_eq!(iter.next(), Some(20));
        assert_eq!(iter.next(), Some(21));
        assert_eq!(iter.next(), Some(26));
        assert_eq!(iter.next(), Some(27));
        assert_eq!(iter.next(), Some(28));
        assert_eq!(iter.next(), Some(29));
        assert_eq!(iter.next(), Some(30));
        assert_eq!(iter.next(), Some(31));
        assert_eq!(iter.next(), None);
    }
}
