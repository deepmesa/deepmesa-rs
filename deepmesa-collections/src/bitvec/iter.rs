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
    bitops, bitslice::BitRef, bitslice::BitSlice, bitvec::BitVector, BitCount, BitOrder,
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
                    BitSlice::read_bits(&self.bits, st_index, len, $max_bits, BitOrder::Lsb0);
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

impl<'a> Iterator for IterMut<'a> {
    type Item = BitRef<'a, bool>;
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
            return Some(BitRef::<bool>::new(bit, byte_ptr, index));
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
