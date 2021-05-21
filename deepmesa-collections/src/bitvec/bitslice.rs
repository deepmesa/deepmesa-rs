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
    bitops,
    iter::{Iter, IterU128, IterU16, IterU32, IterU64, IterU8},
    traits::{
        BitwiseClear, BitwiseClearAssign, BitwiseLsbAssign, BitwiseMsbAssign, BitwisePartialAssign,
        NotLsbAssign, NotMsbAssign, NotPartialAssign,
    },
    BitCount, BitOrderConvert,
};
use core::convert::TryFrom;
use core::fmt;
use core::fmt::Debug;
use core::ops::BitAndAssign;
use core::ops::BitOrAssign;
use core::ops::BitXorAssign;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ops::Index;
use core::ops::IndexMut;
use core::ops::Not;
use core::ops::Range;
use core::ops::RangeFrom;
use core::ops::RangeFull;
use core::ops::RangeInclusive;
use core::ops::RangeTo;
use core::ops::RangeToInclusive;

#[repr(transparent)]
pub struct BitSlice([u8]);

impl Debug for BitSlice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let offset = self.offset();
        write!(
            f,
            "BitSlice {{ bit_len: {}, offset: {}, bits:\n",
            self.len(),
            offset,
        )?;

        let len = self.len();
        write!(f, "{{")?;
        if len > 0 {
            let sb_idx = 0;
            let eb_idx = (len - 1) / 8;
            let mut count = 0;
            for i in sb_idx..=eb_idx {
                if count % 4 == 0 {
                    write!(f, "\n    ")?;
                }

                write!(f, "{:08b} ", self.0[i])?;
                count += 1;
            }
        }
        write!(f, "\n}}}}")?;
        Ok(())
    }
}

macro_rules! iter_unsigned {
    ($iter_fn: ident, $iter_type: ident) => {
        pub fn $iter_fn(&self) -> $iter_type {
            $iter_type::new(&self.0, self.offset(), self.len())
        }
    };
}

macro_rules! read_unsigned {
    ($i:ident, $b: literal, $read_fn: ident) => {
        pub fn $read_fn(&self, start: usize) -> ($i, BitCount) {
            let len = self.len();
            start_bounds_check!(start, len);

            let offset = self.offset();
            let (val, bit_count) =
                BitSlice::read_bits_lsb0(&self.0, start + offset, len + offset, $b);
            (val as $i, bit_count)
        }
    };
}

macro_rules! read_bits_unsigned {
    ($i:ident, $b: literal, $read_bits_fn: ident) => {
        pub fn $read_bits_fn(&self, start: usize, max_bits: BitCount) -> ($i, BitCount) {
            let len = self.len();
            start_bounds_check!(start, len);

            if max_bits > $b {
                panic!(
                    "cannot read more than $b bits into a $i. max_bits={}",
                    max_bits
                );
            }
            let offset = self.offset();
            let (val, bit_count) =
                BitSlice::read_bits_lsb0(&self.0, start + offset, len + offset, max_bits);
            (val as $i, bit_count)
        }
    };
}

macro_rules! as_unsigned {
    ($i:ident, $b: literal, $as_fn: ident) => {
        pub fn $as_fn(&self) -> ($i, BitCount) {
            let len = self.len();
            if len > $b {
                panic!("len {} bits is too big to fit into a $i", len);
            }
            let offset = self.offset();
            let (val, count) = BitSlice::read_bits_lsb0(&self.0, offset, len + offset, $b);
            (val as $i, count)
        }
    };
}

try_from_bitslice!(u8, 8);
try_from_bitslice!(u16, 16);
try_from_bitslice!(u32, 32);
try_from_bitslice!(u64, 64);
try_from_bitslice!(u128, 128);

pub struct BitPtr<'a> {
    bit: bool,
    bits: &'a mut [u8],
    mut_bit: bool,
    index: usize,
}

impl<'a> BitPtr<'a> {
    pub(super) fn new(bit: bool, bits: &'a mut [u8], index: usize) -> BitPtr {
        BitPtr {
            bit,
            bits,
            mut_bit: bit,
            index,
        }
    }
}

impl<'a> Deref for BitPtr<'a> {
    type Target = bool;
    fn deref(&self) -> &Self::Target {
        &self.mut_bit
    }
}

impl<'a> DerefMut for BitPtr<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.mut_bit
    }
}

impl<'a> Drop for BitPtr<'a> {
    fn drop(&mut self) {
        if self.bit != self.mut_bit {
            if self.mut_bit {
                bitops::set_msb_n(&mut self.bits[self.index / 8], (self.index % 8) as u8);
            } else {
                self.bits[self.index / 8].clear_msb_nth_assign((self.index % 8) as u8);
            }
        }
    }
}

macro_rules! bitwise_partial_assign {
    ($val: expr, $start:expr, $len: expr, $rhs: expr, &=) => {
        $val.and_partial_assign($start, $len, $rhs);
    };
    ($val: expr, $start:expr, $len: expr, $rhs: expr, |=) => {
        $val.or_partial_assign($start, $len, $rhs);
    };
    ($val: expr, $start:expr, $len: expr, $rhs: expr, ^=) => {
        $val.xor_partial_assign($start, $len, $rhs);
    };
}

macro_rules! bitwise_lsb_assign {
    ($val: expr, $n:expr, $rhs: expr, &=) => {
        $val.and_lsb_assign($n, $rhs);
    };
    ($val: expr, $n:expr, $rhs: expr, |=) => {
        $val.or_lsb_assign($n, $rhs);
    };
    ($val: expr, $n:expr, $rhs: expr, ^=) => {
        $val.xor_lsb_assign($n, $rhs);
    };
}

macro_rules! bitwise_msb_assign {
    ($val: expr, $n:expr, $rhs: expr, &=) => {
        $val.and_msb_assign($n, $rhs);
    };
    ($val: expr, $n:expr, $rhs: expr, |=) => {
        $val.or_msb_assign($n, $rhs);
    };
    ($val: expr, $n:expr, $rhs: expr, ^=) => {
        $val.xor_msb_assign($n, $rhs);
    };
}

macro_rules! impl_bitwise_assign_bitslice {
    ($t_name: ident, $fn_name: ident, $for: ty, $op: tt) => {
        impl $t_name<&BitSlice> for $for  {
            fn $fn_name(&mut self, rhs: &BitSlice) {
                let len = self.len();
                if len == 0 {
                    return;
                }

                let eb_idx = (len - 1) / 8;
                let offset = self.offset();
                let ss_start = 8 - offset;
                let (rhs_fb, rhs_fb_r) = rhs.read_bits_u8(0, 8 - offset);

                //Special Case the first byte
                if rhs_fb_r < 8 - offset {
                    //left shift the rhs_fb to align the bits
                    let rhs_fb = rhs_fb << (8 - offset - rhs_fb_r);
                    bitwise_partial_assign!(&mut self.0[0], offset as u8, rhs_fb_r as u8, rhs_fb, $op);
                    return;
                } else {
                    bitwise_partial_assign!(&mut self.0[0], offset as u8, rhs_fb_r as u8, rhs_fb, $op);
                }
                let ss = &rhs[ss_start..];
                if ss.len() == 0 {
                    return;
                }

                let mut rhs_iter = ss.iter_u8();
                let mut bits_processed = rhs_fb_r;
                for i in 1..=eb_idx {
                    if let Some((rhs_byte, rhs_bits)) = rhs_iter.next() {
                        if rhs_bits == 8 {
                            let bits_rem = len - bits_processed;
                            if bits_rem >= 8 {
                                b_expr!(self.0[i] $op rhs_byte);
                            } else {
                                bitwise_msb_assign!(self.0[i], bits_rem as u8, rhs_byte, $op);
                            }
                        } else {
                            bitwise_msb_assign!(self.0[i], rhs_bits as u8, (rhs_byte).lsb0_to_msb0(rhs_bits), $op);
                        }

                        bits_processed += rhs_bits;
                    } else {
                        return;
                    }
                }
            }
        }
    };
}

impl_bitwise_assign_bitslice!(BitAndAssign, bitand_assign, &mut BitSlice, &=);
impl_bitwise_assign_bitslice!(BitOrAssign, bitor_assign, &mut BitSlice, |=);
impl_bitwise_assign_bitslice!(BitXorAssign, bitxor_assign, &mut BitSlice, ^=);

macro_rules! bitwise_no_op {
    ($len:ident, $rhs: ident, &=) => {
        if $len == 0 || $rhs {
            return;
        }
    };
    ($len: ident, $rhs: ident, |=) => {
        if $len == 0 || !$rhs {
            return;
        }
    };
    ($len: ident, $rhs: ident, ^=) => {
        if $len == 0 || !$rhs {
            return;
        }
    };
}

macro_rules! impl_bitwise_assign_bool {
    ($t_name: ident, $fn_name: ident, $for: ty, $op: tt) => {
        impl $t_name<bool> for $for {
            fn $fn_name(&mut self, rhs: bool) {
                let len = self.len();
                bitwise_no_op!(len, rhs, $op);

                let offset = self.offset();
                if len < 8 {
                    bitwise_partial_assign!(&mut self.0[0], offset as u8, len as u8, rhs, $op);
                    return;
                }

                let mut rhs_val: u8 = 0;
                if rhs {
                    rhs_val = u8::MAX;
                }

                let eb_idx = (len - 1) / 8;
                for i in 0..=eb_idx {
                    if i == 0 {
                        bitwise_lsb_assign!(&mut self.0[i], (8 - offset) as u8, rhs, $op);
                    } else if i == eb_idx {
                        bitwise_msb_assign!(&mut self.0[i], ((len % 8) + offset) as u8, rhs, $op);
                    } else {
                        b_expr!(self.0[i] $op rhs_val);
                    }
                }
            }
        }
    };
}

impl_bitwise_assign_bool!(BitAndAssign, bitand_assign, BitSlice, &=);
impl_bitwise_assign_bool!(BitAndAssign, bitand_assign, &mut BitSlice, &=);

impl_bitwise_assign_bool!(BitOrAssign, bitor_assign, BitSlice, |=);
impl_bitwise_assign_bool!(BitOrAssign, bitor_assign, &mut BitSlice, |=);

impl_bitwise_assign_bool!(BitXorAssign, bitxor_assign, BitSlice, ^=);
impl_bitwise_assign_bool!(BitXorAssign, bitxor_assign, &mut BitSlice, ^=);

impl Not for &mut BitSlice {
    type Output = Self;
    fn not(self) -> Self::Output {
        let len = self.len();
        if len == 0 {
            return self;
        }
        // underlying slice is [u8] = self.0
        // goes from self.0[0] -> self.0[(self.len() - 1) / 8]
        // first bit in the slice starts at offset within self.0[0]
        // last bit in the slice is bit # self.len)( % 8 within self.0[self.len() / 8]
        // iterating over the bytes of the slice means iterating from 0..self.len() / 8
        // 16 bits = 0..16 -> 0..2 -> [0], [1]

        let offset = self.offset();
        if len < 8 {
            self.0[0].not_partial_assign(offset as u8, len as u8);
            return self;
        }

        let eb_idx = (len - 1) / 8;
        for i in 0..=eb_idx {
            if i == 0 {
                self.0[i].not_lsb_assign((8 - offset) as u8);
            } else if i == eb_idx {
                self.0[i].not_msb_assign(((len % 8) + offset) as u8);
            } else {
                self.0[i] = !self.0[i];
            }
        }

        self
    }
}

impl BitSlice {
    /// zeros out the three most significant bits of the length to
    /// return the actual length.
    #[inline(always)]
    pub fn len(&self) -> usize {
        slice_unpack_len!(self.0.len())
    }

    pub fn fill(&mut self, bit: bool) {
        if bit {
            *self |= true;
        } else {
            *self &= false;
        }
    }

    pub fn get(&self, index: usize) -> Option<bool> {
        if index >= self.len() {
            return None;
        }

        let index = index + self.offset();
        get_unchecked!(index, self.0);
    }

    pub fn get_mut(&mut self, index: usize) -> Option<BitPtr> {
        if let Some(bit) = self.get(index) {
            let offset = self.offset();
            return Some(BitPtr::new(bit, &mut self.0, index + offset));
        }
        return None;
    }

    pub fn any(&self) -> bool {
        if self.len() == 0 {
            return false;
        }
        let mut iter = self.iter_u128();
        while let Some((val, _)) = iter.next() {
            if val > 0 {
                return true;
            }
        }
        return false;
    }

    pub fn all(&self) -> bool {
        if self.len() == 0 {
            return true;
        }
        let mut iter = self.iter_u128();
        while let Some((val, bit_count)) = iter.next() {
            if bit_count == 128 {
                if val != u128::MAX {
                    return false;
                }
            } else {
                if val != (2u128.pow(bit_count as u32) - 1) {
                    return false;
                }
            }
        }
        return true;
    }

    pub fn set(&mut self, index: usize, value: bool) {
        if index >= self.len() {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            );
        }

        let index = index + self.offset();
        set_unchecked!(index, value, &mut self.0);
    }

    pub fn iter(&self) -> Iter {
        Iter::new(&self.0, self.offset(), self.len())
    }

    iter_unsigned!(iter_u8, IterU8);
    iter_unsigned!(iter_u16, IterU16);
    iter_unsigned!(iter_u32, IterU32);
    iter_unsigned!(iter_u64, IterU64);
    iter_unsigned!(iter_u128, IterU128);

    as_unsigned!(u8, 8, as_u8);
    as_unsigned!(u16, 16, as_u16);
    as_unsigned!(u32, 32, as_u32);
    as_unsigned!(u64, 64, as_u64);
    as_unsigned!(u128, 128, as_u128);

    read_unsigned!(u8, 8, read_u8);
    read_unsigned!(u16, 16, read_u16);
    read_unsigned!(u32, 32, read_u32);
    read_unsigned!(u64, 64, read_u64);
    read_unsigned!(u128, 128, read_u128);

    read_bits_unsigned!(u8, 8, read_bits_u8);
    read_bits_unsigned!(u16, 16, read_bits_u16);
    read_bits_unsigned!(u32, 32, read_bits_u32);
    read_bits_unsigned!(u64, 64, read_bits_u64);
    read_bits_unsigned!(u128, 128, read_bits_u128);
}

// Helpers and private methods
impl BitSlice {
    /// Returns the 3 most significant bits of the length
    pub(super) fn offset(&self) -> usize {
        slice_unpack_offset!(self.0.len())
    }

    #[inline(always)]
    pub(super) fn read_bits_lsb0(
        bits: &[u8],
        start: usize,
        len: usize,
        bit_count: BitCount,
    ) -> (u128, BitCount) {
        // let offset = self.offset();
        // let len = self.len() + offset;
        // let st_index = start + offset;
        let (val, bit_count): (u128, BitCount) =
            BitSlice::read_bits_msb0(bits, start, len, bit_count);
        return ((val).msb0_to_lsb0(bit_count), bit_count);
    }

    /// Reads a byte containing upto 8 or `bit_count` lsb bits
    /// (whichever is lower) from the specified byte starting from
    /// `start` with bitorder MSB0 (the MSB is start position
    /// 0). Returns the new byte as well as the bits read. This method
    /// can return fewer than count bits (when start > 0) if there are
    /// fewer than `count` bits in the lsb of the specified byte.
    ///
    /// The bits in the return byte are ordered in BitOrder::LSB0.
    ///
    /// byte: 0b1100_1101 start: 5, count: 3 returns (0b0000_0101, 3)
    /// byte: 0b1100_1101 start: 0, count: 3 returns (0b0000_0110, 3)
    /// byte: 0b1100_1101 start: 4, count: 6 returns (0b0000_1101, 4)
    /// byte: 0b1100_1101 start: 0, count: 8 returns (0b1100_1101, 8)
    /// byte: 0b1100_1101 start: 4, count: 2 returns (0b1100_0011, 2)
    #[inline(always)]
    fn sub_byte_lsb0(byte: u8, start: u8, bit_count: BitCount) -> (u8, BitCount) {
        debug_assert!(start <= 7, "start {} cannot be greater than 7", start);
        let count: u8;
        if bit_count < 8 {
            count = bit_count as u8;
        } else {
            count = 8;
        }

        match start {
            0 => match count {
                8 => (byte, 8),
                _ => (byte >> (8 - count), count as usize),
                //                _ => (bitops::shr_u8(byte, 8 - count), count as usize),
            },

            _ => {
                //
                let avail = 8 - start;
                if count >= avail {
                    return (byte.clear_msb(start), avail as usize);
                }
                return (byte.clear_msb(start) >> (avail - count), count as usize);
            }
        }
    }

    pub(super) fn read_bits_msb0(
        bits: &[u8],
        start: usize,
        len: usize,
        max_bits: BitCount,
    ) -> (u128, BitCount) {
        debug_assert!(
            max_bits <= 128,
            "max_bits cannot exceed 128 bits. max_bits = {}",
            max_bits
        );

        //at most read 128 bits
        let mut retval: u128 = 0;
        let mut bitsread = 0;
        let mut cursor = start;
        let mut bits_remaining = max_bits;
        if bits_remaining > len - start {
            bits_remaining = len - start;
        }

        loop {
            if bits_remaining == 0 {
                break;
            }
            let byte = bits[cursor / 8];
            let (byte_val, read) =
                BitSlice::sub_byte_lsb0(byte, (cursor % 8) as u8, bits_remaining);
            if read == 0 {
                //No more to read. So return. TODO: What should we return?
                return (retval, bitsread);
            }
            // Shift left by: 128-read-bitsread
            retval |= (byte_val as u128) << ((128 - read - bitsread) as u8);
            cursor += read;
            bitsread += read;
            bits_remaining -= read;
        }

        return (retval, bitsread);
    }
}

impl Index<usize> for &BitSlice {
    type Output = bool;
    fn index(&self, index: usize) -> &Self::Output {
        match self.get(index) {
            None => {
                panic!(
                    "index out of bounds: the len is {} but the index is {}",
                    self.len(),
                    index
                );
            }
            Some(true) => &true,
            Some(false) => &false,
        }
    }
}

impl Index<usize> for &mut BitSlice {
    type Output = bool;
    fn index(&self, index: usize) -> &Self::Output {
        match self.get(index) {
            None => {
                panic!(
                    "index out of bounds: the len is {} but the index is {}",
                    self.len(),
                    index
                );
            }
            Some(true) => &true,
            Some(false) => &false,
        }
    }
}

impl_index_range!(&BitSlice, BitSlice, 0);
impl_index_range!(&mut BitSlice, BitSlice, 0);
impl_index_range_mut!(&mut BitSlice, BitSlice, 0);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvec::{bitvec::BitVector, BitOrder};
    #[test]
    fn test_slice() {
        let mut bv = BitVector::with_capacity(20);

        bv.push_u8(0b1011_0011, None);
        bv.push_u8(0b1011_0011, None);
        assert_eq!(bv.get(0), Some(true));
        assert_eq!(bv.get(1), Some(false));

        assert_eq!(bv.len(), 16);
        let s = &bv[0..16];
        assert_eq!(s.len(), 16);

        assert_eq!(bv[0], true);
        assert_eq!(bv[1], false);

        let slice = &bv[9..11];

        assert_eq!(slice.len(), 2);
        assert_eq!(slice.offset(), 1);
        assert_eq!(slice[0], false);
        assert_eq!(slice[1], true);

        let ms = &mut bv[9..11];
        assert_eq!(ms[0], false);
        ms.set(0, true);
        assert_eq!(ms[0], true);

        let slice2 = &bv[9..11];

        assert_eq!(slice2[0], true);
    }

    #[test]
    fn test_read_bits_u8() {
        let mut bvec = BitVector::with_capacity(20);
        bvec.push_bits_u8(0b1100_1011, 8, BitOrder::Msb0);
        bvec.push_bits_u8(0b1010_0101, 8, BitOrder::Msb0);

        let bv = &*bvec;
        assert_eq!(bv.len(), 16);

        // Read a byte from start = 0
        let (byte, bit_count) = bv.read_bits_u8(0, 8);
        assert_eq!(bit_count, 8);
        assert_eq!(byte, 0b1100_1011);

        //Read a byte from start = 4
        let (byte, bit_count) = bv.read_bits_u8(4, 8);
        assert_eq!(bit_count, 8);
        assert_eq!(byte, 0b1011_1010);

        //Read a byte from start = 12
        let (byte, bit_count) = bv.read_bits_u8(12, 8);
        assert_eq!(bit_count, 4);
        assert_eq!(byte, 0b0000_0101);

        //Read a byte from start = 15
        let (byte, bit_count) = bv.read_bits_u8(15, 8);
        assert_eq!(bit_count, 1);
        assert_eq!(byte, 0b0000_0001);

        //Read a byte from start = 16
        let (byte, bit_count) = bv.read_bits_u8(16, 8);
        assert_eq!(bit_count, 0);
        assert_eq!(byte, 0b0000_0000);
    }

    #[test]
    fn test_read_u8_slice() {
        let mut bvec = BitVector::with_capacity(20);
        bvec.push_bits_u8(0b1100_1011, 8, BitOrder::Msb0);
        bvec.push_bits_u8(0b1010_0101, 8, BitOrder::Msb0);

        let slice = &bvec[2..13]; // [0010_1110, 100]
        assert_eq!(slice.len(), 11);

        let (byte, bit_count) = slice.read_bits_u8(0, 8);
        assert_eq!(bit_count, 8);
        assert_eq!(byte, 0b0010_1110);

        let (byte, bit_count) = slice.read_bits_u8(4, 8);
        assert_eq!(bit_count, 7);
        assert_eq!(byte, 0b0111_0100);

        let (byte, bit_count) = slice.read_bits_u8(5, 2);
        assert_eq!(bit_count, 2);
        assert_eq!(byte, 0b0000_0011);

        let (byte, bit_count) = slice.read_bits_u8(8, 8);
        assert_eq!(bit_count, 3);
        assert_eq!(byte, 0b0000_0100);

        let (byte, bit_count) = slice.read_bits_u8(10, 8);
        assert_eq!(bit_count, 1);
        assert_eq!(byte, 0b0000_0000);
    }

    #[test]
    fn test_from() {
        let mut bvec = BitVector::with_capacity(20);
        bvec.push_bits_u8(0b1100_1011, 8, BitOrder::Msb0);
        bvec.push_bits_u8(0b1010_0101, 8, BitOrder::Msb0);

        let slice = &bvec[8..16];
        let (val, read) = slice.as_u16();
        assert_eq!(read, 8);
        assert_eq!(val, 0b1010_0101);
        let val2: u16 = u16::try_from(slice).unwrap();
        assert_eq!(val2, 0b1010_0101);
    }

    #[test]
    fn test_sub_byte() {
        assert_eq!(BitSlice::sub_byte_lsb0(0b1100_1101, 5, 3), (0b0000_0101, 3));
        assert_eq!(BitSlice::sub_byte_lsb0(0b1100_1101, 0, 3), (0b0000_0110, 3));
        assert_eq!(BitSlice::sub_byte_lsb0(0b1100_1101, 4, 6), (0b0000_1101, 4));
        assert_eq!(BitSlice::sub_byte_lsb0(0b1100_1101, 0, 8), (0b1100_1101, 8));
        assert_eq!(BitSlice::sub_byte_lsb0(0b1100_1101, 4, 2), (0b0000_0011, 2));
        assert_eq!(BitSlice::sub_byte_lsb0(0b1100_1101, 0, 1), (0b0000_0001, 1));
        assert_eq!(BitSlice::sub_byte_lsb0(0b1100_1101, 7, 8), (0b0000_0001, 1));
    }

    #[test]
    fn test_get_mut() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1011_1100, None);
        assert_eq!(bv[0], true);
        let s = &mut bv[0..7];
        *s.get_mut(0).unwrap() = false;
        assert_eq!(bv[0], false);
    }

    #[test]
    fn test_bit_not_3() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..5];
        assert_eq!(s.len(), 3);
        assert_eq!(s.read_u8(0), (0b0000_0010, 3));
        s = !s;
        assert_eq!(s.read_u8(0), (0b0000_0101, 3));
        assert_eq!(bv.read_u8(0), (0b1010_1011, 8));
    }

    #[test]
    fn test_bit_not_8() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[0..8];
        assert_eq!(s.len(), 8);
        assert_eq!(s.read_u8(0), (0b1001_0011, 8));
        s = !s;
        assert_eq!(s.read_u8(0), (0b0110_1100, 8));
        assert_eq!(bv.read_u8(0), (0b0110_1100, 8));
    }

    #[test]
    fn test_bit_not_0() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        s = !s;
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
    }

    #[test]
    fn test_bit_not_25() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        //     0       7 8       15        23        31        39        47
        // bv: 1001_0011_0101_1010 0110_1100 1010_0101 1110_1011_1101_0111
        //                 ^                              ^
        // slice:          01_1010 0110_1100 1010_0101 111
        //                 ^        ^         ^         ^
        //                 0        7         15        23
        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);
        assert_eq!(s.read_u8(0), (0b0110_1001, 8));
        assert_eq!(s.read_u8(8), (0b1011_0010, 8));
        assert_eq!(s.read_u8(16), (0b1001_0111, 8));
        assert_eq!(s.read_u8(24), (0b0000_0001, 1));

        s = !s;
        assert_eq!(s.read_u8(0), (0b1001_0110, 8));
        assert_eq!(s.read_u8(8), (0b0100_1101, 8));
        assert_eq!(s.read_u8(16), (0b0110_1000, 8));
        assert_eq!(s.read_u8(24), (0b0000_0000, 1));

        assert_eq!(bv.read_u16(0), (0b1001_0011_0110_0101, 16));
        assert_eq!(bv.read_u16(16), (0b1001_0011_0101_1010, 16));
        assert_eq!(bv.read_u16(32), (0b0000_1011_1101_0111, 16));
    }

    #[test]
    fn test_bit_and_8() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[0..8];
        assert_eq!(s.len(), 8);
        assert_eq!(s.read_u8(0), (0b1001_0011, 8));
        s &= false;
        assert_eq!(s.read_u8(0), (0b0000_0000, 8));
        assert_eq!(bv.read_u8(0), (0b0000_0000, 8));
        bv.clear();
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[0..8];
        assert_eq!(s.len(), 8);
        assert_eq!(s.read_u8(0), (0b1001_0011, 8));
        s &= true;
        assert_eq!(s.read_u8(0), (0b1001_0011, 8));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
    }

    #[test]
    fn test_bit_and_0() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        s &= false;
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
        bv.clear();
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        s &= true;
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
    }

    #[test]
    fn test_bit_and_3() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..5];
        assert_eq!(s.len(), 3);
        assert_eq!(s.read_u8(0), (0b0000_0010, 3));
        s &= false;
        assert_eq!(s.read_u8(0), (0b0000_0000, 3));
        assert_eq!(bv.read_u8(0), (0b1000_0011, 8));
        bv.clear();
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..5];
        assert_eq!(s.len(), 3);
        assert_eq!(s.read_u8(0), (0b0000_0010, 3));
        s &= true;
        assert_eq!(s.read_u8(0), (0b0000_0010, 3));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
    }

    #[test]
    fn test_bit_and_25() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        //     0       7 8       15        23        31        39        47
        // bv: 1001_0011_0101_1010 0110_1100 1010_0101 1110_1011_1101_0111
        //                 ^                              ^
        // slice:          01_1010 0110_1100 1010_0101 111
        //                 ^        ^         ^         ^
        //                 0        7         15        23
        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);
        assert_eq!(s.read_u8(0), (0b0110_1001, 8));
        assert_eq!(s.read_u8(8), (0b1011_0010, 8));
        assert_eq!(s.read_u8(16), (0b1001_0111, 8));
        assert_eq!(s.read_u8(24), (0b0000_0001, 1));

        s &= true;
        assert_eq!(s.read_u8(0), (0b0110_1001, 8));
        assert_eq!(s.read_u8(8), (0b1011_0010, 8));
        assert_eq!(s.read_u8(16), (0b1001_0111, 8));
        assert_eq!(s.read_u8(24), (0b0000_0001, 1));
        assert_eq!(bv.read_u16(0), (0b1001_0011_0101_1010, 16));
        assert_eq!(bv.read_u16(16), (0b0110_1100_1010_0101, 16));
        assert_eq!(bv.read_u16(32), (0b1110_1011_1101_0111, 16));

        bv.clear();
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));
        let mut s = &mut bv[10..35];
        s &= false;
        assert_eq!(s.read_u8(0), (0b0000_0000, 8));
        assert_eq!(s.read_u8(8), (0b0000_0000, 8));
        assert_eq!(s.read_u8(16), (0b0000_0000, 8));
        assert_eq!(s.read_u8(24), (0b0000_0000, 1));
        // range [10..35] in the bitvector should be cleared
        assert_eq!(bv.read_u16(0), (0b1001_0011_0100_0000, 16));
        assert_eq!(bv.read_u16(16), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(32), (0b0000_1011_1101_0111, 16));
    }

    //TODO: for each of these bit and / or tests make sure to assert
    // the contents of the underlying bitvector are correct
    #[test]
    fn test_bit_or_8() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[0..8];
        assert_eq!(s.len(), 8);
        assert_eq!(s.read_u8(0), (0b1001_0011, 8));
        s |= true;
        assert_eq!(s.read_u8(0), (0b1111_1111, 8));
        assert_eq!(bv.read_u8(0), (0b1111_1111, 8));
        bv.clear();
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[0..8];
        assert_eq!(s.len(), 8);
        assert_eq!(s.read_u8(0), (0b1001_0011, 8));
        s |= false;
        assert_eq!(s.read_u8(0), (0b1001_0011, 8));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
    }

    #[test]
    fn test_bit_or_0() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        s |= false;
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
        bv.clear();
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        s |= true;
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
    }

    #[test]
    fn test_bit_or_3() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..5];
        assert_eq!(s.len(), 3);
        assert_eq!(s.read_u8(0), (0b0000_0010, 3));
        s |= false;
        assert_eq!(s.read_u8(0), (0b0000_0010, 3));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
        bv.clear();
        bv.push_u8(0b1001_0000, Some(8));
        let mut s = &mut bv[2..5];
        assert_eq!(s.len(), 3);
        assert_eq!(s.read_u8(0), (0b0000_0010, 3));
        s |= true;
        assert_eq!(s.read_u8(0), (0b0000_0111, 3));
        assert_eq!(bv.read_u8(0), (0b1011_1000, 8));
    }

    #[test]
    fn test_bit_or_25() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        //     0       7 8       15        23        31        39        47
        // bv: 1001_0011_0101_1010 0110_1100 1010_0101 1110_1011_1101_0111
        //                 ^                              ^
        // slice:          01_1010 0110_1100 1010_0101 111
        //                 ^        ^         ^         ^
        //                 0        7         15        23
        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);
        assert_eq!(s.read_u8(0), (0b0110_1001, 8));
        assert_eq!(s.read_u8(8), (0b1011_0010, 8));
        assert_eq!(s.read_u8(16), (0b1001_0111, 8));
        assert_eq!(s.read_u8(24), (0b0000_0001, 1));

        s |= false;
        assert_eq!(s.read_u8(0), (0b0110_1001, 8));
        assert_eq!(s.read_u8(8), (0b1011_0010, 8));
        assert_eq!(s.read_u8(16), (0b1001_0111, 8));
        assert_eq!(s.read_u8(24), (0b0000_0001, 1));
        assert_eq!(bv.read_u16(0), (0b1001_0011_0101_1010, 16));
        assert_eq!(bv.read_u16(16), (0b0110_1100_1010_0101, 16));
        assert_eq!(bv.read_u16(32), (0b1110_1011_1101_0111, 16));

        bv.clear();
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));
        let mut s = &mut bv[10..35];
        s |= true;
        assert_eq!(s.read_u8(0), (0b1111_1111, 8));
        assert_eq!(s.read_u8(8), (0b1111_1111, 8));
        assert_eq!(s.read_u8(16), (0b1111_1111, 8));
        assert_eq!(s.read_u8(24), (0b0000_0001, 1));
        // range [10..35] in the bitvector should be all 1
        assert_eq!(bv.read_u16(0), (0b1001_0011_0111_1111, 16));
        assert_eq!(bv.read_u16(16), (0b1111_1111_1111_1111, 16));
        assert_eq!(bv.read_u16(32), (0b1110_1011_1101_0111, 16));
    }

    #[test]
    fn test_bit_xor_8() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[0..8];
        assert_eq!(s.len(), 8);
        assert_eq!(s.read_u8(0), (0b1001_0011, 8));
        s ^= true;
        assert_eq!(s.read_u8(0), (0b0110_1100, 8));
        assert_eq!(bv.read_u8(0), (0b0110_1100, 8));
        bv.clear();
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[0..8];
        assert_eq!(s.len(), 8);
        assert_eq!(s.read_u8(0), (0b1001_0011, 8));
        s ^= false;
        assert_eq!(s.read_u8(0), (0b1001_0011, 8));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
    }

    #[test]
    fn test_bit_xor_0() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        s ^= false;
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
        bv.clear();
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        s ^= true;
        assert_eq!(s.read_u8(0), (0b0000_0000, 0));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
    }

    #[test]
    fn test_bit_xor_3() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..5];
        assert_eq!(s.len(), 3);
        assert_eq!(s.read_u8(0), (0b0000_0010, 3));
        s ^= false;
        assert_eq!(s.read_u8(0), (0b0000_0010, 3));
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
        bv.clear();
        bv.push_u8(0b1001_0000, Some(8));
        let mut s = &mut bv[2..5];
        assert_eq!(s.len(), 3);
        assert_eq!(s.read_u8(0), (0b0000_0010, 3));
        s ^= true;
        assert_eq!(s.read_u8(0), (0b0000_0101, 3));
        assert_eq!(bv.read_u8(0), (0b1010_1000, 8));
    }

    #[test]
    fn test_bit_xor_25() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        //     0       7 8       15        23        31        39        47
        // bv: 1001_0011_0101_1010 0110_1100 1010_0101 1110_1011_1101_0111
        //                 ^                              ^
        // slice:          01_1010 0110_1100 1010_0101 111
        //                 ^        ^         ^         ^
        //                 0        7         15        23
        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);
        assert_eq!(s.read_u8(0), (0b0110_1001, 8));
        assert_eq!(s.read_u8(8), (0b1011_0010, 8));
        assert_eq!(s.read_u8(16), (0b1001_0111, 8));
        assert_eq!(s.read_u8(24), (0b0000_0001, 1));

        s ^= false;
        assert_eq!(s.read_u8(0), (0b0110_1001, 8));
        assert_eq!(s.read_u8(8), (0b1011_0010, 8));
        assert_eq!(s.read_u8(16), (0b1001_0111, 8));
        assert_eq!(s.read_u8(24), (0b0000_0001, 1));
        assert_eq!(bv.read_u16(0), (0b1001_0011_0101_1010, 16));
        assert_eq!(bv.read_u16(16), (0b0110_1100_1010_0101, 16));
        assert_eq!(bv.read_u16(32), (0b1110_1011_1101_0111, 16));

        bv.clear();
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));
        let mut s = &mut bv[10..35];
        s ^= true;
        assert_eq!(s.read_u8(0), (0b1001_0110, 8));
        assert_eq!(s.read_u8(8), (0b0100_1101, 8));
        assert_eq!(s.read_u8(16), (0b0110_1000, 8));
        assert_eq!(s.read_u8(24), (0b0000_0000, 1));
        // range [10..35] in the bitvector should be flipped
        assert_eq!(bv.read_u16(0), (0b1001_0011_0110_0101, 16));
        assert_eq!(bv.read_u16(16), (0b1001_0011_0101_1010, 16));
        assert_eq!(bv.read_u16(32), (0b0000_1011_1101_0111, 16));
    }

    #[test]
    fn test_bit_and_slice() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        //        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1110_1011_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101, Some(8));
        let s2 = &bv2[0..];
        assert_eq!(s2.len(), 24);

        s &= s2;

        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // bv2: (s2)       11 1010 1111 0101 1101 1011 01
        // s &= s2         01 1010 0110 0100 1000 0001 011
        // res 1001_0011_0101 1010 0110 0100 1000 0001 0110_1011_1101_0111
        assert_eq!(s.read_u32(0), (0b01_1010_0110_0100_1000_0001_011, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0101_1010_0110_0100_1000_0001_0110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_and_slice_0() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1110_1011_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101, Some(8));
        let s2 = &bv2[0..0];
        assert_eq!(s2.len(), 0);

        s &= s2;
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              []
        // s &= s2         01_1010 0110_1100_1010_0101 111
        // res 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        assert_eq!(s.read_u32(0), (0b01_1010_0110_1100_1010_0101_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0101_1010_0110_1100_1010_0101_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_and_slice_3() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1010_1011_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101, Some(8));
        let s2 = &bv2[0..3];
        assert_eq!(s2.len(), 3);

        s &= s2;
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              10 1
        // s &= s2         00_1010 0110_1100_1010_0101 111
        // res 1001_0011_0100_1010 0110_1100_1010_0101 1110_1011_1101_0111
        assert_eq!(s.read_u32(0), (0b00_1010_0110_1100_1010_0101_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0100_1010_0110_1100_1010_0101_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_and_slice_8() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1010_1010_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101, Some(8));
        let s2 = &bv2[0..8];
        assert_eq!(s2.len(), 8);

        s &= s2;
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              10 1010 10
        // s &= s2         00_1010 0010_1100_1010_0101 111
        // res 1001_0011_0100_1010 0010_1100_1010_0101 1110_1011_1101_0111
        assert_eq!(s.read_u32(0), (0b00_1010_0010_1100_1010_0101_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0100_1010_0010_1100_1010_0101_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_and_slice_32() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1010_1010_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101_0011_1010, Some(16));
        let s2 = &bv2[0..32];
        assert_eq!(s2.len(), 32);

        s &= s2;
        //                   0         1         2         3
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              10 1010 1011 0101 1101 1011 0100 11_1010
        // s &= s2         00 1010 0010 0100 1000 0001 010
        // res 1001_0011_0100 1010 0010 0100 1000 0001 0100_1011_1101_0111

        assert_eq!(s.read_u32(0), (0b00_1010_0010_0100_1000_0001_010, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0100_1010_0010_0100_1000_0001_0100_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_or_slice_0() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1110_1011_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101, Some(8));
        let s2 = &bv2[0..0];
        assert_eq!(s2.len(), 0);

        s |= s2;
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              []
        // s |= s2         01_1010 0110_1100_1010_0101 111
        // res 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        assert_eq!(s.read_u32(0), (0b01_1010_0110_1100_1010_0101_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0101_1010_0110_1100_1010_0101_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_or_slice_3() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1010_1011_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101, Some(8));
        let s2 = &bv2[0..3];
        assert_eq!(s2.len(), 3);

        s |= s2;
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              10 1
        // s |= s2         11_1010 0110_1100_1010_0101 111
        // res 1001_0011_0111_1010 0110_1100_1010_0101 1110_1011_1101_0111
        assert_eq!(s.read_u32(0), (0b11_1010_0110_1100_1010_0101_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0111_1010_0110_1100_1010_0101_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_or_slice_8() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1010_1010_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101, Some(8));
        let s2 = &bv2[0..8];
        assert_eq!(s2.len(), 8);

        s |= s2;
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              10 1010 10
        // s |= s2         11_1010 1110_1100_1010_0101 111
        // res 1001_0011_0111_1010 1110_1100_1010_0101 1110_1011_1101_0111
        assert_eq!(s.read_u32(0), (0b11_1010_1110_1100_1010_0101_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0111_1010_1110_1100_1010_0101_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_or_slice_32() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1010_1010_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101_0011_1010, Some(16));
        let s2 = &bv2[0..32];
        assert_eq!(s2.len(), 32);

        s |= s2;
        //                   0         1         2         3
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              10 1010 1011 0101 1101 1011 0100 11_1010
        // s |= s2         11_1010 1111 1101 1111 1111 111
        // res 1001_0011_0111_1010 1111 1101 1111 1111 1110_1011_1101_0111

        assert_eq!(s.read_u32(0), (0b11_1010_1111_1101_1111_1111_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0111_1010_1111_1101_1111_1111_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_xor_slice_0() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1110_1011_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101, Some(8));
        let s2 = &bv2[0..0];
        assert_eq!(s2.len(), 0);

        s ^= s2;
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              []
        // s ^= s2         01_1010 0110_1100_1010_0101 111
        // res 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        assert_eq!(s.read_u32(0), (0b01_1010_0110_1100_1010_0101_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0101_1010_0110_1100_1010_0101_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_xor_slice_3() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1010_1011_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101, Some(8));
        let s2 = &bv2[0..3];
        assert_eq!(s2.len(), 3);

        s ^= s2;
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              10 1
        // s ^= s2         11_0010 0110_1100_1010_0101 111
        // res 1001_0011_0111_0010 0110_1100_1010_0101 1110_1011_1101_0111
        assert_eq!(s.read_u32(0), (0b11_0010_0110_1100_1010_0101_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0111_0010_0110_1100_1010_0101_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_xor_slice_8() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1010_1010_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101, Some(8));
        let s2 = &bv2[0..8];
        assert_eq!(s2.len(), 8);

        s ^= s2;
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        // s2              10 1010 10
        // s ^= s2         11_0000 1110_1100_1010_0101 111
        // res 1001_0011_0111_0000 1110_1100_1010_0101 1110_1011_1101_0111
        assert_eq!(s.read_u32(0), (0b11_0000_1110_1100_1010_0101_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0111_0000_1110_1100_1010_0101_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_bit_xor_slice_32() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let mut s = &mut bv[10..35];
        assert_eq!(s.len(), 25);

        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1010_1010_1101_0111, Some(16));
        bv2.push_u16(0b0110_1101_0011_1010, Some(16));
        let s2 = &bv2[0..32];
        assert_eq!(s2.len(), 32);

        s ^= s2;
        //                   0         1         2         3
        // bv: 1001_0011_0101_1010 0110_1100_1010_0101 1110_1011_1101_0111
        //             7   ^     15        23        31   ^    39        47
        //                 10                             35
        //                 01_1010 0110_1100_1010_0101 111
        // s2              10 1010 1011 0101 1101 1011 0100 11_1010
        // s ^= s2         11_0000 1101 1001 0111 1110 101
        // res 1001_0011_0111_0000 1101 1001 0111 1110 1010_1011_1101_0111

        assert_eq!(s.read_u32(0), (0b11_0000_1101_1001_0111_1110_101, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0111_0000_1101_1001_0111_1110_1010_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_subslice() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));

        let slice = &bv[8..16];
        assert_eq!(slice.len(), 8);
        assert_eq!(slice.read_u8(0), (0b0101_1010, 8));
        let ss = &slice[2..6];
        assert_eq!(ss.read_u8(0), (0b0000_0110, 4));

        let mut slice = &mut bv[8..16];
        assert_eq!(slice.len(), 8);
        assert_eq!(slice.read_u8(0), (0b0101_1010, 8));
        let ss_mut = &mut slice[2..7];
        assert_eq!(ss_mut.len(), 5);
        assert_eq!(ss_mut.read_u8(0), (0b0000_1101, 5));

        ss_mut.fill(true);
        assert_eq!(ss_mut.read_u16(0), (0b0001_1111, 5));
        ss_mut.fill(false);
        assert_eq!(ss_mut.read_u16(0), (0b0000_0000, 5));
    }

    #[test]
    fn test_slice_fill_0() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let s = &mut bv[10..35];
        assert_eq!(s.len(), 25);
        s.fill(false);
        assert_eq!(s.read_u32(0), (0, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0100_0000_0000_0000_0000_0000_000_0_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_slice_fill_1() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u16(0b0110_1100_1010_0101, Some(16));
        bv.push_u16(0b1110_1011_1101_0111, Some(16));

        let s = &mut bv[10..35];
        assert_eq!(s.len(), 25);
        s.fill(true);
        assert_eq!(s.read_u32(0), (0b11_1111_1111_1111_1111_1111_111, 25));
        assert_eq!(
            bv.read_u64(0),
            (
                0b1001_0011_0111_1111_1111_1111_1111_1111_1110_1011_1101_0111,
                48
            )
        );
    }

    #[test]
    fn test_all() {
        //test that all bits in the slice are 1
        let mut bv = BitVector::with_capacity(128);
        bv.push_u128(u128::MAX, None);
        let slice = &bv[..];
        assert_eq!(slice.all(), true);

        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_1111_1111, Some(16));
        assert_eq!(bv[0..8].all(), false);
        assert_eq!(bv[8..16].all(), true);
        assert_eq!(bv[0..1].all(), true);
        assert_eq!(bv[1..3].all(), false);
        assert_eq!(bv[6..].all(), true);
    }

    #[test]
    fn test_any() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u128(u128::MAX, None);
        let slice = &bv[..];
        assert_eq!(slice.any(), true);

        let mut bv = BitVector::with_capacity(128);
        bv.push_u128(0, Some(128));
        let slice = &bv[..];
        assert_eq!(slice.any(), false);

        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1001_0011_1111_0000, Some(16));
        assert_eq!(bv[0..8].any(), true);
        assert_eq!(bv[8..16].any(), true);
        assert_eq!(bv[0..1].any(), true);
        assert_eq!(bv[1..3].any(), false);
        assert_eq!(bv[6..].any(), true);
        assert_eq!(bv[12..].any(), false);
    }
}
