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
    bitref::{BitRef, BitRefMut},
    bitvec::BitVector,
    bytes,
    iter::{Iter, IterMut, IterOnes, IterU128, IterU16, IterU32, IterU64, IterU8, IterZeros},
    traits::{
        AsMsb0, BitwiseClearAssign, BitwiseLsbAssign, BitwiseMsbAssign, BitwisePartialAssign,
        NotLsbAssign, NotMsbAssign, NotPartialAssign,
    },
    BitCount, BitOrder,
};
use core::convert::TryFrom;
use core::fmt;
use core::fmt::Debug;
use core::ops::BitAndAssign;
use core::ops::BitOrAssign;
use core::ops::BitXorAssign;
use core::ops::Index;
use core::ops::IndexMut;
use core::ops::Not;
use core::ops::Range;
use core::ops::RangeFrom;
use core::ops::RangeFull;
use core::ops::RangeInclusive;
use core::ops::RangeTo;
use core::ops::RangeToInclusive;

/// A slice of bits backed by a [`BitVector`](../struct.BitVector.html).
///
/// The `BitSlice` is an unsized type and is a view into a range
/// within a [`BitVector`](BitVector). A [`BitVector`](BitVector) can
/// produce mutable or immutable slices which in turn can be
/// subsliced.
///
/// The `BitSlice` is a wrapper around `[u8]` and borrows memory via
/// reference types `&BitSlice` and `&mut BitSlice`. The memory in a
/// `BitSlice` is owned and managed by the underlying
/// [`BitVector`](BitVector).
///
/// # Examples
/// ```
/// use deepmesa::collections::BitVector;
///
/// let mut bv = BitVector::with_capacity(20);
/// bv.push_u8(0b1011_0011, None);
/// bv.push_u8(0b1011_0011, None);
///
/// let slice = &bv[0..16];
///
/// assert_eq!(slice.len(), 16);
/// assert_eq!(slice[0], true);
/// assert_eq!(slice[1], false);
///
/// let slice_mut = &mut bv[9..11];
/// assert_eq!(slice_mut[0], false);
/// slice_mut.set(0, true);
/// assert_eq!(slice_mut[0], true);
///
/// ```
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
    (
        $(#[$outer:meta])*
        $iter_fn: ident, $iter_type: ident
    ) => {
        $(#[$outer])*
        pub fn $iter_fn(&self) -> $iter_type {
            $iter_type::new(&self.0, self.offset(), self.len())
        }
    };
}

macro_rules! read_unsigned {
    (
        $(#[$outer:meta])*
        $u_type:ty, $max_bits: literal, $read_fn: ident
    ) => {
        $(#[$outer])*
        pub fn $read_fn(&self, start: usize) -> ($u_type, BitCount) {
            let len = self.len();
            start_bounds_check!(start, len);

            let offset = self.offset();
            let (val, bit_count) =
                bytes::read_bits(&self.0, start + offset, len + offset, $max_bits, BitOrder::Lsb0);

            (val as $u_type, bit_count)
        }
    };
}

macro_rules! read_bits_unsigned {
    (
        $(#[$outer:meta])*
        $i:ident, $b: literal, $read_bits_fn: ident
    ) => {
        $(#[$outer])*
        pub fn $read_bits_fn(&self, start: usize, max_bits: BitCount) -> ($i, BitCount) {
            let len = self.len();
            start_bounds_check!(start, len);

            if max_bits > $b {
                panic!(
                    "cannot read more than $b bits into a $i. max_bits={}",
                    max_bits
                );
            }
            match max_bits {
                0=> (0,0),
                _ => {
                    let offset = self.offset();
                    let (val, bit_count) =
                        bytes::read_bits(&self.0, start + offset, len + offset, max_bits, BitOrder::Lsb0);
                    (val as $i, bit_count)
                }
            }
        }
    };
}

macro_rules! as_unsigned {
    (
        $(#[$outer:meta])*
        $u_type:ty, $max_bits: literal, $as_fn: ident
    ) => {
        $(#[$outer])*
        pub fn $as_fn(&self) -> ($u_type, BitCount) {
            let len = self.len();
            if len > $max_bits {
                panic!(
                    concat!("len {} bits is too big to fit into a ", stringify!($i)),
                    len
                );
            }
            let offset = self.offset();
            let (val, count) = bytes::read_bits(&self.0, offset, len + offset, $max_bits, BitOrder::Lsb0);
            (val as $u_type, count)
        }
    };
}

try_from_bitslice!(u8, 8);
try_from_bitslice!(u16, 16);
try_from_bitslice!(u32, 32);
try_from_bitslice!(u64, 64);
try_from_bitslice!(u128, 128);

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
                if rhs.len() == 0 {
                    return;
                }
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
                            bitwise_msb_assign!(self.0[i], rhs_bits as u8, (rhs_byte).as_msb0(rhs_bits), $op);
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
    /// Returns the number of bits in the [`BitSlice`](BitSlice)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(22);
    /// bv.push_u8(0b1001_1011, None);
    /// let s = &bv[2..4];
    /// assert_eq!(s.len(), 2);
    /// ```
    #[inline(always)]
    pub fn len(&self) -> usize {
        slice_unpack_len!(self.0.len())
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn repeat(&self, n: usize) -> BitVector {
        let new_len = n * self.len();
        //TODO: check that new_len isn't greater than max
        // capacity. Ideally do the check in the BitVector Constructor
        let mut bv = BitVector::with_capacity(new_len);
        for _ in 0..n {
            bv.extend_from_bitslice(self);
        }
        bv
    }

    pub fn set_all(&mut self, value: bool) {
        self.fill(value);
    }

    /// Fills the slice with the specified bit.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b1000_0001, None);
    /// let s = &mut bv[1..7];
    /// s.fill(true);
    /// assert_eq!(bv.read_u8(0), (0b1111_1111, 8));
    /// ```
    pub fn fill(&mut self, bit: bool) {
        if bit {
            *self |= true;
        } else {
            *self &= false;
        }
    }

    /// Returns a boolean value indicating whether the bit at the
    /// specified index is set or `None` if the index is greater than
    /// or equal to the number of bits in the slice.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b1010_0011, None);
    /// let s = &bv[1..7];
    /// assert_eq!(s.get(0), Some(false));
    /// assert_eq!(s.get(1), Some(true));
    /// assert_eq!(s.get(7), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<bool> {
        if index >= self.len() {
            return None;
        }

        let index = index + self.offset();
        return Some(bit_at_unchecked!(index, self.0));
    }

    /// Returns a mutable reference to the bit at the specified index
    /// or `None` if the index is greater than or equal to the number
    /// of bits in the slice.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1011_1100, None);
    /// assert_eq!(bv[0], true);
    ///
    /// let s = &mut bv[0..7];
    /// *s.get_mut(0).unwrap() = false;
    /// assert_eq!(bv[0], false);
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<BitRefMut<bool>> {
        if index >= self.len() {
            return None;
        }

        let bit_idx = index + self.offset();
        let bit = bit_at_unchecked!(bit_idx, self.0);

        let byte_idx = bit_idx / 8;
        let byte_ptr = self.0[byte_idx..byte_idx].as_mut_ptr();
        return Some(BitRefMut::<bool>::new(bit, byte_ptr, bit_idx));
    }

    /// Returns true if any bit in the slice is set to `1` and false
    /// otherwise.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1011_0000, None);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.any(), true);
    /// let s = &bv[4..8];
    /// assert_eq!(s.any(), false);
    /// ```
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

    /// Returns true if all the bits in the slice are set to `1` and
    /// false otherwise.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1011_1111, None);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.all(), false);
    /// let s = &bv[4..8];
    /// assert_eq!(s.all(), true);
    /// ```
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

    /// Sets the bit at the specified index with the given bit
    /// `value`.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1011_1111, None);
    /// assert_eq!(bv.get(1), Some(false));
    ///
    /// let s = &mut bv[0..4];
    /// s.set(1, true);
    /// assert_eq!(bv.get(1), Some(true));
    /// ```
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

    /// Counts the number of bits from the start of the bitslice to
    /// the first bit set to `0`.
    ///
    /// Returns `0` if the slice is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b0011_1101, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.leading_ones(), 0);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.leading_ones(), 4);
    ///
    /// let s = &bv[8..];
    /// assert_eq!(s.leading_ones(), 0);
    ///
    /// let s = &bv[10..];
    /// assert_eq!(s.leading_ones(), 4);
    /// ```
    pub fn leading_ones(&self) -> usize {
        let len = self.len();
        match len {
            0 => 0,
            _ => {
                let offset = self.offset();
                bytes::leading_ones(&self.0, offset, len + offset)
            }
        }
    }

    /// Counts the number of bits from the start of the bitslice to
    /// the first bit set to `1`.
    ///
    /// Returns `0` if the slice is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0000_0111, Some(8));
    /// bv.push_u8(0b1100_0010, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.leading_zeros(), 0);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.leading_zeros(), 4);
    ///
    /// let s = &bv[8..];
    /// assert_eq!(s.leading_zeros(), 0);
    ///
    /// let s = &bv[10..];
    /// assert_eq!(s.leading_zeros(), 4);
    /// ```
    pub fn leading_zeros(&self) -> usize {
        let len = self.len();
        match len {
            0 => 0,
            _ => {
                let offset = self.offset();
                bytes::leading_zeros(&self.0, offset, len + offset)
            }
        }
    }

    /// Counts the number of bits from the end of the bitslice to the
    /// last bit that is set to `0`.
    ///
    /// Returns 0 if the slice is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0000_0111, Some(8));
    /// bv.push_u8(0b1100_0111, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.trailing_ones(), 0);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.trailing_ones(), 0);
    ///
    /// let s = &bv[4..10];
    /// assert_eq!(s.trailing_ones(), 5);
    ///
    /// let s = &bv[10..];
    /// assert_eq!(s.trailing_ones(), 3);
    /// ```
    pub fn trailing_ones(&self) -> usize {
        let len = self.len();
        match len {
            0 => 0,
            _ => {
                let offset = self.offset();
                bytes::trailing_ones(&self.0, offset, len + offset)
            }
        }
    }

    /// Counts the number of bits from the end of the bitslice to the
    /// last bit that is set to `1`.
    ///
    /// Returns 0 if the slice is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b0011_1000, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.trailing_zeros(), 0);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.trailing_zeros(), 0);
    ///
    /// let s = &bv[4..10];
    /// assert_eq!(s.trailing_zeros(), 5);
    ///
    /// let s = &bv[10..];
    /// assert_eq!(s.trailing_zeros(), 3);
    /// ```
    pub fn trailing_zeros(&self) -> usize {
        let len = self.len();
        match len {
            0 => 0,
            _ => {
                let offset = self.offset();
                bytes::trailing_zeros(&self.0, offset, len + offset)
            }
        }
    }

    /// Counts the bits in the slice that are set to `1`.
    /// Returns 0 if the slice is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b0011_1000, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.count_ones(), 0);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.count_ones(), 4);
    ///
    /// let s = &bv[4..10];
    /// assert_eq!(s.count_ones(), 1);
    ///
    /// let s = &bv[10..];
    /// assert_eq!(s.count_ones(), 3);
    /// ```
    pub fn count_ones(&self) -> usize {
        let len = self.len();
        match len {
            0 => 0,
            _ => {
                let offset = self.offset();
                bytes::count_ones(&self.0, offset, len + offset)
            }
        }
    }

    /// Counts the bits in the slice that are set to `0`.
    /// Returns 0 if the slice is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0000_0111, Some(8));
    /// bv.push_u8(0b1100_0111, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.count_zeros(), 0);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.count_zeros(), 4);
    ///
    /// let s = &bv[4..10];
    /// assert_eq!(s.count_zeros(), 1);
    ///
    /// let s = &bv[10..];
    /// assert_eq!(s.count_zeros(), 3);
    /// ```
    pub fn count_zeros(&self) -> usize {
        let len = self.len();
        match len {
            0 => 0,
            _ => {
                let offset = self.offset();
                bytes::count_zeros(&self.0, offset, len + offset)
            }
        }
    }

    /// Returns the index of the first bit in the `BitSlice` that is
    /// set to `1`. Returns None if there are no bits set to `1` or if
    /// the slice is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0000_0111, Some(8));
    /// bv.push_u8(0b1100_0111, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.first_one(), None);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.first_one(), None);
    ///
    /// let s = &bv[4..10];
    /// assert_eq!(s.first_one(), Some(1));
    ///
    /// let s = &bv[10..];
    /// assert_eq!(s.first_one(), Some(3));
    /// ```
    pub fn first_one(&self) -> Option<usize> {
        let len = self.len();
        match len {
            0 => None,
            _ => {
                let offset = self.offset();
                match bytes::first_one(&self.0, offset, len + offset) {
                    None => None,
                    Some(idx) => Some(idx - offset),
                }
            }
        }
    }

    /// Returns the index of the first bit in the `BitSlice` that is
    /// set to `0`. Returns None if there are no bits set to `0` or if
    /// the slice is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b0011_1000, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.first_zero(), None);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.first_zero(), None);
    ///
    /// let s = &bv[4..10];
    /// assert_eq!(s.first_zero(), Some(1));
    ///
    /// let s = &bv[10..];
    /// assert_eq!(s.first_zero(), Some(3));
    /// ```
    pub fn first_zero(&self) -> Option<usize> {
        let len = self.len();
        match len {
            0 => None,
            _ => {
                let offset = self.offset();
                match bytes::first_zero(&self.0, offset, len + offset) {
                    None => None,
                    Some(idx) => Some(idx - offset),
                }
            }
        }
    }

    /// Returns the index of the last bit in the `BitSlice` that is
    /// set to `1`. Returns None if there are no bits set to `1` or if
    /// the slice is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0000_0111, Some(8));
    /// bv.push_u8(0b1100_0110, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.last_one(), None);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.last_one(), None);
    ///
    /// let s = &bv[4..10];
    /// assert_eq!(s.last_one(), Some(5));
    ///
    /// let s = &bv[10..];
    /// assert_eq!(s.last_one(), Some(4));
    /// ```
    pub fn last_one(&self) -> Option<usize> {
        let len = self.len();
        match len {
            0 => None,
            _ => {
                let offset = self.offset();
                match bytes::last_one(&self.0, offset, len + offset) {
                    None => None,
                    Some(idx) => Some(idx - offset),
                }
            }
        }
    }

    /// Returns the index of the last bit in the `BitSlice` that is
    /// set to `0`. Returns None if there are no bits set to `0` or if
    /// the slice is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b0011_1001, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.last_zero(), None);
    ///
    /// let s = &bv[0..4];
    /// assert_eq!(s.last_zero(), None);
    ///
    /// let s = &bv[4..10];
    /// assert_eq!(s.last_zero(), Some(5));
    ///
    /// let s = &bv[10..];
    /// assert_eq!(s.last_zero(), Some(4));
    /// ```
    pub fn last_zero(&self) -> Option<usize> {
        let len = self.len();
        match len {
            0 => None,
            _ => {
                let offset = self.offset();
                match bytes::last_zero(&self.0, offset, len + offset) {
                    None => None,
                    Some(idx) => Some(idx - offset),
                }
            }
        }
    }

    /// Returns an immutable reference to the first bit in the
    /// `BitSlice` or None if the `BitSlice` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0010_0100, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.first(), None);
    ///
    /// let s = &bv[2..5];
    /// assert_eq!(s.first().as_deref(), Some(&true));
    /// ```
    pub fn first(&self) -> Option<BitRef<bool>> {
        match self.len() {
            0 => None,
            _ => {
                let bit = bit_at_unchecked!(self.offset(), self.0);
                Some(BitRef::<bool>::new(bit))
            }
        }
    }

    /// Returns a mutable reference to the first bit in the
    /// `BitSlice` or None if the `BitSlice` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0010_0100, Some(8));
    ///
    /// let s = &mut bv[2..2];
    /// assert_eq!(s.first_mut(), None);
    ///
    /// let s = &mut bv[2..5];
    /// assert_eq!(s.first_mut().as_deref(), Some(&true));
    /// *s.first_mut().unwrap() = false;
    /// assert_eq!(s.first_mut().as_deref(), Some(&false));
    /// ```
    pub fn first_mut(&mut self) -> Option<BitRefMut<bool>> {
        match self.len() {
            0 => None,
            _ => {
                let bit_idx = self.offset();
                let bit = bit_at_unchecked!(bit_idx, self.0);

                let byte_idx = bit_idx / 8;
                let byte_ptr = self.0[byte_idx..byte_idx].as_mut_ptr();
                return Some(BitRefMut::<bool>::new(bit, byte_ptr, bit_idx));
            }
        }
    }

    /// Returns an immutable reference to the last bit in the
    /// `BitSlice` or None if the `BitSlice` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0010_0100, Some(8));
    ///
    /// let s = &bv[2..2];
    /// assert_eq!(s.last(), None);
    ///
    /// let s = &bv[2..5];
    /// assert_eq!(s.last().as_deref(), Some(&false));
    /// ```
    pub fn last(&self) -> Option<BitRef<bool>> {
        match self.len() {
            0 => None,
            _ => {
                let bit = bit_at_unchecked!(self.len() - 1 + self.offset(), self.0);
                Some(BitRef::<bool>::new(bit))
            }
        }
    }

    /// Returns a mutable reference to the first bit in the
    /// `BitSlice` or None if the `BitSlice` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0010_0100, Some(8));
    ///
    /// let s = &mut bv[2..2];
    /// assert_eq!(s.last_mut(), None);
    ///
    /// let s = &mut bv[2..6];
    /// assert_eq!(s.last_mut().as_deref(), Some(&true));
    /// *s.last_mut().unwrap() = false;
    /// assert_eq!(s.last_mut().as_deref(), Some(&false));
    /// ```
    pub fn last_mut(&mut self) -> Option<BitRefMut<bool>> {
        match self.len() {
            0 => None,
            _ => {
                let bit_idx = self.len() - 1 + self.offset();
                let bit = bit_at_unchecked!(bit_idx, self.0);

                let byte_idx = bit_idx / 8;
                let byte_ptr = self.0[byte_idx..byte_idx].as_mut_ptr();
                return Some(BitRefMut::<bool>::new(bit, byte_ptr, bit_idx));
            }
        }
    }

    /// Iterates over all the bits in the `BitSlice` that are set to
    /// `1`.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0010_0101, Some(8));
    ///
    /// let s = &bv[2..2];
    /// let mut iter = s.iter_ones();
    /// assert_eq!(iter.next(), None);
    ///
    /// let s = &bv[2..6];
    /// let mut iter = s.iter_ones();
    /// assert_eq!(iter.next(), Some(0));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_ones(&self) -> IterOnes {
        IterOnes::new(&self.0, self.offset(), self.len())
    }

    /// Iterates over all the bits in the `BitSlice` that are set to
    /// `0`.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1101_1010, Some(8));
    ///
    /// let s = &bv[2..2];
    /// let mut iter = s.iter_zeros();
    /// assert_eq!(iter.next(), None);
    ///
    /// let s = &bv[2..6];
    /// let mut iter = s.iter_zeros();
    /// assert_eq!(iter.next(), Some(0));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_zeros(&self) -> IterZeros {
        IterZeros::new(&self.0, self.offset(), self.len())
    }

    /// Returns an iterator over the bits of this
    /// [`BitSlice`](BitSlice)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b1011_0011, None);
    ///
    /// let s = &bv[0..3];
    /// let mut iter = s.iter();
    /// assert_eq!(iter.next(), Some(true));
    /// assert_eq!(iter.next(), Some(false));
    /// assert_eq!(iter.next(), Some(true));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter {
        Iter::new(&self.0, self.offset(), self.len())
    }

    /// Returns a mutable iterator that allows modifying the bits of
    /// this [`BitSlice`](BitSlice)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1011_1100, None);
    /// assert_eq!(bv[0], true);
    ///
    /// let s = &mut bv[0..7];
    /// let iter = s.iter_mut();
    /// for mut bit in iter {
    ///    *bit = true;
    /// }
    /// assert_eq!(bv.read_u8(0), (0b1111_1110, 8));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut {
        let offset = self.offset();
        let len = self.len();
        IterMut::new(&mut self.0, offset, len)
    }

    iter_unsigned!(
        /// Returns an iterator that iterates over the
        /// [`BitSlice`](BitSlice) 8 bits at a time. Each invocation
        /// of `iter.next` returns a u8 value and the number of bits
        /// read. The bits are read from the lower to the higher index
        /// from the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// The iterator returns None if there are no more bits to
        /// return
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u16(0b0101_1101_0011_1010, Some(16));
        ///
        /// let s = &bv[..];
        /// let mut iter = s.iter_u8();
        /// assert_eq!(iter.next(), Some((0b0101_1101, 8)));
        /// assert_eq!(iter.next(), Some((0b0011_1010, 8)));
        /// assert_eq!(iter.next(), None);
        /// ```
        iter_u8,
        IterU8
    );
    iter_unsigned!(
        /// Returns an iterator that iterates over the
        /// [`BitSlice`](BitSlice) 16 bits at a time. Each invocation
        /// of `iter.next` returns a u16 value and the number of bits
        /// read. The bits are read from the lower to the higher index
        /// from the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// The iterator returns None if there are no more bits to
        /// return
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u16(0b0101_1101_0011_1010, Some(16));
        ///
        /// let s = &bv[..];
        /// let mut iter = s.iter_u16();
        /// assert_eq!(iter.next(), Some((0b0101_1101_0011_1010, 16)));
        /// assert_eq!(iter.next(), None);
        /// ```
        iter_u16,
        IterU16
    );
    iter_unsigned!(
        /// Returns an iterator that iterates over the
        /// [`BitSlice`](BitSlice) 32 bits at a time. Each invocation
        /// of `iter.next` returns a u32 value and the number of bits
        /// read. The bits are read from the lower to the higher index
        /// from the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// The iterator returns None if there are no more bits to
        /// return
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u16(0b0101_1101_0011_1010, Some(16));
        /// bv.push_u16(0b1111_0011_1100_0000, Some(16));
        ///
        /// let s = &bv[..];
        /// let mut iter = s.iter_u32();
        /// assert_eq!(iter.next(), Some((0b0101_1101_0011_1010_1111_0011_1100_0000, 32)));
        /// assert_eq!(iter.next(), None);
        /// ```
        iter_u32,
        IterU32
    );
    iter_unsigned!(
        /// Returns an iterator that iterates over the
        /// [`BitSlice`](BitSlice) 64 bits at a time. Each invocation
        /// of `iter.next` returns a u64 value and the number of bits
        /// read. The bits are read from the lower to the higher index
        /// from the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// The iterator returns None if there are no more bits to
        /// return
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u64(u64::MAX, Some(64));
        ///
        /// let s = &bv[..];
        /// let mut iter = s.iter_u64();
        /// assert_eq!(iter.next(), Some((u64::MAX, 64)));
        /// assert_eq!(iter.next(), None);
        /// ```
        iter_u64,
        IterU64
    );
    iter_unsigned!(
        /// Returns an iterator that iterates over the
        /// [`BitSlice`](BitSlice) 128 bits at a time. Each invocation
        /// of `iter.next` returns a u128 value and the number of bits
        /// read. The bits are read from the lower to the higher index
        /// from the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// The iterator returns None if there are no more bits to
        /// return
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u64(u64::MAX, Some(64));
        /// bv.push_u64(u64::MAX, Some(64));
        ///
        /// let s = &bv[..];
        /// let mut iter = s.iter_u128();
        /// assert_eq!(iter.next(), Some((u128::MAX, 128)));
        /// assert_eq!(iter.next(), None);
        /// ```
        iter_u128,
        IterU128
    );

    as_unsigned!(
        /// Returns the contents of this slice as a [`u8`]. This
        /// method will panic if the length of the slice is greater
        /// than or equal to 8. The bits are read from the lower to
        /// the higher index from the slice and shifted right, so the
        /// bit at the lower index is the MSB of returned value while
        /// the bit at the highest index is the LSB.
        ///
        /// Returns a [`u8`] value and the number of bits read as a
        /// tuple.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        ///
        /// let mut bv = BitVector::new();
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let s = &bv[..];
        /// assert_eq!(s.as_u8(), (0b0011_0110, 8));
        /// ```
        /// If a Result is preferred over a panic, then
        /// using the `TryFrom<&BitSlice>` trait may be used.
        ///
        /// # Example of `TryFrom<&BitSlice> for u8`
        ///
        /// ```
        /// use deepmesa::collections::BitVector;
        /// use core::convert::TryFrom;
        ///
        /// let mut bv = BitVector::new();
        /// bv.push_u8(0b0011_0110, Some(8));
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let s = &bv[0..8];
        /// match u8::try_from(s) {
        ///     Ok(val) => assert_eq!(val, 0b0011_0110),
        ///     Err(e) => assert!(false, "{}", e),
        /// }
        /// ```
        u8,
        8,
        as_u8
    );
    as_unsigned!(
        /// Returns the contents of this slice as a [`u16`]. This
        /// method will panic if the length of the slice is greater
        /// than or equal to 16. The bits are read from the lower to
        /// the higher index from the slice and shifted right, so the
        /// bit at the lower index is the MSB of returned value while
        /// the bit at the highest index is the LSB.
        ///
        /// Returns a [`u16`] value and the number of bits read as a
        /// tuple.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        ///
        /// let mut bv = BitVector::new();
        /// bv.push_u8(0b0011_0110, Some(8));
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let s = &bv[..];
        /// assert_eq!(s.as_u16(), (0b0011_0110_0011_0110, 16));
        /// ```
        ///
        /// If a Result is preferred over a panic, then
        /// using the `TryFrom<&BitSlice>` trait may be used.
        ///
        /// # Example of `TryFrom<&BitSlice> for u16`
        ///
        /// ```
        /// use deepmesa::collections::BitVector;
        /// use core::convert::TryFrom;
        ///
        /// let mut bv = BitVector::new();
        /// bv.push_u8(0b0011_0110, Some(8));
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let s = &bv[..];
        /// match u16::try_from(s) {
        ///     Ok(val) => assert_eq!(val, 0b0011_0110_0011_0110),
        ///     Err(e) => assert!(false, "{}", e),
        /// }
        /// ```
        u16,
        16,
        as_u16
    );
    as_unsigned!(
        /// Returns the contents of this slice as a [`u32`]. This
        /// method will panic if the length of the slice is greater
        /// than or equal to 32. The bits are read from the lower
        /// to the higher index from the slice and shifted right, so
        /// the bit at the lower index is the MSB of returned value
        /// while the bit at the highest index is the LSB.
        ///
        /// Returns a [`u32`] value and the number of bits read as a
        /// tuple.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        ///
        /// let mut bv = BitVector::new();
        /// bv.push_u32(u32::MAX, Some(32));
        ///
        /// let s = &bv[..];
        /// assert_eq!(s.as_u32(), (u32::MAX, 32));
        /// ```
        ///
        /// If a Result is preferred over a panic, then
        /// using the `TryFrom<&BitSlice>` trait may be used.
        ///
        /// # Example of `TryFrom<&BitSlice> for u32`
        ///
        /// ```
        /// use deepmesa::collections::BitVector;
        /// use core::convert::TryFrom;
        ///
        /// let mut bv = BitVector::new();
        /// bv.push_u32(u32::MAX, Some(32));
        ///
        /// let s = &bv[..];
        /// match u32::try_from(s) {
        ///     Ok(val) => assert_eq!(val, u32::MAX),
        ///     Err(e) => assert!(false, "{}", e),
        /// }
        /// ```
        u32,
        32,
        as_u32
    );
    as_unsigned!(
        /// Returns the contents of this slice as a [`u64`]. This
        /// method will panic if the length of the slice is greater
        /// than or equal to 64. The bits are read from the lower
        /// to the higher index from the slice and shifted right, so
        /// the bit at the lower index is the MSB of returned value
        /// while the bit at the highest index is the LSB.
        ///
        /// Returns a [`u64`] value and the number of bits read as a
        /// tuple.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        ///
        /// let mut bv = BitVector::new();
        /// bv.push_u64(u64::MAX, Some(64));
        ///
        /// let s = &bv[..];
        /// assert_eq!(s.as_u64(), (u64::MAX, 64));
        /// ```
        ///
        /// If a Result is preferred over a panic, then
        /// using the `TryFrom<&BitSlice>` trait may be used.
        ///
        /// # Example of `TryFrom<&BitSlice> for u64`
        ///
        /// ```
        /// use deepmesa::collections::BitVector;
        /// use core::convert::TryFrom;
        ///
        /// let mut bv = BitVector::new();
        /// bv.push_u64(u64::MAX, Some(64));
        ///
        /// let s = &bv[..];
        /// match u64::try_from(s) {
        ///     Ok(val) => assert_eq!(val, u64::MAX),
        ///     Err(e) => assert!(false, "{}", e),
        /// }
        /// ```
        u64,
        64,
        as_u64
    );
    as_unsigned!(
        /// Returns the contents of this slice as a [`u128`]. This
        /// method will panic if the length of the slice is greater
        /// than or equal to 128. The bits are read from the lower
        /// to the higher index from the slice and shifted right, so
        /// the bit at the lower index is the MSB of returned value
        /// while the bit at the highest index is the LSB.
        ///
        /// Returns a [`u128`] value and the number of bits read as a
        /// tuple.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        ///
        /// let mut bv = BitVector::new();
        /// bv.push_u128(u128::MAX, Some(128));
        ///
        /// let s = &bv[..];
        /// assert_eq!(s.as_u128(), (u128::MAX, 128));
        /// ```
        ///
        /// If a Result is preferred over a panic, then
        /// using the `TryFrom<&BitSlice>` trait may be used.
        ///
        /// # Example of `TryFrom<&BitSlice> for u128`
        ///
        /// ```
        /// use deepmesa::collections::BitVector;
        /// use core::convert::TryFrom;
        ///
        /// let mut bv = BitVector::new();
        /// bv.push_u128(u128::MAX, Some(128));
        ///
        /// let s = &bv[..];
        /// match u128::try_from(s) {
        ///     Ok(val) => assert_eq!(val, u128::MAX),
        ///     Err(e) => assert!(false, "{}", e),
        /// }
        /// ```
        u128,
        128,
        as_u128
    );

    read_unsigned!(
        /// Reads upto 8 bits from this [`BitSlice`](BitSlice) into
        /// a u8 starting at the specified `start` position. This
        /// method will panic if `start` is greater than or equal to
        /// the length of the slice.
        ///
        /// The bits are read from the lower to the higher index from
        /// the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let s = &bv[..];
        /// let (val, read) = s.read_u8(0);
        /// assert_eq!(read, 8);
        /// assert_eq!(val, 0b0011_0110);
        ///
        /// let (val, read) = s.read_u8(4);
        /// assert_eq!(read, 4);
        /// assert_eq!(val, 0b0000_0110);
        /// ```
        u8,
        8,
        read_u8
    );
    read_unsigned!(
        /// Reads upto 16 bits from this [`BitSlice`](BitSlice) into a
        /// u16 starting at the specified `start` position. This
        /// method will panic if `start` is greater than or equal to
        /// the length of the slice.
        ///
        /// The bits are read from the lower to the higher index from
        /// the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u16(0b0011_0110_1100_0011, Some(16));
        ///
        /// let s = &bv[..];
        /// let (val, read) = s.read_u16(0);
        /// assert_eq!(read, 16);
        /// assert_eq!(val, 0b0011_0110_1100_0011);
        ///
        /// let (val, read) = s.read_u16(4);
        /// assert_eq!(read, 12);
        /// assert_eq!(val, 0b0000_0110_1100_0011);
        /// ```
        u16,
        16,
        read_u16
    );
    read_unsigned!(
        /// Reads upto 32 bits from this [`BitSlice`](BitSlice) into
        /// a u32 starting at the specified `start` position. This
        /// method will panic if `start` is greater than or equal to
        /// the length of the slice.
        ///
        /// The bits are read from the lower to the higher index from
        /// the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u16(0b0011_0110_1100_0011, Some(16));
        /// bv.push_u16(0b1100_1010_0100_1100, Some(16));
        ///
        /// let s = &bv[..];
        /// let (val, read) = s.read_u32(0);
        /// assert_eq!(read, 32);
        /// assert_eq!(val, 0b0011_0110_1100_0011_1100_1010_0100_1100);
        ///
        /// let (val, read) = s.read_u16(16);
        /// assert_eq!(read, 16);
        /// assert_eq!(val, 0b1100_1010_0100_1100);
        /// ```
        u32,
        32,
        read_u32
    );
    read_unsigned!(
        /// Reads upto 64 bits from this [`BitSlice`](BitSlice) into
        /// a u64 starting at the specified `start` position. This
        /// method will panic if `start` is greater than or equal to
        /// the length of the slice.
        ///
        /// The bits are read from the lower to the higher index from
        /// the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u16(0b0011_0110_1100_0011, Some(16));
        /// bv.push_u16(0b1100_1010_0100_1100, Some(16));
        ///
        /// let s = &bv[..];
        /// let (val, read) = s.read_u64(20);
        /// assert_eq!(read, 12);
        //
        /// assert_eq!(val, 0b1010_0100_1100);
        ///
        /// let (val, read) = s.read_u64(16);
        /// assert_eq!(read, 16);
        /// assert_eq!(val, 0b1100_1010_0100_1100);
        /// ```
        u64,
        64,
        read_u64
    );
    read_unsigned!(
        /// Reads upto 128 bits from this [`BitSlice`](BitSlice)
        /// into a u128 starting at the specified `start`
        /// position. This method will panic if `start` is greater
        /// than or equal to the length of the slice.
        ///
        /// The bits are read from the lower to the higher index from
        /// the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u16(0b0011_0110_1100_0011, Some(16));
        /// bv.push_u16(0b1100_1010_0100_1100, Some(16));
        ///
        /// let s = &bv[..];
        /// let (val, read) = bv.read_u128(20);
        /// assert_eq!(read, 12);
        //
        /// assert_eq!(val, 0b1010_0100_1100);
        ///
        /// let (val, read) = s.read_u128(16);
        /// assert_eq!(read, 16);
        /// assert_eq!(val, 0b1100_1010_0100_1100);
        /// ```
        u128,
        128,
        read_u128
    );

    read_bits_unsigned!(
        /// Reads upto `max_bits` bits from this
        /// [`BitSlice`](BitSlice) into a u8 starting at the
        /// specified `start` position. This method will panic if
        /// `max_bits` is greater than 8 or if `start` is greater than
        /// or equal to the length of the slice.
        ///
        /// The bits are read from the lower to the higher index from
        /// the slice and shifted right, so the bit at the lower index
        /// is the MSB of returned value while the bit at the highest
        /// index is the LSB.
        ///
        /// Here is an illustrative example for a slice with 8
        /// bits.
        ///
        /// ```text
        ///   0 1 2 3 4 5 6 7
        /// [ 0,0,1,1,0,1,1,0 ]
        ///  MSB [_______] LSB
        ///       ^ Start = 2
        ///
        /// value read = 0b1101
        /// ```
        /// Reading 4 bits from the start position of 2, results in a
        /// u8 value of decimal 13.
        ///
        /// This method returns the read value as well as the number of
        /// bits read as a tuple.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// // Push 8 bits: 0b0011_0110
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let s = &bv[..];
        /// let (val, read) = s.read_bits_u8(2, 4);
        /// assert_eq!(read,4);
        /// assert_eq!(val, 0b0000_1101);
        /// assert_eq!(val, 13);
        /// ```
        u8,
        8,
        read_bits_u8
    );
    read_bits_unsigned!(
        /// Reads upto `max_bits` bits from this
        /// [`BitSlice`](BitSlice) into a u16 starting at the
        /// specified `start` position. This method will panic if
        /// `max_bits` is greater than 16 or if `start` is greater
        /// than or equal to the length of the slice.
        ///
        /// The bits are read from the lower to the higher index from
        /// the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// Here is an illustrative example for a slice with 8
        /// bits.
        ///
        /// ```text
        ///   0 1 2 3 4 5 6 7
        /// [ 0,0,1,1,0,1,1,0 ]
        ///  MSB [_______] LSB
        ///       ^ Start = 2
        ///
        /// value read = 0b1101
        /// ```
        /// Reading 4 bits from the start position of 2, results in a
        /// u16 value of decimal 13.
        ///
        /// This method returns the read value as well as the number of
        /// bits read as a tuple.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// // Push 8 bits: 0b0011_0110
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let s = &bv[..];
        /// let (val, read) = s.read_bits_u16(2, 4);
        /// assert_eq!(read,4);
        /// assert_eq!(val, 0b0000_1101);
        /// assert_eq!(val, 13);
        /// ```
        u16,
        16,
        read_bits_u16
    );
    read_bits_unsigned!(
        /// Reads upto `max_bits` bits from this
        /// [`BitSlice`](BitSlice) into a u32 starting at the
        /// specified `start` position. This method will panic if
        /// `max_bits` is greater than 32 or if `start` is greater
        /// than or equal to the length of the slice.
        ///
        /// The bits are read from the lower to the higher index from
        /// the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// Here is an illustrative example for a slice with 8
        /// bits.
        ///
        /// ```text
        ///   0 1 2 3 4 5 6 7
        /// [ 0,0,1,1,0,1,1,0 ]
        ///  MSB [_______] LSB
        ///       ^ Start = 2
        ///
        /// value read = 0b1101
        /// ```
        /// Reading 4 bits from the start position of 2, results in a
        /// u32 value of decimal 13.
        ///
        /// This method returns the read value as well as the number of
        /// bits read as a tuple.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// // Push 8 bits: 0b0011_0110
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let s = &bv[..];
        /// let (val, read) = s.read_bits_u32(2, 4);
        /// assert_eq!(read,4);
        /// assert_eq!(val, 0b0000_1101);
        /// assert_eq!(val, 13);
        /// ```
        u32,
        32,
        read_bits_u32
    );
    read_bits_unsigned!(
        /// Reads upto `max_bits` bits from this
        /// [`BitSlice`](BitSlice) into a u64 starting at the
        /// specified `start` position. This method will panic if
        /// `max_bits` is greater than 64 or if `start` is greater
        /// than or equal to the length of the slice.
        ///
        /// The bits are read from the lower to the higher index from
        /// the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// Here is an illustrative example for a slice with 8
        /// elements.
        ///
        /// ```text
        ///   0 1 2 3 4 5 6 7
        /// [ 0,0,1,1,0,1,1,0 ]
        ///  MSB [_______] LSB
        ///       ^ Start = 2
        ///
        /// value read = 0b1101
        /// ```
        /// Reading 4 bits from the start position of 2, results in a
        /// u64 value of decimal 13.
        ///
        /// This method returns the read value as well as the number of
        /// bits read as a tuple.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// // Push 8 bits: 0b0011_0110
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let s = &bv[..];
        /// let (val, read) = s.read_bits_u64(2, 4);
        /// assert_eq!(read,4);
        /// assert_eq!(val, 0b0000_1101);
        /// assert_eq!(val, 13);
        /// ```
        u64,
        64,
        read_bits_u64
    );
    read_bits_unsigned!(
        /// Reads upto `max_bits` bits from this
        /// [`BitSlice`](BitSlice) into a u128 starting at the
        /// specified `start` position. This method will panic if
        /// `max_bits` is greater than 128 or if `start` is greater
        /// than or equal to the length of the slice.
        ///
        /// The bits are read from the lower to the higher index from
        /// the slice and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// Here is an illustrative example for a slice with 8
        /// bits.
        ///
        /// ```text
        ///   0 1 2 3 4 5 6 7
        /// [ 0,0,1,1,0,1,1,0 ]
        ///  MSB [_______] LSB
        ///       ^ Start = 2
        ///
        /// value read = 0b1101
        /// ```
        /// Reading 4 bits from the start position of 2, results in a
        /// u128 value of decimal 13.
        ///
        /// This method returns the read value as well as the number of
        /// bits read as a tuple.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// // Push 8 bits: 0b0011_0110
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let s = &bv[..];
        /// let (val, read) = s.read_bits_u128(2, 4);
        /// assert_eq!(read,4);
        /// assert_eq!(val, 0b0000_1101);
        /// assert_eq!(val, 13);
        /// ```
        ///
        u128,
        128,
        read_bits_u128
    );
}

// Helpers and private methods
impl BitSlice {
    /// Returns the 3 most significant bits of the length
    #[inline(always)]
    pub(super) fn offset(&self) -> usize {
        slice_unpack_offset!(self.0.len())
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
        let mut bv = BitVector::with_capacity(20);
        bv.push_bits_u8(0b1100_1011, 8, BitOrder::Msb0);
        bv.push_bits_u8(0b1010_0101, 8, BitOrder::Msb0);

        //        let bv = &*bvec;
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
    #[allow(unused_assignments)]
    fn test_bit_not_0() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        s = !s;
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
        s &= false;
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
        bv.clear();
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        s &= true;
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
        s |= false;
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
        bv.clear();
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        s |= true;
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
        s ^= false;
        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
        bv.clear();
        bv.push_u8(0b1001_0011, Some(8));
        let mut s = &mut bv[2..2];
        assert_eq!(s.len(), 0);
        s ^= true;
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
        assert_eq!(s.len(), 25);

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

    #[test]
    fn test_get_mut() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1010_1101, None);

        let s = &mut bv[2..7];
        *s.get_mut(0).unwrap() = false;
        *s.get_mut(1).unwrap() = true;
        *s.get_mut(2).unwrap() = false;
        *s.get_mut(3).unwrap() = false;
        *s.get_mut(4).unwrap() = true;

        assert_eq!(bv.read_u8(0), (0b1001_0011, 8));
    }

    #[test]
    fn test_iter_mut() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1011_1100, None);
        assert_eq!(bv[0], true);
        let s = &mut bv[0..7];
        let iter = s.iter_mut();
        for mut bit in iter {
            *bit = true;
        }
        assert_eq!(bv.read_u8(0), (0b1111_1110, 8));

        let s = &mut bv[0..7];
        for mut bit in s.iter_mut() {
            *bit = false;
        }
        assert_eq!(bv.read_u8(0), (0b0000_0000, 8));
    }

    #[test]
    fn test_first() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1011_1100, None);
        assert_eq!(bv[0], true);
        let s = &bv[0..8];
        assert_eq!(*(s.first().unwrap()), true);
        assert_eq!(s.first().as_deref(), Some(&true));
        assert_eq!(bv[0], true);
    }

    #[test]
    fn test_first_mut() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1011_1100, None);
        assert_eq!(bv[0], true);
        let s = &mut bv[0..8];
        assert_eq!(*(s.first_mut().unwrap()), true);
        *s.first_mut().unwrap() = false;
        assert_eq!(*(s.first_mut().unwrap()), false);
        assert_eq!(s.first().as_deref(), Some(&false));
        assert_eq!(bv[0], false);
    }

    #[test]
    fn test_last() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1011_1100, None);
        assert_eq!(bv[7], false);
        let s = &bv[0..8];
        assert_eq!(*(s.last().unwrap()), false);
        assert_eq!(s.last().as_deref(), Some(&false));
        assert_eq!(bv[7], false);
    }

    #[test]
    fn test_last_mut() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b0000_0000, Some(8));
        assert_eq!(bv[7], false);
        let s = &mut bv[0..8];
        assert_eq!(*(s.last_mut().unwrap()), false);
        *s.last_mut().unwrap() = true;
        assert_eq!(*(s.last().unwrap()), true);
        assert_eq!(s.last().as_deref(), Some(&true));
        assert_eq!(bv[7], true);
    }

    #[test]
    fn test_iter_ones() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1100_1010_0011_0101, None);
        bv.push_u16(0b1000_1100_0011_1111, None);
        let s = &bv[2..2];
        let mut iter = s.iter_ones();
        assert_eq!(iter.next(), None);

        let s = &bv[2..4];
        let mut iter = s.iter_ones();
        assert_eq!(iter.next(), None);

        let s = &bv[2..19];
        let mut iter = s.iter_ones();
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(8));
        assert_eq!(iter.next(), Some(9));
        assert_eq!(iter.next(), Some(11));
        assert_eq!(iter.next(), Some(13));
        assert_eq!(iter.next(), Some(14));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_zeros() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b0011_0101_1100_1010, Some(16));
        bv.push_u16(0b0111_0011_1100_0000, Some(16));

        let s = &bv[2..2];

        let mut iter = s.iter_zeros(); //IterZeros::new(&s.0, s.offset(), s.len());
        assert_eq!(iter.next(), None);

        let s = &bv[2..4];
        let mut iter = s.iter_zeros(); //IterZeros::new(&s.0, s.offset(), s.len());
        assert_eq!(iter.next(), None);

        let s = &bv[2..19];
        let mut iter = s.iter_zeros(); //IterZeros::new(&s.0, s.offset(), s.len());
        assert_eq!(iter.next(), Some(2));
        assert_eq!(iter.next(), Some(4));
        assert_eq!(iter.next(), Some(8));
        assert_eq!(iter.next(), Some(9));
        assert_eq!(iter.next(), Some(11));
        assert_eq!(iter.next(), Some(13));
        assert_eq!(iter.next(), Some(14));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_count_ones() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1111_1000, Some(8));
        bv.push_u8(0b0011_1000, Some(8));

        let s = &bv[4..10];
        assert_eq!(s.count_ones(), 1);

        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1110_1111, Some(8));
        let s = &bv[2..6];
        assert_eq!(s.count_ones(), 3);
    }
}
