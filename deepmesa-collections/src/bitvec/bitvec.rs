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
    bitslice::BitPtr,
    bitslice::BitSlice,
    iter::{Iter, IterU128, IterU16, IterU32, IterU64, IterU8},
    traits::{BitwiseClear, BitwiseClearAssign},
    BitCount, BitOrder, BitOrderConvert,
};
use core::fmt;
use core::fmt::Debug;
use core::ops::BitAnd;
use core::ops::BitAndAssign;
use core::ops::BitOr;
use core::ops::BitOrAssign;
use core::ops::BitXor;
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

#[macro_export]
macro_rules! bitvec {
    () => {
        BitVector::new();
    };
    ($($arg:tt)*) => {{
        let slice = [$($arg)*];
        let mut bv = BitVector::new();
        for item in &slice {
            match item {
                0 => bv.push(false),
                1 => bv.push(true),
                _ => panic!("{} is not a binary digit", item),
            }
        }
        bv
    };};
    ($item: expr, $len: expr) => {
        {
            match $item {
                0=> BitVector::repeat(false, $len),
                1=> BitVector::repeat(true, $len),
                _ => panic!("{} is not a binary digit", item),
            }
        }
    };
}

/// A fast contiguous growable array of bits allocated on the heap
/// that allows storing and manipulating an arbitrary number of
/// bits. This collection is backed by a Vector<u8> which manages the
/// underlying memory.
///
/// # Getting Started
/// To get started add the deepmesa dependency to Cargo.toml and the
/// use declaration in your source.
///
/// ```text
/// [dependencies]
/// deepmesa = "0.6.0"
/// ```
///
/// ```
/// use deepmesa::collections::BitVector;
///
/// let mut bv = BitVector::with_capacity(128);
/// bv.push(true);
/// bv.push(false);
/// bv.push(true);
///
/// assert_eq!(bv.get(0), Some(true));
/// assert_eq!(bv.get(1), Some(false));
/// assert_eq!(bv.get(2), Some(true));
/// ```
pub struct BitVector {
    pub(super) bits: Vec<u8>,
    pub(super) capacity_bits: usize,
    pub(super) bit_len: usize,
}

//Set the bits after bit_len in the last byte to 0
macro_rules! clr_lsb_last_byte {
    ($self: ident) => {
        ($self.bits[($self.bit_len - 1) / 8]).clear_lsb_assign((7 - ($self.bit_len - 1) % 8) as u8);
    };
}

macro_rules! iter_unsigned {
    ($iter_fn: ident, $iter_type: ident) => {
        pub fn $iter_fn(&self) -> $iter_type {
            $iter_type::new(&self.bits, 0, self.bit_len)
        }
    };
}

macro_rules! check_push_bounds {
    ($t: ty, $sz:literal, $bit_count: ident) => {
        if $bit_count > $sz {
            panic!(
                concat!(
                    "cannot push more than ",
                    $sz,
                    " bits from a ",
                    stringify!($t),
                    ". bit_count={}"
                ),
                $bit_count
            );
        }
    };
}

macro_rules! push_bits_unsigned {
    ($i:ident, $sz: literal, $push_bits_fn: ident) => {
        pub fn $push_bits_fn(&mut self, val: $i, bit_count: BitCount, order: BitOrder) -> BitCount {
            if bit_count == 0 {
                return 0;
            }

            check_push_bounds!($i, $sz, bit_count);

            match order {
                BitOrder::Msb0 => self.push_bits_msb0((val as u128).lsb0_to_msb0($sz), bit_count),
                BitOrder::Lsb0 => {
                    self.push_bits_msb0((val as u128).lsb0_to_msb0(bit_count), bit_count)
                }
            }
        }
    };
}

macro_rules! push_unsigned {
    ($i:ident, $b: literal, $push_fn: ident) => {
        pub fn $push_fn(&mut self, val: $i, min_width: Option<BitCount>) -> BitCount {
            let mut count = $b - val.leading_zeros() as usize;
            match min_width {
                None => {}
                Some(width) => {
                    if width > count {
                        if width > $b {
                            self.fill(false, width - $b);
                            //fill with zeros (width - $b)
                            count = $b;
                            //bits = $b
                        } else {
                            //implicit: if width <= $b
                            count = width;
                            //bits = width
                        }
                    }
                }
            }

            self.push_bits_msb0((val as u128).lsb0_to_msb0(count), count)
        }
    };
}

macro_rules! read_unsigned {
    ($i:ident, $b: literal, $read_fn: ident) => {
        pub fn $read_fn(&self, start: usize) -> ($i, BitCount) {
            start_bounds_check!(start, self.bit_len);
            let (val, bit_count) = BitSlice::read_bits_lsb0(&self.bits, start, self.bit_len, $b);
            (val as $i, bit_count)
        }
    };
}

macro_rules! read_bits_unsigned {
    ($i:ident, $b: literal, $read_bits_fn: ident) => {
        pub fn $read_bits_fn(&self, start: usize, max_bits: BitCount) -> ($i, BitCount) {
            start_bounds_check!(start, self.bit_len);

            if max_bits > $b {
                panic!(
                    "cannot read more than $b bits into a $i. max_bits={}",
                    max_bits
                );
            }
            let (val, bit_count) =
                BitSlice::read_bits_lsb0(&self.bits, start, self.bit_len, max_bits);
            (val as $i, bit_count)
        }
    };
}

const U128_BITS: u8 = 128;

impl BitVector {
    /// Creates an empty BitVector with a capacity or 128 bits.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// let bv = BitVector::new();
    /// assert_eq!(bv.capacity(), 128);
    /// ```
    pub fn new() -> BitVector {
        BitVector::with_capacity(128)
    }

    /// Creates an empty BitVector with the specified capacity. If the
    /// specified capacity is not a multiple of 8, it is increased to
    /// be a multiple of 8
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// let bv = BitVector::with_capacity(6);
    /// assert_eq!(bv.capacity(), 8);
    /// ```
    pub fn with_capacity(capacity_bits: usize) -> BitVector {
        BitVector {
            bits: Vec::with_capacity((capacity_bits + 7) / 8),
            capacity_bits: ((capacity_bits + 7) / 8) * 8,
            bit_len: 0,
        }
    }
    /// Returns the number of bits this BitVector can hold before new
    /// memory is allocated.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// let bv = BitVector::with_capacity(22);
    /// assert_eq!(bv.capacity(), 24);
    /// ```
    pub fn capacity(&self) -> usize {
        self.capacity_bits
    }

    /// Returns the number of bits in the bitvector
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// let mut bv = BitVector::with_capacity(22);
    /// for _ in 0..5 {
    ///     bv.push(true);
    /// }
    /// assert_eq!(bv.len(), 5);
    /// ```
    pub fn len(&self) -> usize {
        self.bit_len
    }

    /// Returns true if the vector contains no bits.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// let mut bv = BitVector::with_capacity(22);
    /// assert!(bv.is_empty());
    /// bv.push(true);
    /// assert!(!bv.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.bit_len == 0
    }

    /// Clears the vector, removing all the bits. This method has no
    /// effect on the allocated capacity of the vector.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// let mut bv = BitVector::with_capacity(22);
    /// for _ in 0..5 {
    ///     bv.push(true);
    /// }
    /// assert_eq!(bv.len(), 5);
    /// bv.clear();
    /// assert_eq!(bv.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.bits.clear();
        self.bit_len = 0;
    }

    pub fn truncate(&mut self, len: usize) {
        if len == 0 {
            self.clear();
            return;
        }
        if len >= self.bit_len {
            return;
        }
        self.bits.truncate(((len - 1) / 8) + 1);
        self.bit_len = len;
        clr_lsb_last_byte!(self)
    }

    pub fn iter(&self) -> Iter {
        Iter::new(&self.bits, 0, self.bit_len)
    }

    iter_unsigned!(iter_u8, IterU8);
    iter_unsigned!(iter_u16, IterU16);
    iter_unsigned!(iter_u32, IterU32);
    iter_unsigned!(iter_u64, IterU64);
    iter_unsigned!(iter_u128, IterU128);

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

    push_bits_unsigned!(u8, 8, push_bits_u8);
    push_bits_unsigned!(u16, 16, push_bits_u16);
    push_bits_unsigned!(u32, 32, push_bits_u32);
    push_bits_unsigned!(u64, 64, push_bits_u64);
    push_bits_unsigned!(u128, 128, push_bits_u128);

    push_unsigned!(u8, 8, push_u8);
    push_unsigned!(u16, 16, push_u16);
    push_unsigned!(u32, 32, push_u32);
    push_unsigned!(u64, 64, push_u64);
    push_unsigned!(u128, 128, push_u128);

    pub fn as_bitslice(&self) -> &BitSlice {
        self.index(0..self.bit_len)
    }

    pub fn as_mut_bitslice(&mut self) -> &mut BitSlice {
        self.index_mut(0..self.bit_len)
    }

    pub fn as_raw_slice(&self) -> &[u8] {
        unsafe {
            let ptr = self.bits.as_ptr();
            std::slice::from_raw_parts(ptr, self.bits.len())
        }
    }

    pub fn as_mut_raw_slice(&mut self) -> &mut [u8] {
        unsafe {
            let ptr = self.bits.as_mut_ptr();
            std::slice::from_raw_parts_mut(ptr, self.bits.len())
        }
    }

    pub fn as_raw_ptr(&self) -> *const u8 {
        self.bits.as_ptr()
    }

    pub fn as_mut_raw_ptr(&mut self) -> *const u8 {
        self.bits.as_mut_ptr()
    }

    pub fn append(&mut self, other: &mut BitVector) {
        let mut iter = other.iter_u8();
        while let Some((val, bitcount)) = iter.next() {
            self.push_u8(val, Some(bitcount));
        }

        other.clear()
    }

    pub fn extend_from_bitslice(&mut self, other: &BitSlice) {
        let mut iter = other.iter_u8();
        while let Some((val, bitcount)) = iter.next() {
            self.push_u8(val, Some(bitcount));
        }
    }

    pub fn from_bitslice(slice: &BitSlice) -> Self {
        let mut bv = BitVector::with_capacity(slice.len());
        let mut iter = slice.iter_u8();
        while let Some((val, bitcount)) = iter.next() {
            bv.push_u8(val, Some(bitcount));
        }
        bv
    }

    pub fn repeat(bit: bool, len: usize) -> Self {
        let mut bv = BitVector::with_capacity(len);
        bv.fill(bit, len);
        bv
    }
    /// Sets the bit at the given index to 1 if bit is true, otherwise
    /// clears it. Panic if the index exceeds the length
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(22);
    /// bv.push(true);
    /// bv.push(false);
    /// bv.push(true);
    /// assert_eq!(bv[0], true);
    /// assert_eq!(bv[1], false);
    /// assert_eq!(bv[2], true);
    /// bv.set(0, false);
    /// bv.set(1, true);
    /// bv.set(2, false);
    /// assert_eq!(bv[0], false);
    /// assert_eq!(bv[1], true);
    /// assert_eq!(bv[2], false);
    /// ```
    pub fn set(&mut self, index: usize, value: bool) {
        if index >= self.len() {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            );
        }

        set_unchecked!(index, value, &mut self.bits);
    }

    /// Returns a boolean value indicating whether the bit at the
    /// specified index is set or None if the index exceeds the number
    /// of bits in the BitVector.
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(22);
    /// bv.push(true);
    /// bv.push(true);
    /// bv.push(false);
    /// assert_eq!(bv.get(0), Some(true));
    /// assert_eq!(bv.get(1), Some(true));
    /// assert_eq!(bv.get(2), Some(false));
    /// assert_eq!(bv.get(3), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<bool> {
        if index >= self.len() {
            return None;
        }

        get_unchecked!(index, self.bits);
    }

    pub fn get_mut(&mut self, index: usize) -> Option<BitPtr> {
        if let Some(bit) = self.get(index) {
            return Some(BitPtr::new(bit, &mut self.bits, index));
        }
        return None;
    }

    /// Pushes a single bit to the end of the BitVector.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(22);
    /// bv.push(true);
    /// bv.push(false);
    /// assert_eq!(bv[0], true);
    /// assert_eq!(bv[1], false);
    /// ```
    pub fn push(&mut self, bit: bool) {
        if bit {
            self.push_bits_msb0(u128::MAX, 1);
        } else {
            self.push_bits_msb0(0, 1);
        }
    }

    /// Removes the last bit from the BitVector or None if its empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(22);
    /// bv.push(true);
    /// bv.push(false);
    /// bv.push(true);
    /// assert_eq!(bv.get(0), Some(true));
    /// assert_eq!(bv.get(1), Some(false));
    /// assert_eq!(bv.get(2), Some(true));
    /// assert_eq!(bv.pop(), Some(true));
    /// assert_eq!(bv.get(2), None);
    /// ```
    pub fn pop(&mut self) -> Option<bool> {
        if self.bit_len == 0 {
            return None;
        }
        let retval = self.get(self.bit_len - 1);
        let pos: u8 = ((self.bit_len - 1) % 8) as u8;

        if pos == 0 {
            self.bits.pop();
        } else {
            self.bits[(self.bit_len - 1) / 8].clear_msb_nth_assign(pos);
        }
        self.bit_len -= 1;
        retval
    }

    pub fn fill(&mut self, bit: bool, count: usize) -> BitCount {
        let mut push_val: u128 = 0;
        if bit {
            push_val = u128::MAX;
        }
        let mut rem = count;
        let mut total_pushed = 0;
        while rem > 0 {
            let mut push_ct = rem;
            if push_ct > 128 {
                push_ct = 128;
            }
            let pushed = self.push_bits_msb0(push_val, push_ct);
            total_pushed += pushed;
            rem -= pushed;
        }
        total_pushed
    }
}

impl Debug for BitVector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "BitVec {{ bit_len: {}, capacity_bits: {}, bits:\n",
            self.bit_len, self.capacity_bits
        )?;

        let mut count = 0;
        write!(f, "{{")?;
        for byte in self.bits.iter() {
            if count % 4 == 0 {
                write!(f, "\n    ")?;
            }
            write!(f, "{:08b} ", byte)?;
            count += 1;
        }
        write!(f, "\n}}}}")?;
        Ok(())
    }
}

impl Index<usize> for BitVector {
    type Output = bool;
    fn index(&self, index: usize) -> &Self::Output {
        match self.get(index) {
            None => {
                panic!(
                    "index out of bounds: the len is {} but the index is {}",
                    self.bit_len, index
                );
            }
            Some(true) => &true,
            Some(false) => &false,
        }
    }
}

impl Deref for BitVector {
    type Target = BitSlice;
    fn deref(&self) -> &Self::Target {
        &self[0..self.len()]
    }
}

impl DerefMut for BitVector {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let len = self.len();
        &mut self[0..len]
    }
}

impl Not for BitVector {
    type Output = Self;
    fn not(mut self) -> Self::Output {
        if self.bit_len == 0 {
            return self;
        }

        for byte in self.bits.iter_mut() {
            *byte = !*byte;
        }

        clr_lsb_last_byte!(self);
        self
    }
}

macro_rules! impl_bitwise {
    ($t_name: ident, $fn_name: ident, $rhs: ty, $for: ty, $op: tt) => {
        impl $t_name<$rhs> for $for {
            type Output = Self;
            fn $fn_name(mut self, rhs: $rhs) -> Self::Output {
                b_expr!(self $op rhs);
                self
            }
        }
    };
}

// impl BitAnd<BitVector> for BitVector
impl_bitwise!(BitAnd, bitand, BitVector, BitVector, &=);
// impl BitAnd<&BitVector> for BitVector
impl_bitwise!(BitAnd, bitand, &BitVector, BitVector, &=);
// impl BitAnd<&BitSlice> for BitVector
impl_bitwise!(BitAnd, bitand, &BitSlice, BitVector, &=);

// impl BitOr<BitVector> for BitVector
impl_bitwise!(BitOr, bitor, BitVector, BitVector, |=);
// impl BitOr<&BitVector> for BitVector
impl_bitwise!(BitOr, bitor, &BitVector, BitVector, |=);
// impl BitOr<&BitSlice> for BitVector
impl_bitwise!(BitOr, bitor, &BitSlice, BitVector, |=);

// impl BitXor<BitVector> for BitVector
impl_bitwise!(BitXor, bitxor, BitVector, BitVector, ^=);
// impl BitXor<&BitVector> for BitVector
impl_bitwise!(BitXor, bitxor, &BitVector, BitVector, ^=);
// impl BitXor<&BitSlice> for BitVector
impl_bitwise!(BitXor, bitxor, &BitSlice, BitVector, ^=);

macro_rules! impl_bitwise_bool {
    ($t_name: ident, $fn_name: ident, $for: ty, $op:tt) => {
        impl $t_name<bool> for $for {
            type Output = Self;
            fn $fn_name(mut self, rhs: bool) -> Self::Output {
                b_expr!(self $op rhs);
                self
            }
        }
    };
}

impl_bitwise_bool!(BitOr, bitor, BitVector, |=);
impl_bitwise_bool!(BitAnd, bitand, BitVector, &=);
impl_bitwise_bool!(BitXor, bitxor, BitVector, ^=);

macro_rules! impl_bitwise_assign {
    ($t_name: ident, $fn_name: ident, $rhs: ty, $for: ty, $op: tt) => {
        impl $t_name<$rhs> for $for {
            fn $fn_name(&mut self, rhs: $rhs) {
                if self.bit_len == 0 {
                    return;
                }

                let mut s_iter = rhs.iter_u8();
                for byte in self.bits.iter_mut() {
                    if let Some((s_byte, s_bits)) = s_iter.next() {
                        if s_bits == 8 {
                            b_expr!(*byte $op s_byte);
                        } else {
                            b_expr!(*byte $op (s_byte).lsb0_to_msb0(s_bits));
                        }
                    } else {
                        break;
                    }
                }

                clr_lsb_last_byte!(self);
            }
        }
    };
}

//impl BitAndAssign<BitVector> for BitVector
impl_bitwise_assign!(BitAndAssign, bitand_assign, BitVector, BitVector, &=);
//impl BitAndAssign<&BitVector> for BitVector
impl_bitwise_assign!(BitAndAssign, bitand_assign, &BitVector, BitVector, &=);
//impl BitAndAssign<&BitSlice> for BitVector
impl_bitwise_assign!(BitAndAssign, bitand_assign, &BitSlice, BitVector, &=);

//impl BitOrAssign<BitVector> for BitVector {
impl_bitwise_assign!(BitOrAssign, bitor_assign, BitVector, BitVector, |=);
//impl BitOrAssign<&BitVector> for BitVector {
impl_bitwise_assign!(BitOrAssign, bitor_assign, &BitVector, BitVector, |=);
//impl BitOrAssign<&BitSlice> for BitVector {
impl_bitwise_assign!(BitOrAssign, bitor_assign, &BitSlice, BitVector, |=);

//impl BitXorAssign<BitVector> for BitVector {
impl_bitwise_assign!(BitXorAssign, bitxor_assign, BitVector, BitVector, ^=);
//impl BitXorAssign<&BitVector> for BitVector {
impl_bitwise_assign!(BitXorAssign, bitxor_assign, &BitVector, BitVector, ^=);
//impl BitXorAssign<&BitSlice> for BitVector {
impl_bitwise_assign!(BitXorAssign, bitxor_assign, &BitSlice, BitVector, ^=);

macro_rules! impl_bitwise_assign_bool {
    ($t_name: ident, $fn_name: ident, $for: ty, $op: tt) => {
        impl $t_name<bool> for $for {
            fn $fn_name(&mut self, rhs: bool) {
                if self.bit_len == 0 {
                    return;
                }
                let mut and_val: u8 = 0;
                if rhs {
                    and_val = u8::MAX;
                }
                for byte in self.bits.iter_mut() {
                    b_expr!(*byte $op and_val);
                }

                clr_lsb_last_byte!(self);
            }
        }
    };
}

impl_bitwise_assign_bool!(BitAndAssign, bitand_assign, BitVector, &=);
impl_bitwise_assign_bool!(BitOrAssign, bitor_assign, BitVector, |=);
impl_bitwise_assign_bool!(BitXorAssign, bitxor_assign, BitVector, ^=);

impl AsMut<BitSlice> for BitVector {
    fn as_mut(&mut self) -> &mut BitSlice {
        self.index_mut(0..self.bit_len)
    }
}

impl AsRef<BitSlice> for BitVector {
    fn as_ref(&self) -> &BitSlice {
        self.index(0..self.bit_len)
    }
}

impl Default for BitVector {
    fn default() -> Self {
        Self::new()
    }
}

impl_index_range!(BitVector, BitVector, bits);
impl_index_range_mut!(BitVector, BitVector, bits);

//Private and Helper methods
impl BitVector {
    /// Pushes `bit_count` bits in the specified u128 into the vector
    /// starting from the msb.
    fn push_bits_msb0(&mut self, val: u128, bit_count: BitCount) -> BitCount {
        debug_assert!(
            bit_count <= 128,
            "cannot push more than 128 bits from a u128. count={}",
            bit_count
        );

        if bit_count == 0 {
            return 0;
        }
        let mut len_b = U128_BITS;
        let mut rem = bit_count as u8;

        // Calculate the number of partial bits in the last byte.
        let partial_bits = (self.bit_len % 8) as u8;

        //if push_ct is 1 thru 7 then do this. If its 0 then push a
        // whole byte, if its 8 then push 8 bits (aka whole byte)

        if partial_bits > 0 {
            let push_ct = 8 - partial_bits;
            let mut byte: u8 = bitops::ls_byte(val >> (len_b - 8));
            if push_ct > rem {
                byte.clear_lsb_assign(8 - rem);
                rem = 0;
            } else {
                len_b -= push_ct;
                rem -= push_ct;
            }
            bitops::shl_into(&mut self.bits[(self.bit_len - 1) / 8], byte, push_ct);
        }

        while rem >= 8 {
            // Get the 8 bits of val from the MSB end (shift val right
            // then get the LSB 8 bits)
            let byte: u8 = bitops::ls_byte(val >> (len_b - 8));
            len_b -= 8;
            rem -= 8;
            self.bits.push(byte);
        }

        if rem > 0 {
            // Get the 8 bits of val from the MSB end (shift val right
            // then get the LSB 8 bits)
            let byte: u8 = bitops::ls_byte(val >> (len_b - 8));
            //clear out the 8-rem lsb bits of the byte
            self.bits.push(byte.clear_lsb(8 - rem));
        }
        self.bit_len += bit_count as usize;
        bit_count
    }
}

#[cfg(test)]
impl BitVector {
    #[cfg(test)]
    fn len_bytes(&self) -> usize {
        self.bits.len()
    }

    #[cfg(test)]
    fn byte_at(&self, byte_index: usize) -> Option<u8> {
        self.bits.get(byte_index).cloned()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_at() {
        let mut bv = BitVector::with_capacity(32);
        //push a byte = 0101_0011
        bv.push_bits_u8(0b0101_0011, 8, BitOrder::Lsb0);
        assert_eq!(bv.get(0).unwrap(), false);
        assert_eq!(bv.get(1).unwrap(), true);
        assert_eq!(bv.get(2).unwrap(), false);
        assert_eq!(bv.get(3).unwrap(), true);
        assert_eq!(bv.get(4).unwrap(), false);
        assert_eq!(bv.get(5).unwrap(), false);
        assert_eq!(bv.get(6).unwrap(), true);
        assert_eq!(bv.get(7).unwrap(), true);

        //push another byte = 1100_1011
        bv.push_bits_u8(0b1100_1011, 8, BitOrder::Lsb0);
        assert_eq!(bv.get(8).unwrap(), true);
        assert_eq!(bv.get(9).unwrap(), true);
        assert_eq!(bv.get(10).unwrap(), false);
        assert_eq!(bv.get(11).unwrap(), false);
        assert_eq!(bv.get(12).unwrap(), true);
        assert_eq!(bv.get(13).unwrap(), false);
        assert_eq!(bv.get(14).unwrap(), true);
        assert_eq!(bv.get(15).unwrap(), true);

        assert_eq!(bv.get(18), None);
    }

    #[test]
    fn test_push_byte() {
        let mut bv = BitVector::with_capacity(32);
        assert_eq!(bv.len(), 0);
        assert_eq!(bv.len_bytes(), 0);
        assert_eq!(bv.bit_len, 0);
        bv.push_bits_u8(0b0110_0000, 8, BitOrder::Lsb0);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.bit_len, 8);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.len_bytes(), 1);
        //now artifically set the bit_len to 3 to indicate that
        // there are only 3 buts in the bitvec
        bv.bit_len = 3;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.len_bytes(), 1);
        assert_eq!(bv.bit_len, 3);

        //now push another byte and ensure that the correct bits are
        // set
        bv.push_bits_u8(0b0110_1001, 8, BitOrder::Lsb0);
        assert_eq!(bv.len(), 11);
        assert_eq!(bv.len_bytes(), 2);
        assert_eq!(bv.bit_len, 11);
        assert!(bv.byte_at(0).is_some());
        assert!(bv.byte_at(1).is_some());
        assert_eq!(
            bv.byte_at(0).unwrap(), //Goober
            0b0110_1101,
            "Found {:08b}",
            bv.byte_at(0).unwrap()
        );

        assert_eq!(
            bv.byte_at(1).unwrap(),
            0b0010_0000,
            "Found {:08b} at byte(1)",
            bv.byte_at(1).unwrap()
        );
    }

    //test pushing bits in 8 bit multiples
    #[test]
    fn test_push_bits_8_multiple() {
        let mut bv = BitVector::with_capacity(32);
        assert_eq!(bv.len(), 0);
        assert_eq!(bv.bit_len, 0);
        bv.fill(true, 8);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.bit_len, 8);
        for i in 0..8 {
            assert_eq!(bv.get(i).unwrap(), true);
        }
        assert_eq!(bv.byte_at(0).unwrap(), 0b1111_1111);
        assert_eq!(bv.byte_at(1), None);
        //now push a byte of zeros
        bv.fill(false, 8);
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.bit_len, 16);
        for i in 8..16 {
            assert_eq!(bv.get(i).unwrap(), false);
        }
        assert_eq!(bv.byte_at(1).unwrap(), 0b0000_0000);
        assert_eq!(bv.byte_at(2), None);
    }

    #[test]
    fn test_fill() {
        let mut bv = BitVector::with_capacity(32);
        assert_eq!(bv.len(), 0);
        assert_eq!(bv.bit_len, 0);
        bv.fill(true, 1);
        assert_eq!(bv.len(), 1);
        assert_eq!(bv.get(0).unwrap(), true);
        assert_eq!(bv.get(1), None);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1000_0000);
        assert_eq!(bv.byte_at(1), None);

        bv.fill(false, 2);
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.get(0).unwrap(), true);
        assert_eq!(bv.get(1).unwrap(), false);
        assert_eq!(bv.get(2).unwrap(), false);
        assert_eq!(bv.get(3), None);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1000_0000);
        assert_eq!(bv.byte_at(1), None, "Found {:08b}", bv.byte_at(1).unwrap());

        let val = 0b0110_0011;
        bv.push_bits_u8(val, 8, BitOrder::Lsb0);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1000_1100);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0110_0000);
        assert_eq!(bv.byte_at(2), None);
        //        assert_eq!(val << 3, 0b0001_1000);
        // lts3 = 011 0001_1000
        assert_eq!(bv.len(), 11);
        assert_eq!(bv.bit_len, 11);

        assert_eq!(bv.get(0).unwrap(), true);
        assert_eq!(bv.get(1).unwrap(), false);
        assert_eq!(bv.get(2).unwrap(), false);

        assert_eq!(bv.get(3).unwrap(), false);
        assert_eq!(bv.get(4).unwrap(), true);
        assert_eq!(bv.get(5).unwrap(), true);
        assert_eq!(bv.get(6).unwrap(), false);

        assert_eq!(bv.get(7).unwrap(), false);
        assert_eq!(bv.get(8).unwrap(), false);
        assert_eq!(bv.get(9).unwrap(), true);
        assert_eq!(bv.get(10).unwrap(), true);
        assert_eq!(bv.get(11), None);
        assert_eq!(bv.get(12), None);
        assert_eq!(bv.get(9282), None);
    }

    #[test]
    fn test_push_100_bits() {
        let mut bv = BitVector::with_capacity(1);
        assert_eq!(bv.len(), 0);
        assert_eq!(bv.bit_len, 0);
        bv.fill(true, 100);
        assert_eq!(bv.len(), 100);
        for i in 0..100 {
            assert_eq!(bv.get(i).unwrap(), true);
        }
        assert_eq!(bv.get(100), None);
    }

    #[test]
    #[should_panic(expected = "cannot push more than 8 bits from a u8. bit_count=10")]
    fn test_push_bits_u8_panic() {
        let mut bv = BitVector::with_capacity(20);
        let val = 0b1010_1000;

        bv.push_bits_u8(val, 10, BitOrder::Msb0);
    }

    #[test]
    fn test_push_bits() {
        let mut bv = BitVector::with_capacity(20);
        let val: u8 = 0b1100_1010;
        bv.push_bits_u8(val, 0, BitOrder::Msb0);
        assert_eq!(bv.len(), 0);
        assert_eq!(bv.byte_at(0), None);

        bv.push_bits_u8(val, 3, BitOrder::Msb0);
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1100_0000);

        //now push 3 more
        bv.push_bits_u8(val, 3, BitOrder::Msb0);
        assert_eq!(bv.len(), 6);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1000);

        //now push 0 bits of a byte again
        bv.push_bits_u8(val, 0, BitOrder::Msb0);
        assert_eq!(bv.len(), 6);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1000);

        let val: u8 = 0b1010_0011;
        bv.push_bits_u8(val, 8, BitOrder::Msb0);
        assert_eq!(bv.len(), 14);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1010);
        assert_eq!(bv.byte_at(1).unwrap(), 0b1000_1100);
        assert_eq!(bv.byte_at(2), None);
    }

    #[test]
    #[should_panic(expected = "cannot push more than 8 bits from a u8. bit_count=11")]
    fn test_push_bits_u8_trailing_panic() {
        let mut bv = BitVector::with_capacity(20);
        let val = 0b1010_1000;

        bv.push_bits_u8(val, 11, BitOrder::Lsb0);
    }

    #[test]
    fn test_push_bits_u8_trailing() {
        let mut bv = BitVector::with_capacity(20);
        let val = 0b1010_0011;

        bv.push_bits_u8(val, 0, BitOrder::Lsb0);
        assert_eq!(bv.len(), 0);

        bv.push_bits_u8(val, 3, BitOrder::Lsb0);
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.byte_at(0).unwrap(), 0b0110_0000);

        //Now push another 8 bits
        let val = 0b0101_1100;
        bv.push_bits_u8(val, 8, BitOrder::Lsb0);
        assert_eq!(bv.len(), 11);
        assert_eq!(bv.byte_at(0).unwrap(), 0b0110_1011);
        assert_eq!(bv.byte_at(1).unwrap(), 0b1000_0000);
        assert_eq!(bv.byte_at(2), None);
    }

    #[test]
    #[should_panic(expected = "cannot push more than 128 bits from a u128. bit_count=300")]
    fn test_push_u128_panic() {
        let mut bv = BitVector::with_capacity(20);
        let val = 0b0110_1000;
        bv.push_bits_u128(val, 300, BitOrder::Msb0);
    }

    #[test]
    fn test_push_usize_trailing() {
        let mut bv = BitVector::with_capacity(20);
        let val = 0b0110_1010;

        //first push 0 bits
        bv.push_bits_u128(val, 0, BitOrder::Lsb0);

        assert_eq!(bv.len(), 0);

        //first push only 3 bits
        bv.push_bits_u128(val, 3, BitOrder::Lsb0);
        assert_eq!(bv.len(), 3);
        assert_eq!(
            bv.byte_at(0).unwrap(),
            0b0100_0000,
            "val={}/{:08b}, enc={}/{:08b}",
            val,
            val,
            bv.byte_at(0).unwrap(),
            bv.byte_at(0).unwrap()
        );
        assert_eq!(bv.byte_at(1), None);
    }

    #[test]
    fn test_push_bits_u8() {
        let mut bv = BitVector::with_capacity(20);
        let val = 0b0110_1000;

        //first push 0 bits
        assert_eq!(bv.push_bits_u8(val, 0, BitOrder::Msb0), 0);
        assert_eq!(bv.len(), 0);

        //first push only 3 bits
        assert_eq!(bv.push_bits_u8(val, 3, BitOrder::Msb0), 3);
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.byte_at(0).unwrap(), 0b01100_000);
        assert_eq!(bv.byte_at(1), None);

        //now push 8 bits
        let val2 = 0b1100_0011;
        assert_eq!(bv.push_bits_u8(val2, 8, BitOrder::Msb0), 8);
        assert_eq!(bv.len(), 11); //0111_1000_011
        assert_eq!(bv.byte_at(0).unwrap(), 0b0111_1000);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0110_0000);
        assert_eq!(bv.byte_at(2), None);

        //now push 11 bits
        let val3 = 0b1100_0011_1010_0101;
        assert_eq!(bv.push_bits_u16(val3, 11, BitOrder::Msb0), 11);
        assert_eq!(bv.len(), 22); //0111_1000 0111_1000 0111_01
        assert_eq!(bv.byte_at(0).unwrap(), 0b0111_1000);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0111_1000);
        assert_eq!(bv.byte_at(2).unwrap(), 0b0111_0100);
        assert_eq!(bv.byte_at(3), None);

        //now push 5 bits out of a u128
        let val4 = 0b1011_1010 << U128_BITS - 8;
        assert_eq!(bv.push_bits_u128(val4, 5, BitOrder::Msb0), 5);
        assert_eq!(bv.byte_at(0).unwrap(), 0b0111_1000);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0111_1000);
        assert_eq!(bv.byte_at(2).unwrap(), 0b0111_0110);
        assert_eq!(bv.byte_at(3).unwrap(), 0b1110_0000);
        assert_eq!(bv.byte_at(4), None);
    }

    #[test]
    fn test_read_bits_u16() {
        let mut bv = BitVector::with_capacity(20);
        //push 3 bits 110
        bv.push(true);
        bv.push(true);
        bv.push(false);
        let (val, read) = bv.read_bits_u16(0, 3);
        assert_eq!(read, 3);
        assert_eq!(val, 6);

        // Push another 8 bits for a total bitvector of:
        //1101_0011 110
        bv.push_bits_u8(0b1001_1110, 8, BitOrder::Msb0);
        assert_eq!(bv.len(), 11);
        let (val, read) = bv.read_bits_u16(0, 11);
        assert_eq!(read, 11);
        assert_eq!(val, 0b0000_0110_1001_1110);
    }

    #[test]
    fn test_read_bits_u8() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_bits_u8(0b1100_1011, 8, BitOrder::Msb0);
        bv.push_bits_u8(0b1010_0101, 8, BitOrder::Msb0);
        assert_eq!(bv.len(), 16);

        //Read a byte from start = 0
        let (byte, numbits) = bv.read_bits_u8(0, 8);
        assert_eq!(numbits, 8);
        assert_eq!(byte, 0b1100_1011);

        //Read a byte from start = 4
        let (byte, numbits) = bv.read_bits_u8(4, 8);
        assert_eq!(numbits, 8);
        assert_eq!(byte, 0b1011_1010);

        //Read a byte from start = 12
        let (byte, numbits) = bv.read_bits_u8(12, 8);
        assert_eq!(numbits, 4);
        assert_eq!(byte, 0b0000_0101);

        //Read a byte from start = 15
        let (byte, numbits) = bv.read_bits_u8(15, 8);
        assert_eq!(numbits, 1);
        assert_eq!(byte, 0b0000_0001);

        //Read a byte from start = 16
        let (byte, numbits) = bv.read_bits_u8(16, 8);
        assert_eq!(numbits, 0);
        assert_eq!(byte, 0b0000_0000);
    }

    #[test]
    fn test_read_2bits() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_bits_u8(0b1011_0111, 8, BitOrder::Msb0);
        bv.push_bits_u8(0b00001_0001, 8, BitOrder::Msb0);
        bv.push_bits_u8(0b1100_0011, 8, BitOrder::Msb0);
        bv.push_bits_u8(0b1111_1100, 6, BitOrder::Msb0);
        assert_eq!(bv.bit_len, 30);
        let (val, read) = bv.read_bits_u128(9, 2);
        assert_eq!(read, 2);
        assert_eq!(val, 0b0000_0000);
    }

    #[test]
    fn test_slice() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b0001_0110, Some(8));
        let s = &bv[0..4];
        assert_eq!(s.len(), 4);
        let s = &bv[0..];
        assert_eq!(s.len(), 8);
        let s = &bv[0..=4];
        assert_eq!(s.len(), 5);
        let s = &bv[0..=7];
        assert_eq!(s.len(), 8);
        let s = &bv[..];
        assert_eq!(s.len(), 8);
        let s = &bv[..=6];
        assert_eq!(s.len(), 7);
    }

    #[test]
    fn test_pop() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_bits_u8(23, 8, BitOrder::Lsb0);
        assert_eq!(bv.get(7), Some(true));
        assert_eq!(bv.pop(), Some(true));
        assert_eq!(bv.get(7), None);
        bv.clear();
        bv.push(true);
        assert_eq!(bv.get(0), Some(true));
        assert_eq!(bv.pop(), Some(true));
        assert_eq!(bv.get(0), None);
    }

    #[test]
    fn test_set() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_bits_u8(0b1010_1100, 8, BitOrder::Lsb0);
        assert_eq!(bv.get(3), Some(false));
        assert_eq!(bv.get(7), Some(false));
        assert_eq!(bv.get(6), Some(false));
        bv.set(3, true);
        assert_eq!(bv.get(3), Some(true));
        bv.set(7, true);
        bv.set(6, true);
        assert_eq!(bv.get(6), Some(true));
        assert_eq!(bv.get(7), Some(true));
        bv.set(6, false);
        assert_eq!(bv.get(6), Some(false));
        bv.set(7, false);
        assert_eq!(bv.get(7), Some(false));
    }

    #[test]
    fn test_push_bits_u64() {
        let mut bv = BitVector::with_capacity(512);
        bv.push_bits_u64(u64::MAX, 64, BitOrder::Msb0);
        let (val, bit_count) = bv.read_bits_u64(0, 64);
        assert_eq!(bit_count, 64);
        assert_eq!(val, u64::MAX);
    }

    #[test]
    fn test_push_bits_u128() {
        let mut bv = BitVector::with_capacity(512);
        assert_eq!(bv.push_bits_u128(u64::MAX as u128, 64, BitOrder::Lsb0), 64);
        assert_eq!(bv.len(), 64);
        let (val, bit_count) = bv.read_bits_u128(0, 64);
        assert_eq!(bit_count, 64);
        assert_eq!(val, u64::MAX as u128);
    }

    #[test]
    fn test_push_u8() {
        let mut bv = BitVector::with_capacity(20);
        let val: u8 = 0b0011_0000;
        bv.push_u8(val, None);
        assert_eq!(bv.len(), 6);
        assert_eq!(bv.get(0), Some(true));
        assert_eq!(bv.get(1), Some(true));
        assert_eq!(bv.get(2), Some(false));
        assert_eq!(bv.get(3), Some(false));
        assert_eq!(bv.get(4), Some(false));
        assert_eq!(bv.get(5), Some(false));
        assert_eq!(bv.get(6), None);

        let (val2, bit_count) = bv.read_u8(0);
        assert_eq!(bit_count, 6);
        assert_eq!(val2, 0b0011_0000);
        // bv.clear();
        // assert_eq!(bv.len(), 0);
        // bv.push_bits_u8(val, 4, BitOrder::Msb0); //1111 or 0011
        // assert_eq!(bv.len(), 4);
        // let (val2, bit_count) = bv.read_u8(0);
        // assert_eq!(bit_count, 8); //HWAT?
        // assert_eq!(val2, 0b0011_0000);
    }

    #[test]
    fn test_get_mut() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1011_1100, None);
        assert_eq!(bv[0], true);
        *bv.get_mut(0).unwrap() = false;
        assert_eq!(bv[0], false);
    }

    #[test]
    fn test_read_u16() {
        let mut bv = BitVector::with_capacity(128);
        bv.push(true);
        bv.push(false);
        bv.push(true);

        bv.push_u16(0b1100_1010_0011_0101, None);
        let (val, read) = bv.read_u16(3);
        assert_eq!(read, 16);
        assert_eq!(val, 0b1100_1010_0011_0101);
    }

    #[test]
    fn test_push_u8_width() {
        let mut bv = BitVector::with_capacity(128);

        bv.push_u8(0b0000_0000, Some(0));
        assert_eq!(bv.len(), 0);
        assert_eq!(bv.read_u8(0), (0b0000_0000, 0));
        bv.clear();

        bv.push_u8(0b0000_0000, Some(2));
        assert_eq!(bv.len(), 2);
        assert_eq!(bv.read_u8(0), (0b0000_0000, 2));
        bv.clear();

        bv.push_u8(0b0000_0011, Some(2));
        assert_eq!(bv.len(), 2);
        assert_eq!(bv.read_u8(0), (0b0000_0011, 2));
        bv.clear();

        bv.push_u8(0b0000_0011, Some(4));
        assert_eq!(bv.len(), 4);
        assert_eq!(bv.read_u8(0), (0b0000_0011, 4));
        bv.clear();

        bv.push_u8(0b0111_1000, Some(5));
        assert_eq!(bv.len(), 7);
        assert_eq!(bv.read_u8(0), (0b0111_1000, 7));
        bv.clear();

        bv.push_u8(0b0111_1000, Some(20));
        assert_eq!(bv.len(), 20);
        assert_eq!(bv.read_u8(0), (0b0000_0000, 8));
        bv.clear();
    }

    #[test]
    fn test_bit_and() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b0000_0101, None);
        assert_eq!(bv.len(), 3);

        let bv2 = bv & true;
        assert_eq!(bv2.len(), 3);
        assert_eq!(bv2.read_u8(0), (0b0000_0101, 3));

        let bv3 = bv2 & false;
        assert_eq!(bv3.len(), 3);
        assert_eq!(bv3.read_u8(0), (0b0000_0000, 3));
    }

    #[test]
    fn test_bit_and_assign() {
        let mut bv = BitVector::with_capacity(128);
        bv &= true; //should do nothing
        bv.push_u8(0b0000_0101, None);
        assert_eq!(bv.len(), 3);

        bv &= true;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.read_u8(0), (0b0000_0101, 3));

        bv &= false;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.read_u8(0), (0b0000_0000, 3));

        bv.clear();
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u8(0b0000_0101, None);
        assert_eq!(bv.len(), 19);
        bv &= true;
        assert_eq!(bv.read_u16(0), (0b1001_0011_0101_1010, 16));
        assert_eq!(bv.read_u8(16), (0b0000_0101, 3));

        bv &= false;
        assert_eq!(bv.read_u16(0), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u8(16), (0b0000_0000, 3));

        bv &= true;
        assert_eq!(bv.read_u16(0), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u8(16), (0b0000_0000, 3));
    }

    #[test]
    fn test_bit_or() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b0000_0101, None);
        assert_eq!(bv.len(), 3);

        let bv2 = bv | true;
        assert_eq!(bv2.len(), 3);
        assert_eq!(bv2.read_u8(0), (0b0000_0111, 3));

        let bv3 = bv2 | false;
        assert_eq!(bv3.len(), 3);
        assert_eq!(bv3.read_u8(0), (0b0000_0111, 3));
    }

    #[test]
    fn test_bit_or_assign() {
        let mut bv = BitVector::with_capacity(128);
        bv |= true; //should do nothing

        bv.push_u8(0b0000_0101, None);
        assert_eq!(bv.len(), 3);

        bv |= true;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.read_u8(0), (0b0000_0111, 3));

        bv |= false;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.read_u8(0), (0b0000_0111, 3));

        bv.clear();
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u8(0b0000_0101, None);
        assert_eq!(bv.len(), 19);
        bv |= true;
        assert_eq!(bv.read_u16(0), (0b1111_1111_1111_1111, 16));
        assert_eq!(bv.read_u8(16), (0b0000_0111, 3));

        bv |= false;
        assert_eq!(bv.read_u16(0), (0b1111_1111_1111_1111, 16));
        assert_eq!(bv.read_u8(16), (0b0000_0111, 3));

        bv |= true;
        assert_eq!(bv.read_u16(0), (0b1111_1111_1111_1111, 16));
        assert_eq!(bv.read_u8(16), (0b0000_0111, 3));
    }

    #[test]
    fn test_bit_not() {
        let mut bv = BitVector::with_capacity(128);
        bv = !bv; //should do nothing
        bv.push_u8(0b0000_0101, None);
        assert_eq!(bv.len(), 3);

        bv = !bv;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.read_u8(0), (0b0000_0010, 3));

        bv = !bv;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.read_u8(0), (0b0000_0101, 3));
    }

    #[test]
    fn test_bit_xor() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b0000_0101, None);
        assert_eq!(bv.len(), 3);

        let bv2 = bv ^ true;
        assert_eq!(bv2.len(), 3);
        assert_eq!(bv2.read_u8(0), (0b0000_0010, 3));

        let bv3 = bv2 ^ false;
        assert_eq!(bv3.len(), 3);
        assert_eq!(bv3.read_u8(0), (0b0000_0010, 3));

        let bv4 = bv3 ^ true;
        assert_eq!(bv4.len(), 3);
        assert_eq!(bv4.read_u8(0), (0b0000_0101, 3));
    }

    #[test]
    fn test_bit_xor_assign() {
        let mut bv = BitVector::with_capacity(128);
        bv ^= false; // should do nothing
        bv.push_u8(0b0000_0101, None);
        assert_eq!(bv.len(), 3);

        bv ^= true;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.read_u8(0), (0b0000_0010, 3));

        bv ^= false;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.read_u8(0), (0b0000_0010, 3));

        bv ^= true;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.read_u8(0), (0b0000_0101, 3));

        bv.clear();
        bv.push_u16(0b1001_0011_0101_1010, Some(16));
        bv.push_u8(0b0000_0101, None);
        assert_eq!(bv.len(), 19);
        bv ^= true;
        assert_eq!(bv.read_u16(0), (0b0110_1100_1010_0101, 16));
        assert_eq!(bv.read_u8(16), (0b0000_0010, 3));

        bv ^= false;
        assert_eq!(bv.read_u16(0), (0b0110_1100_1010_0101, 16));
        assert_eq!(bv.read_u8(16), (0b0000_0010, 3));
        bv ^= true;
        assert_eq!(bv.read_u16(0), (0b1001_0011_0101_1010, 16));
        assert_eq!(bv.read_u8(16), (0b0000_0101, 3));
    }

    #[test]
    fn test_last_byte_cleared() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1101_0110, None);
        bv.push_u8(0b0000_1001, None);

        assert_eq!(bv.len(), 12);
        let raw_slice = bv.as_raw_slice();
        let last_byte = raw_slice[raw_slice.len() - 1];
        assert_eq!(last_byte, 0b1001_0000);

        bv |= true;
        let raw_slice = bv.as_raw_slice();
        let last_byte = raw_slice[raw_slice.len() - 1];
        assert_eq!(last_byte, 0b1111_0000);
    }

    #[test]
    fn test_bit_and_slice() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1011_0101_0011_1100, Some(16));
        assert_eq!(bv.len(), 16);
        let mut bv2 = BitVector::with_capacity(8);
        bv2.push_u8(0b1100_0011, Some(8));

        let s = &bv2[..];
        assert_eq!(s.len(), 8);
        bv = bv & s;
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.read_u16(0), (0b1000_0001_0011_1100, 16));

        bv.clear();
        bv.push_u16(0b1011_0101_0011_1100, Some(16));
        bv2.push_u8(0b1111_0011, None);
        let s = &bv2[..];
        assert_eq!(s.len(), 16);
        bv = bv & s;
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.read_u16(0), (0b1000_0001_0011_0000, 16));
        bv &= &bv2;
    }

    #[test]
    #[should_panic(expected = "start index 19 out of range for length 16")]
    fn test_read_bounds() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1011_0101_0011_1100, Some(16));
        bv.read_u8(19);
    }

    #[test]
    #[should_panic(expected = "start index 19 out of range for length 16")]
    fn test_read_bits_bounds() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1011_0101_0011_1100, Some(16));
        bv.read_bits_u8(19, 5);
    }

    #[test]
    fn test_append() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1011_0101, Some(8));
        let mut other = BitVector::with_capacity(128);
        other.push_u16(0b1011_0101_0011_1100, Some(16));
        other.push_u16(0b1111_1111_1111_1111, Some(16));
        other.push_u16(0b0000_0000_0000_0000, Some(16));
        assert_eq!(bv.len(), 8);
        assert_eq!(other.len(), 48);
        bv.append(&mut other);
        assert_eq!(bv.len(), 56);
        assert_eq!(other.len(), 0);
        assert_eq!(bv.read_u8(0), (0b1011_0101, 8));
        assert_eq!(bv.read_u16(8), (0b1011_0101_0011_1100, 16));
        assert_eq!(bv.read_u16(24), (0b1111_1111_1111_1111, 16));
        assert_eq!(bv.read_u16(40), (0b0000_0000_0000_0000, 16));
    }

    #[test]
    fn test_extend_from_bitslice() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u8(0b1011_0101, Some(8));
        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1011_0101_0011_1100, Some(16));
        bv2.push_u16(0b1111_1111_1111_1111, Some(16));
        bv2.push_u16(0b0000_0000_0000_0000, Some(16));
        let other = &bv2[..];
        assert_eq!(bv.len(), 8);
        assert_eq!(other.len(), 48);
        bv.extend_from_bitslice(other);
        assert_eq!(bv.len(), 56);
        assert_eq!(other.len(), 48);
        assert_eq!(bv.read_u8(0), (0b1011_0101, 8));
        assert_eq!(bv.read_u16(8), (0b1011_0101_0011_1100, 16));
        assert_eq!(bv.read_u16(24), (0b1111_1111_1111_1111, 16));
        assert_eq!(bv.read_u16(40), (0b0000_0000_0000_0000, 16));
    }

    #[test]
    fn test_from_bitslice() {
        let mut bv2 = BitVector::with_capacity(128);
        bv2.push_u16(0b1011_0101_0011_1100, Some(16));
        bv2.push_u16(0b1111_1111_1111_1111, Some(16));
        bv2.push_u16(0b0000_0000_0000_0000, Some(16));
        let slice = &bv2[..];
        assert_eq!(slice.len(), 48);
        let bv = BitVector::from_bitslice(slice);
        assert_eq!(bv.len(), 48);
        assert_eq!(slice.len(), 48);
        assert_eq!(bv.read_u16(0), (0b1011_0101_0011_1100, 16));
        assert_eq!(bv.read_u16(16), (0b1111_1111_1111_1111, 16));
        assert_eq!(bv.read_u16(32), (0b0000_0000_0000_0000, 16));
    }

    #[test]
    fn test_repeat() {
        let bv = BitVector::repeat(false, 48);
        assert_eq!(bv.read_u16(0), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(16), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(32), (0b0000_0000_0000_0000, 16));
    }

    #[test]
    fn test_truncate_3() {
        //
        let mut bv = BitVector::repeat(false, 48);
        assert_eq!(bv.read_u16(0), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(16), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(32), (0b0000_0000_0000_0000, 16));
        bv.truncate(3);
        assert_eq!(bv.len(), 3);
    }

    #[test]
    fn test_truncate_0() {
        let mut bv = BitVector::repeat(false, 48);
        assert_eq!(bv.read_u16(0), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(16), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(32), (0b0000_0000_0000_0000, 16));
        bv.truncate(0);
        assert_eq!(bv.len(), 0);
    }

    #[test]
    fn test_truncate_greater() {
        let mut bv = BitVector::repeat(false, 48);
        assert_eq!(bv.read_u16(0), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(16), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(32), (0b0000_0000_0000_0000, 16));
        bv.truncate(100);
        assert_eq!(bv.len(), 48);
    }

    #[test]
    fn test_truncate_16() {
        let mut bv = BitVector::repeat(false, 48);
        assert_eq!(bv.read_u16(0), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(16), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(32), (0b0000_0000_0000_0000, 16));
        bv.truncate(16);
        assert_eq!(bv.len(), 16);
    }

    #[test]
    fn test_truncate_48() {
        let mut bv = BitVector::repeat(false, 48);
        assert_eq!(bv.read_u16(0), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(16), (0b0000_0000_0000_0000, 16));
        assert_eq!(bv.read_u16(32), (0b0000_0000_0000_0000, 16));
        bv.truncate(48);
        assert_eq!(bv.len(), 48);
    }

    #[test]
    fn test_bitvec_macro() {
        let bv = bitvec!();
        assert_eq!(bv.len(), 0);
        let bv = bitvec![1, 0, 1, 1];
        assert_eq!(bv.len(), 4);
        assert_eq!(bv.read_u8(0), (0b1011, 4));
        let bv = bitvec![1;100];
        assert_eq!(bv.len(), 100);
        assert_eq!(bv.read_u64(0), (u64::MAX, 64));
        assert_eq!(bv.read_u32(64), (u32::MAX, 32));
        assert_eq!(bv.read_u8(96), (0b1111, 4));
    }
}
