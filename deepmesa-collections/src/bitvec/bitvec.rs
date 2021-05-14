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

use crate::bitvec::{bitops, bitslice::BitSlice, BitCount, BitOrder};
use core::fmt;
use core::fmt::Debug;
use core::ops::Deref;
use core::ops::DerefMut;
use core::ops::Index;

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
/// let mut bv = BitVector::new(128);
/// bv.push(true);
/// bv.push(false);
/// bv.push(true);
///
/// assert_eq!(bv.get(0), Some(true));
/// assert_eq!(bv.get(1), Some(false));
/// assert_eq!(bv.get(2), Some(true));
/// ```
pub struct BitVector {
    bits: Vec<u8>,
    capacity_bits: usize,
    bit_index: usize,
}

impl Debug for BitVector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "BitVec {{ bit_index: {}, capacity_bits: {}, bits:\n",
            self.bit_index, self.capacity_bits
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
        if index >= self.bit_index {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.bit_index, index
            );
        }

        match self.get(index) {
            None => {
                panic!(
                    "index out of bounds: the len is {} but the index is {}",
                    self.bit_index, index
                );
            }
            Some(true) => &true,
            Some(false) => &false,
        }
    }
}

macro_rules! push_bits_unsigned {
    ($i:ident, $b: literal, $push_bits_fn: ident) => {
        pub fn $push_bits_fn(
            &mut self,
            val: $i,
            bit_count: BitCount,
            order: BitOrder,
            ignore_msb_zeros: bool,
        ) {
            if bit_count > $b {
                panic!(
                    "cannot push more than $b bits from a $i. bit_count={}",
                    bit_count
                );
            }

            self.push_bits_u128(val as u128, bit_count, order, ignore_msb_zeros);
        }
    };
}

macro_rules! push_unsigned {
    ($i:ident, $b: literal, $push_fn: ident) => {
        pub fn $push_fn(&mut self, val: $i) {
            let count = $b - val.leading_zeros() as usize;
            self.push_bits_u128(val as u128, count, BitOrder::Lsb0, true);
        }
    };
}

macro_rules! read_unsigned {
    ($i:ident, $b: literal, $read_fn: ident) => {
        pub fn $read_fn(&self, start: usize) -> ($i, BitCount) {
            let (val, bit_count) = BitSlice::read_bits_lsb0(&self.bits, start, self.bit_index, $b);
            (val as $i, bit_count)
        }
    };
}

macro_rules! read_bits_unsigned {
    ($i:ident, $b: literal, $read_bits_fn: ident) => {
        pub fn $read_bits_fn(&self, start: usize, max_bits: BitCount) -> ($i, BitCount) {
            if max_bits > $b {
                panic!(
                    "cannot read more than $b bits into a $i. max_bits={}",
                    max_bits
                );
            }
            let (val, bit_count) =
                BitSlice::read_bits_lsb0(&self.bits, start, self.bit_index, max_bits);
            (val as $i, bit_count)
        }
    };
}

const U128_BITS: usize = 128;

impl BitVector {
    /// Creates an empty BitVector with the specified capacity. If the
    /// specified capacity is not a multiple of 8, it is increased to
    /// be a multiple of 8
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// let bv = BitVector::new(6);
    /// assert_eq!(bv.capacity(), 8);
    /// ```
    pub fn new(capacity_bits: usize) -> BitVector {
        BitVector {
            bits: Vec::with_capacity((capacity_bits + 7) / 8),
            capacity_bits: ((capacity_bits + 7) / 8) * 8,
            bit_index: 0,
        }
    }

    /// Returns the number of bits this BitVector can hold before new
    /// memory is allocated.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// let bv = BitVector::new(22);
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
    /// let mut bv = BitVector::new(22);
    /// for _ in 0..5 {
    ///     bv.push(true);
    /// }
    /// assert_eq!(bv.len(), 5);
    /// ```
    pub fn len(&self) -> usize {
        self.bit_index
    }

    /// Returns true if the vector contains no bits.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// let mut bv = BitVector::new(22);
    /// assert!(bv.is_empty());
    /// bv.push(true);
    /// assert!(!bv.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.bit_index == 0
    }

    /// Clears the vector, removing all the bits. This method has no
    /// effect on the allocated capacity of the vector.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// let mut bv = BitVector::new(22);
    /// for _ in 0..5 {
    ///     bv.push(true);
    /// }
    /// assert_eq!(bv.len(), 5);
    /// bv.clear();
    /// assert_eq!(bv.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.bits.clear();
        self.bit_index = 0;
    }

    /// Returns Number of bits in the last byte of the underlying
    /// Vector.
    #[inline(always)]
    fn last_count(&self) -> u8 {
        (self.bit_index % 8) as u8
    }

    /// Increments the bit_index
    #[inline(always)]
    fn inc_index(&mut self, val: u8) {
        self.bit_index += val as usize;
    }

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

    push_bits_unsigned!(u16, 16, push_bits_u16);
    push_bits_unsigned!(u32, 32, push_bits_u32);
    push_bits_unsigned!(u64, 64, push_bits_u64);

    pub fn push_bits_u128(
        &mut self,
        value: u128,
        bit_count: BitCount,
        order: BitOrder,
        ignore_msb_zeros: bool,
    ) {
        if bit_count > 128 {
            panic!(
                "cannot push more than 128 bits from a u128. count={}",
                bit_count
            );
        }

        if bit_count == 0 {
            return;
        }
        let mut val = value;
        let mut len_b = U128_BITS as u8;
        if ignore_msb_zeros {
            len_b = (U128_BITS - val.leading_zeros() as usize) as u8;
        }

        let mut count = bit_count as u8;
        if count > len_b {
            panic!(
                "Length ({}) of val ({}), exceeds count ({})",
                len_b, val, count
            );
        }

        if len_b <= 8 {
            if order == BitOrder::Msb0 {
                val = bitops::shl(val, 8 - len_b);
            }
            self.push_bits_u8(val as u8, count, order);
            return;
        }

        loop {
            let byte: u8;
            match order {
                BitOrder::Msb0 => {
                    byte = bitops::ls_byte(bitops::shr_u128(val, len_b - 8));
                    len_b -= 8;
                }
                BitOrder::Lsb0 => {
                    byte = bitops::ls_byte(val);
                    val = bitops::shr_u128(val, 8);
                }
            }
            if count >= 8 {
                self.push_byte(byte);
                count -= 8;
            } else {
                self.push_bits_u8(byte, count, order);
                count = 0;
            }

            if count == 0 {
                break;
            }
        }
    }

    /// Pushes at most 'count' bits from the specified 'val' to the
    /// end of the BitVector. If the 'count' is equal to 8 the oredr
    /// is ignored and all bits are pushed from the MSB (bit position
    /// 7) to the LSB (bit position 0). If the count is less than 8,
    /// then the bits are pushed in the specified Order as follows:
    ///
    /// If the order is Msb0, the leading 'count' bits starting from the
    /// MSB (from bit position 7) are pushed to the end of the
    /// BitVector
    ///
    /// If the order is Lsb0, then trailing 'count' bits starting from
    /// the LSB (from bit position 0) are pushed to the end of the
    /// BitVector.
    ///
    /// This method will panic, if the count is greater than 8.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    /// use deepmesa::collections::bitvec::BitOrder;
    ///
    /// let mut bv = BitVector::new(22);
    /// let val:u8 = 0b1100_0101;
    /// bv.push_bits_u8(val, 3, BitOrder::Msb0);
    /// assert_eq!(bv.len(), 3);
    /// assert_eq!(bv[0], true);
    /// assert_eq!(bv[1], true);
    /// assert_eq!(bv[2], false);
    ///
    /// let mut bv = BitVector::new(22);
    /// bv.push_bits_u8(val, 3, BitOrder::Lsb0);
    /// assert_eq!(bv.len(), 3);
    /// assert_eq!(bv[0], true);
    /// assert_eq!(bv[1], false);
    /// assert_eq!(bv[2], true);
    ///
    /// ```
    pub fn push_bits_u8(&mut self, value: u8, count: u8, order: BitOrder) {
        if count == 0 {
            return;
        }
        if count > 8 {
            panic!("Invalid count: {} cannot be greater than 8", count);
        }
        let mut val = value;
        if order == BitOrder::Lsb0 {
            val = val << (8 - count);
        }
        //clear out the trailing bits from val
        bitops::clr_lsb(&mut val, 8 - count);

        let set_bits: u8 = (self.bit_index % 8) as u8;
        if set_bits == 0 {
            //push the entire byte
            self.bits.push(val);
        } else {
            bitops::shl_into(&mut self.bits[self.bit_index / 8], val, 8 - set_bits);

            if count + set_bits > 8 {
                // Shift left by count - rem
                // rem = count + set_bits - 8;
                // count - rem =
                //   => count - (count + set_bits - 8);
                //   => count - count - set_bits + 8
                //   => - set_bits + 8
                //   => 8 - set_bits
                self.bits.push(val << (8 - set_bits));
            }
        }
        self.inc_index(count);
    }

    push_unsigned!(u8, 8, push_u8);
    push_unsigned!(u16, 16, push_u16);
    push_unsigned!(u32, 32, push_u32);
    push_unsigned!(u64, 64, push_u64);
    push_unsigned!(u128, 128, push_u128);

    /// Pushes all the 8 bits of the specified byte 'val' to the end
    /// of the BitVector. The bits are pushed from the MSB (bit
    /// position 7) to the LSB (bit position 0), with the MSB
    /// occupying the lower index in the BitVector
    fn push_byte(&mut self, val: u8) {
        let set_bits = self.last_count();
        if set_bits == 0 {
            self.bits.push(val);
        } else {
            bitops::shl_into(&mut self.bits[self.bit_index / 8], val, 8 - set_bits);

            //keep the lsb 'set_bits' in the byte. chop off the msb 8-set_bits.
            self.bits.push(bitops::crop_msb(val, 8 - set_bits));
        }
        self.bit_index += 8;
    }

    /// Sets the bit at the given index to 1 if bit is true, otherwise
    /// clears it. Panic if the index exceeds the length
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new(22);
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

        BitSlice::set_unchecked(&mut self.bits, index, value);
    }

    /// Returns a boolean value indicating whether the bit at the
    /// specified index is set or None if the index exceeds the number
    /// of bits in the BitVector.
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new(22);
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

        BitSlice::get_unchecked(&self.bits, index)
    }
    /// Pushes a single bit to the end of the BitVector.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new(22);
    /// bv.push(true);
    /// bv.push(false);
    /// assert_eq!(bv[0], true);
    /// assert_eq!(bv[1], false);
    /// ```
    pub fn push(&mut self, bit: bool) {
        self.fill(1, bit);
    }

    /// Removes the last bit from the BitVector or None if its empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new(22);
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
        if self.bit_index == 0 {
            return None;
        }
        let retval = self.get(self.bit_index - 1);
        let pos: u8 = ((self.bit_index - 1) % 8) as u8;

        if pos == 0 {
            self.bits.pop();
        } else {
            bitops::clr_msb_n(&mut self.bits[(self.bit_index - 1) / 8], pos);
        }
        self.bit_index -= 1;
        retval
    }

    /// Pushes 'count' bits to the end of the BitVector.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new(22);
    /// bv.fill(2, false);
    /// assert_eq!(bv.len(), 2);
    /// bv.fill(2, true);
    /// assert_eq!(bv.len(), 4);
    /// assert_eq!(bv[0], false);
    /// assert_eq!(bv[1], false);
    /// assert_eq!(bv[2], true);
    /// assert_eq!(bv[3], true);
    /// ```
    pub fn fill(&mut self, mut count: usize, bit: bool) {
        let set_bits = self.last_count();
        if set_bits > 0 {
            if bit {
                // fill the rest of the byte with ones
                let empty_bits = 8 - set_bits as usize;
                if count < empty_bits {
                    //Fill the LSB of last byte with 'count' 1s
                    bitops::fill_lsb_from(
                        &mut self.bits[self.bit_index / 8],
                        count as u8,
                        (empty_bits - 1) as u8,
                    );
                    //inc bit_index by count
                    self.inc_index(count as u8);
                    count = 0;
                } else {
                    //Fill the LSB of the last byte with empty_bits
                    bitops::fill_lsb(&mut self.bits[self.bit_index / 8], empty_bits as u8);
                    //inc bit_index by 8-set_bits
                    self.inc_index(8 - set_bits);
                    count -= empty_bits;
                }
            } else {
                //fill the rest of the byte with zeros by simply advancing the bit_index
                if count < 8 - set_bits as usize {
                    self.bit_index += count;
                    count = 0;
                } else {
                    self.inc_index(8 - set_bits);
                    count -= 8 - set_bits as usize;
                }
            }
        }

        //now look at count to see how many new bytes to push
        let bytes_to_push = count / 8;
        let bits_to_push = (count % 8) as u8;
        for _ in 0..bytes_to_push {
            if bit {
                self.bits.push(255u8);
            } else {
                self.bits.push(0u8);
            }
            self.bit_index += 8;
        }

        if bits_to_push != 0 {
            if bit {
                self.bits.push(bitops::msb_ones(bits_to_push));
            } else {
                self.bits.push(0u8);
            }
            self.inc_index(bits_to_push);
        }
    }

    pub(super) fn index(&self, start: usize, end: usize) -> &BitSlice {
        BitSlice::check_bounds(start, end, self.len());
        unsafe {
            let ptr = self.bits.as_ptr().add(start / 8);
            let slice: &[u8] =
                std::slice::from_raw_parts(ptr, BitSlice::pack(end - start, start % 8));
            std::mem::transmute(slice)
        }
    }

    pub(super) fn index_mut(&mut self, start: usize, end: usize) -> &mut BitSlice {
        BitSlice::check_bounds(start, end, self.len());
        unsafe {
            let ptr = self.bits.as_mut_ptr().add(start % 8);
            let slice: &mut [u8] =
                std::slice::from_raw_parts_mut(ptr, BitSlice::pack(end - start, start % 8));

            std::mem::transmute(slice)
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
    //    use crate::bitvec::Slice;

    #[test]
    fn test_bit_at() {
        let mut bv = BitVector::new(32);
        //push a byte = 0101_0011
        bv.push_byte(0b0101_0011);
        assert_eq!(bv.get(0).unwrap(), false);
        assert_eq!(bv.get(1).unwrap(), true);
        assert_eq!(bv.get(2).unwrap(), false);
        assert_eq!(bv.get(3).unwrap(), true);
        assert_eq!(bv.get(4).unwrap(), false);
        assert_eq!(bv.get(5).unwrap(), false);
        assert_eq!(bv.get(6).unwrap(), true);
        assert_eq!(bv.get(7).unwrap(), true);

        //push another byte = 1100_1011
        bv.push_byte(0b1100_1011);
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
        let mut bv = BitVector::new(32);
        assert_eq!(bv.len(), 0);
        assert_eq!(bv.len_bytes(), 0);
        assert_eq!(bv.bit_index, 0);
        bv.push_byte(0b0110_0000);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.bit_index, 8);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.len_bytes(), 1);
        //now artifically set the bit_index to 3 to indicate that
        // there are only 3 buts in the bitvec
        bv.bit_index = 3;
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.len_bytes(), 1);
        assert_eq!(bv.bit_index, 3);

        //now push another byte and ensure that the correct bits are
        // set
        bv.push_byte(0b0110_1001);
        assert_eq!(bv.len(), 11);
        assert_eq!(bv.len_bytes(), 2);
        assert_eq!(bv.bit_index, 11);
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
        let mut bv = BitVector::new(32);
        assert_eq!(bv.len(), 0);
        assert_eq!(bv.bit_index, 0);
        bv.fill(8, true);
        assert_eq!(bv.len(), 8);
        assert_eq!(bv.bit_index, 8);
        for i in 0..8 {
            assert_eq!(bv.get(i).unwrap(), true);
        }
        assert_eq!(bv.byte_at(0).unwrap(), 0b1111_1111);
        assert_eq!(bv.byte_at(1), None);
        //now push a byte of zeros
        bv.fill(8, false);
        assert_eq!(bv.len(), 16);
        assert_eq!(bv.bit_index, 16);
        for i in 8..16 {
            assert_eq!(bv.get(i).unwrap(), false);
        }
        assert_eq!(bv.byte_at(1).unwrap(), 0b0000_0000);
        assert_eq!(bv.byte_at(2), None);
    }

    #[test]
    fn test_fill() {
        let mut bv = BitVector::new(32);
        assert_eq!(bv.len(), 0);
        assert_eq!(bv.bit_index, 0);
        bv.fill(1, true);
        assert_eq!(bv.len(), 1);
        assert_eq!(bv.get(0).unwrap(), true);
        assert_eq!(bv.get(1), None);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1000_0000);
        assert_eq!(bv.byte_at(1), None);

        bv.fill(2, false);
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.get(0).unwrap(), true);
        assert_eq!(bv.get(1).unwrap(), false);
        assert_eq!(bv.get(2).unwrap(), false);
        assert_eq!(bv.get(3), None);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1000_0000);
        assert_eq!(bv.byte_at(1), None, "Found {:08b}", bv.byte_at(1).unwrap());

        let val = 0b0110_0011;
        bv.push_byte(val);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1000_1100);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0110_0000);
        assert_eq!(bv.byte_at(2), None);
        //        assert_eq!(val << 3, 0b0001_1000);
        // lts3 = 011 0001_1000
        assert_eq!(bv.len(), 11);
        assert_eq!(bv.bit_index, 11);

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
        let mut bv = BitVector::new(1);
        assert_eq!(bv.len(), 0);
        assert_eq!(bv.bit_index, 0);
        bv.fill(100, true);
        assert_eq!(bv.len(), 100);
        for i in 0..100 {
            assert_eq!(bv.get(i).unwrap(), true);
        }
        assert_eq!(bv.get(100), None);
    }

    #[test]
    #[should_panic(expected = "Invalid count: 10 cannot be greater than 8")]
    fn test_push_bits_u8_panic() {
        let mut bv = BitVector::new(20);
        let val = 0b1010_1000;

        bv.push_bits_u8(val, 10, BitOrder::Msb0);
    }

    #[test]
    fn test_push_bits_u8() {
        let mut bv = BitVector::new(20);
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
    #[should_panic(expected = "Invalid count: 11 cannot be greater than 8")]
    fn test_push_bits_u8_trailing_panic() {
        let mut bv = BitVector::new(20);
        let val = 0b1010_1000;

        bv.push_bits_u8(val, 11, BitOrder::Lsb0);
    }

    #[test]
    fn test_push_bits_u8_trailing() {
        let mut bv = BitVector::new(20);
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
    #[should_panic(expected = "Length (7) of val (104), exceeds count (30)")]
    fn test_push_usize_panic() {
        let mut bv = BitVector::new(20);
        let val = 0b0110_1000;
        bv.push_bits_u128(val, 30, BitOrder::Msb0, true);
    }

    #[test]
    #[should_panic(expected = "Length (4) of val (10), exceeds count (5)")]
    fn test_push_usize_trailing_panic() {
        let mut bv = BitVector::new(20);
        let val = 0b0000_1010;

        bv.push_bits_u128(val, 5, BitOrder::Msb0, true);
    }

    #[test]
    fn test_push_usize_trailing() {
        let mut bv = BitVector::new(20);
        let val = 0b0110_1010;

        //first push 0 bits
        bv.push_bits_u128(val, 0, BitOrder::Lsb0, true);
        assert_eq!(bv.len(), 0);

        //first push only 3 bits
        bv.push_bits_u128(val, 3, BitOrder::Lsb0, true);
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
    fn test_push_usize_leading() {
        let mut bv = BitVector::new(20);
        let val = 0b0110_1000;

        //first push 0 bits
        bv.push_bits_u128(val, 0, BitOrder::Msb0, true);
        assert_eq!(bv.len(), 0);

        //first push only 3 bits
        bv.push_bits_u128(val, 3, BitOrder::Msb0, true);
        assert_eq!(bv.len(), 3);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1100_0000);
        assert_eq!(bv.byte_at(1), None);

        //now push 8 bits
        let val2 = 0b1100_0011;
        bv.push_bits_u128(val2, 8, BitOrder::Msb0, true);
        assert_eq!(bv.len(), 11);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1000);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0110_0000);
        assert_eq!(bv.byte_at(2), None);

        //now push 11 bits
        let val3 = 0b1100_0011_1010_0101;
        bv.push_bits_u128(val3, 11, BitOrder::Msb0, true);
        assert_eq!(bv.len(), 22);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1000);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0111_1000);
        assert_eq!(bv.byte_at(2).unwrap(), 0b0111_0100);
        assert_eq!(bv.byte_at(3), None);

        //now push 5 bits out of a u128
        let val4 = 0b1011_1010 << U128_BITS - 8;
        bv.push_bits_u128(val4, 5, BitOrder::Msb0, true);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1000);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0111_1000);
        assert_eq!(bv.byte_at(2).unwrap(), 0b0111_0110);
        assert_eq!(bv.byte_at(3).unwrap(), 0b1110_0000);
        assert_eq!(bv.byte_at(4), None);
    }

    #[test]
    fn test_read_bits_u16() {
        let mut bv = BitVector::new(20);
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
        let mut bv = BitVector::new(20);
        bv.push_bits_u8(0b1100_1011, 8, BitOrder::Msb0);
        bv.push_bits_u8(0b1010_0101, 8, BitOrder::Msb0);
        assert_eq!(bv.len(), 16);

        // Read a byte from start = 0
        // let (byte, numbits) = bv.read_bits_u8(0, 8);
        // assert_eq!(numbits, 8);
        // assert_eq!(byte, 0b1100_1011);

        // //Read a byte from start = 4
        // let (byte, numbits) = bv.read_bits_u8(4, 8);
        // assert_eq!(numbits, 8);
        // assert_eq!(byte, 0b1011_1010);

        //Read a byte from start = 12
        let (byte, numbits) = bv.read_bits_u8(12, 8);
        assert_eq!(numbits, 4);
        assert_eq!(byte, 0b0000_0101);

        // //Read a byte from start = 15
        // let (byte, numbits) = bv.read_bits_u8(15, 8);
        // assert_eq!(numbits, 1);
        // assert_eq!(byte, 0b0000_0001);

        // //Read a byte from start = 16
        // let (byte, numbits) = bv.read_bits_u8(16, 8);
        // assert_eq!(numbits, 0);
        // assert_eq!(byte, 0b0000_0000);
    }

    #[test]
    fn test_read_2bits() {
        let mut bv = BitVector::new(20);
        bv.push_bits_u8(0b1011_0111, 8, BitOrder::Msb0);
        bv.push_bits_u8(0b00001_0001, 8, BitOrder::Msb0);
        bv.push_bits_u8(0b1100_0011, 8, BitOrder::Msb0);
        bv.push_bits_u8(0b1111_1100, 6, BitOrder::Msb0);
        assert_eq!(bv.bit_index, 30);
        //        let slice = bv.get_slice(9, 11);
        //let (val, read) = slice.as_u128();
        let (val, read) = bv.read_bits_u128(9, 2);
        assert_eq!(read, 2);
        assert_eq!(val, 0b0000_0000);
    }

    // #[test]
    // fn test_slice() {
    //     let mut bv = BitVector::new(20);
    //     bv.push_byte(22);
    //     let s = bv.slice(0..4);
    //     assert_eq!(s.len(), 4);
    //     assert_eq!(s.start(), 0);
    //     let s = bv.slice(0..);
    //     assert_eq!(s.len(), 8);
    //     assert_eq!(s.start(), 0);
    //     let s = bv.slice(0..=4);
    //     assert_eq!(s.len(), 5);
    //     assert_eq!(s.start(), 0);
    //     let s = bv.slice(0..=7);
    //     assert_eq!(s.len(), 8);
    //     assert_eq!(s.start(), 0);
    //     let s = bv.slice(..);
    //     assert_eq!(s.len(), 8);
    //     assert_eq!(s.start(), 0);
    //     let s = bv.slice(..=6);
    //     assert_eq!(s.len(), 7);
    //     assert_eq!(s.start(), 0);
    // }

    #[test]
    fn test_pop() {
        let mut bv = BitVector::new(20);
        bv.push_byte(23);
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
        let mut bv = BitVector::new(20);
        bv.push_byte(0b1010_1100);
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
        let mut bv = BitVector::new(512);
        bv.push_bits_u64(u64::MAX, 64, BitOrder::Msb0, true);
        let (val, bit_count) = bv.read_bits_u64(0, 64);
        assert_eq!(bit_count, 64);
        assert_eq!(val, u64::MAX);
    }

    #[test]
    fn test_push_bits_u128() {
        let mut bv = BitVector::new(512);
        bv.push_bits_u128(u64::MAX as u128, 64, BitOrder::Msb0, true);
        assert_eq!(bv.len(), 64);
        let (val, bit_count) = bv.read_bits_u128(0, 64);
        assert_eq!(bit_count, 64);
        assert_eq!(val, u64::MAX as u128);
    }

    #[test]
    fn test_push_u8() {
        let mut bv = BitVector::new(20);
        //push_u8 //ignores leading zeros
        let val: u8 = 0b0011_0000;
        println!("PUSHING VAL: {}", val);
        bv.push_u8(val);
        assert_eq!(bv.len(), 6);
        assert_eq!(bv.get(0), Some(true));
        assert_eq!(bv.get(1), Some(true));
        assert_eq!(bv.get(2), Some(false));
        assert_eq!(bv.get(3), Some(false));
        assert_eq!(bv.get(4), Some(false));
        assert_eq!(bv.get(5), Some(false));
        assert_eq!(bv.get(6), None);

        let (val2, bit_count) = bv.read_u8(0);
        println!("VAL READ: {:08b}, Count: {}", val2, bit_count);
        assert_eq!(bit_count, 6);
        // bv.clear();
        // assert_eq!(bv.len(), 0);
        // bv.push_bits_u8(val, 4, BitOrder::Msb0); //1111 or 0011
        // assert_eq!(bv.len(), 4);
        // let (val2, bit_count) = bv.read_u8(0);
        // assert_eq!(bit_count, 8); //HWAT?
        // assert_eq!(val2, 0b0011_0000);
    }
}
