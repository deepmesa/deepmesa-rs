/*
   FastBitVector: A fast contiguous growable array of bits allocated
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

use crate::bitvec::{bitslice::FastBitSlice, BitOrder, BitOrderConvert, Numbits};
use core::fmt;
use core::fmt::Debug;
use core::mem;
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
/// deepmesa = "0.1.0"
/// ```
///
/// ```
/// use deepmesa::collections::FastBitVector;
///
/// let mut bv = FastBitVector::new(128);
/// bv.push(true);
/// bv.push(false);
/// bv.push(true);
///
/// assert_eq!(bv.bit_at(0), Some(true));
/// assert_eq!(bv.bit_at(1), Some(false));
/// assert_eq!(bv.bit_at(2), Some(true));
/// ```
pub struct FastBitVector {
    bits: Vec<u8>,
    capacity_bits: usize,
    bit_index: usize,
}

impl Debug for FastBitVector {
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

impl Index<usize> for FastBitVector {
    type Output = bool;
    fn index(&self, index: usize) -> &Self::Output {
        if index >= self.bit_index {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.bit_index, index
            );
        }

        match self.bit_at(index) {
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

impl FastBitVector {
    pub fn get_slice(&self, start: usize, end: usize) -> FastBitSlice {
        return FastBitSlice::new(self, start, end);
    }

    pub fn new(capacity_bits: usize) -> FastBitVector {
        FastBitVector {
            bits: Vec::with_capacity((capacity_bits + 7) / 8),
            capacity_bits: ((capacity_bits + 7) / 8) * 8,
            bit_index: 0,
        }
    }

    pub fn capacity_bits(&self) -> usize {
        self.capacity_bits
    }

    pub fn len_bits(&self) -> usize {
        self.bit_index
    }

    #[cfg(test)]
    fn len_bytes(&self) -> usize {
        self.bits.len()
    }

    //Number of bits in the last byte
    #[inline(always)]
    fn last_count(&self) -> u8 {
        (self.bit_index % 8) as u8
    }

    fn inc_index(&mut self, val: u8) {
        self.bit_index += val as usize;
    }

    pub fn read_u8(&self, start: usize, max: Numbits) -> (u8, Numbits) {
        if max > 8 {
            panic!("cannot read more than 8 bits into a u8. max={}", max);
        }

        let (mut val, mut read) = self.read_byte(start);
        if read > max {
            //clear the lsb bits
            bitops::clr_lsb(&mut val, 8 - max as u8);
            read = max;
        }
        return ((val as u8).msb0_to_lsb0(read), read);
    }

    pub fn read_u16(&self, start: usize, max: Numbits) -> (u16, Numbits) {
        if max > 16 {
            panic!("cannot read more than 16 bits into a u16. max={}", max);
        }
        let (val, numbits) = self.read_bits(start, max);
        return ((val as u16).msb0_to_lsb0(numbits), numbits);
    }

    pub fn read_u32(&self, start: usize, max: Numbits) -> (u32, Numbits) {
        if max > 32 {
            panic!("cannot read more than 32 bits into a u32. max={}", max);
        }
        let (val, numbits) = self.read_bits(start, max);
        return ((val as u32).msb0_to_lsb0(numbits), numbits);
    }

    pub fn read_u64(&self, start: usize, max: Numbits) -> (u64, Numbits) {
        if max > 64 {
            panic!("cannot read more than 64 bits into a u64. max={}", max);
        }
        let (val, numbits) = self.read_bits(start, max);
        return ((val as u64).msb0_to_lsb0(numbits), numbits);
    }

    pub fn read_u128(&self, start: usize, max: Numbits) -> (u128, Numbits) {
        if max > 128 {
            panic!("cannot read more than 128 bits into a u128. max={}", max);
        }
        let (val, numbits) = self.read_bits(start, max);
        return ((val as u128).msb0_to_lsb0(numbits), numbits);
    }

    fn read_bits(&self, start: usize, max: Numbits) -> (u128, Numbits) {
        if max > 128 {
            panic!("max cannot exceed 128 bits. max = {}", max);
        }

        //at most read 128 bits
        let mut retval: u128 = 0;
        let mut bitsread = 0;
        let mut cursor = start;
        loop {
            let (val, read) = self.read_byte(cursor);
            if read == 0 {
                return (retval, bitsread);
            }
            cursor += read;
            // Shift left by: 128-bitsread-8
            retval |= (val as u128) << (128 - bitsread - 8);
            bitsread += read;
            if bitsread == max {
                break;
            } else if bitsread > max {
                //We've read more than max bits. So clear bitsread-max lsb bits
                retval &= (u128::MAX) << (bitsread - max);
                bitsread = max;
                break;
            }
        }
        return (retval, bitsread);
    }

    fn read_byte(&self, start: usize) -> (u8, Numbits) {
        if start >= self.bit_index {
            return (0, 0);
        }

        let mut byte: u8 = 0;
        //Read the current byte at start
        let mut read: usize =
            bitops::read_lsb(&mut byte, self.bits[start / 8], (start % 8) as u8) as usize;
        let next_idx = (start + 8) / 8;
        if read < 8 && next_idx < self.bit_index / 8 {
            //now read the next byte.
            let next_byte = self.bits[(start + 8) / 8];
            bitops::shl_into(&mut byte, next_byte, 8 - read as u8);
            read = 8;
        }

        //now we've read upto 8 bits. Check how many were actually available
        let avail = self.bit_index - start;
        if read > avail {
            //clear the trailing 'read-available' bits
            bitops::clr_lsb(&mut byte, (read - avail) as u8);
            return (byte, read);
        }
        return (byte, read);
    }

    pub fn push_u16(&mut self, val: u16, count: u8, order: BitOrder) {
        self.push_u128(val as u128, count, order);
    }

    pub fn push_u32(&mut self, val: u32, count: u8, order: BitOrder) {
        self.push_u128(val as u128, count, order);
    }

    pub fn push_u64(&mut self, val: u64, count: u8, order: BitOrder) {
        self.push_u128(val as u128, count, order);
    }

    pub fn push_u128(&mut self, mut val: u128, mut count: u8, order: BitOrder) {
        if count == 0 {
            return;
        }
        let mut len_b = ((mem::size_of::<u128>() * 8) - val.leading_zeros() as usize) as u8;
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
            self.push_u8(val as u8, count, order);
            return;
        }

        loop {
            let byte: u8;
            match order {
                BitOrder::Msb0 => {
                    byte = bitops::ls_byte(bitops::shr(val, len_b - 8));
                    len_b -= 8;
                }
                BitOrder::Lsb0 => {
                    byte = bitops::ls_byte(val);
                    val = bitops::shr(val, 8);
                }
            }
            if count >= 8 {
                self.push_byte(byte);
                count -= 8;
            } else {
                self.push_u8(byte, count, order);
                count = 0;
            }

            if count == 0 {
                break;
            }
        }
    }

    pub fn push_u8(&mut self, mut val: u8, count: u8, order: BitOrder) {
        if count == 0 {
            return;
        }
        if count > 8 {
            panic!("Invalid count: {} cannot be greater than 8", count);
        }
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
            //TODO: This should be 8-set_bits
            bitops::shl_into(&mut self.bits[self.bit_index / 8], val, 8 - set_bits);

            if count + set_bits > 8 {
                // let rem = count + set_bits - 8;
                // count - (count + set_bits - 8);
                // count - count - set_bits + 8
                //                self.bits.push(byte << (count - rem));
                self.bits.push(val << (8 - set_bits)); //TODO: Update this
            }
        }
        self.inc_index(count);
    }

    pub fn push_byte(&mut self, val: u8) {
        let set_bits = self.last_count();
        if set_bits == 0 {
            self.bits.push(val);
        } else {
            //TODO: this should shl 8-set_bits
            bitops::shl_into(&mut self.bits[self.bit_index / 8], val, 8 - set_bits);

            //keep the lsb 'set_bits' in the byte. chop off the msb 8-set_bits.
            self.bits.push(bitops::crop_msb(val, 8 - set_bits));
        }
        self.bit_index += 8;
    }

    fn byte_at(&self, byte_index: usize) -> Option<u8> {
        self.bits.get(byte_index).cloned()
    }

    pub fn bit_at(&self, bit_index: usize) -> Option<bool> {
        if bit_index >= self.bit_index {
            return None;
        }
        let byte_index = bit_index / 8;
        let byte: u8;
        match self.byte_at(byte_index) {
            None => return None,
            Some(x) => byte = x,
        }

        return Some(bitops::is_msb_nset(byte, (bit_index % 8) as u8));
    }

    pub fn push(&mut self, bit: bool) {
        self.fill(1, bit);
    }

    //TODO: Handle the case when the BitVec is full
    pub fn fill(&mut self, mut count: usize, bit: bool) {
        let set_bits = self.last_count();
        if set_bits > 0 {
            if bit {
                // fill the rest of the byte with ones
                //                let last_byte: u8 = self.bits[self.bit_index / 8];
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
                    //Fill the LSB of the last byte with empty_bits 1s
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
}

mod bitops {
    #[allow(unused_parens)]
    #[inline(always)]
    pub(super) fn clr_lsb(val: &mut u8, count: u8) {
        *val &= (0xFF << count);
    }

    //left shift count msb bits of src into dst
    #[allow(unused_parens)]
    #[inline(always)]
    pub(super) fn shl_into(dst: &mut u8, src: u8, count: u8) {
        *dst |= (src >> 8 - count);
    }

    #[inline(always)]
    pub(super) fn crop_msb(val: u8, count: u8) -> u8 {
        val << count
    }

    #[inline(always)]
    pub(super) fn is_msb_nset(val: u8, n: u8) -> bool {
        let mask = msb_nset(n);
        val & mask == mask
    }

    #[inline(always)]
    pub(super) fn msb_nset(n: u8) -> u8 {
        match n {
            0 => 0b1000_0000,
            1 => 0b0100_0000,
            2 => 0b0010_0000,
            3 => 0b0001_0000,
            4 => 0b0000_1000,
            5 => 0b0000_0100,
            6 => 0b0000_0010,
            7 => 0b0000_0001,
            _ => panic!("n ({}) exceeds 7", n),
        }
    }

    #[inline(always)]
    pub(super) fn lsb_ones(n: u8) -> u8 {
        match n {
            0 => 0b0000_0000,
            1 => 0b0000_0001,
            2 => 0b0000_0011,
            3 => 0b0000_0111,
            4 => 0b0000_1111,
            5 => 0b0001_1111,
            6 => 0b0011_1111,
            7 => 0b0111_1111,
            8 => 0b1111_1111,
            _ => panic!("n ({}) exceeds 8", n),
        }
    }

    pub(super) fn msb_ones(n: u8) -> u8 {
        match n {
            0 => 0b0000_0000,
            1 => 0b1000_0000,
            2 => 0b1100_0000,
            3 => 0b1110_0000,
            4 => 0b1111_0000,
            5 => 0b1111_1000,
            6 => 0b1111_1100,
            7 => 0b1111_1110,
            8 => 0b1111_1111,
            _ => panic!("n ({}) exceeds 8", n),
        }
    }

    #[inline(always)]
    pub(super) fn fill_lsb(byte: &mut u8, count: u8) {
        *byte |= lsb_ones(count);
    }

    #[allow(unused_parens)]
    #[inline(always)]
    pub(super) fn fill_lsb_from(byte: &mut u8, count: u8, from: u8) {
        *byte |= (lsb_ones(count) << from - count + 1)
    }

    #[inline(always)]
    pub(super) fn ls_byte(val: u128) -> u8 {
        (val & 0xFF) as u8
    }

    #[inline(always)]
    pub(super) fn shr(val: u128, count: u8) -> u128 {
        val >> count
    }

    #[inline(always)]
    pub(super) fn shl(val: u128, count: u8) -> u128 {
        val << count
    }

    #[inline(always)]
    pub(super) fn read_lsb(dst: &mut u8, src: u8, start: u8) -> u8 {
        *dst = src << start;
        8 - start % 8
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_at() {
        let mut bv = FastBitVector::new(32);
        //push a byte = 0101_0011
        bv.push_byte(0b0101_0011);
        assert_eq!(bv.bit_at(0).unwrap(), false);
        assert_eq!(bv.bit_at(1).unwrap(), true);
        assert_eq!(bv.bit_at(2).unwrap(), false);
        assert_eq!(bv.bit_at(3).unwrap(), true);
        assert_eq!(bv.bit_at(4).unwrap(), false);
        assert_eq!(bv.bit_at(5).unwrap(), false);
        assert_eq!(bv.bit_at(6).unwrap(), true);
        assert_eq!(bv.bit_at(7).unwrap(), true);

        //push another byte = 1100_1011
        bv.push_byte(0b1100_1011);
        assert_eq!(bv.bit_at(8).unwrap(), true);
        assert_eq!(bv.bit_at(9).unwrap(), true);
        assert_eq!(bv.bit_at(10).unwrap(), false);
        assert_eq!(bv.bit_at(11).unwrap(), false);
        assert_eq!(bv.bit_at(12).unwrap(), true);
        assert_eq!(bv.bit_at(13).unwrap(), false);
        assert_eq!(bv.bit_at(14).unwrap(), true);
        assert_eq!(bv.bit_at(15).unwrap(), true);

        assert_eq!(bv.bit_at(18), None);
    }

    #[test]
    fn test_push_byte() {
        let mut bv = FastBitVector::new(32);
        assert_eq!(bv.len_bits(), 0);
        assert_eq!(bv.len_bytes(), 0);
        assert_eq!(bv.bit_index, 0);
        bv.push_byte(0b0110_0000);
        assert_eq!(bv.len_bits(), 8);
        assert_eq!(bv.bit_index, 8);
        assert_eq!(bv.len_bits(), 8);
        assert_eq!(bv.len_bytes(), 1);
        //now artifically set the bit_index to 3 to indicate that
        // there are only 3 buts in the bitvec
        bv.bit_index = 3;
        assert_eq!(bv.len_bits(), 3);
        assert_eq!(bv.len_bytes(), 1);
        assert_eq!(bv.bit_index, 3);

        //now push another byte and ensure that the correct bits are
        // set
        bv.push_byte(0b0110_1001);
        assert_eq!(bv.len_bits(), 11);
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
        let mut bv = FastBitVector::new(32);
        assert_eq!(bv.len_bits(), 0);
        assert_eq!(bv.bit_index, 0);
        bv.fill(8, true);
        assert_eq!(bv.len_bits(), 8);
        assert_eq!(bv.bit_index, 8);
        for i in 0..8 {
            assert_eq!(bv.bit_at(i).unwrap(), true);
        }
        assert_eq!(bv.byte_at(0).unwrap(), 0b1111_1111);
        assert_eq!(bv.byte_at(1), None);
        //now push a byte of zeros
        bv.fill(8, false);
        assert_eq!(bv.len_bits(), 16);
        assert_eq!(bv.bit_index, 16);
        for i in 8..16 {
            assert_eq!(bv.bit_at(i).unwrap(), false);
        }
        assert_eq!(bv.byte_at(1).unwrap(), 0b0000_0000);
        assert_eq!(bv.byte_at(2), None);
    }

    #[test]
    fn test_fill() {
        let mut bv = FastBitVector::new(32);
        assert_eq!(bv.len_bits(), 0);
        assert_eq!(bv.bit_index, 0);
        bv.fill(1, true);
        assert_eq!(bv.len_bits(), 1);
        assert_eq!(bv.bit_at(0).unwrap(), true);
        assert_eq!(bv.bit_at(1), None);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1000_0000);
        assert_eq!(bv.byte_at(1), None);

        bv.fill(2, false);
        assert_eq!(bv.len_bits(), 3);
        assert_eq!(bv.bit_at(0).unwrap(), true);
        assert_eq!(bv.bit_at(1).unwrap(), false);
        assert_eq!(bv.bit_at(2).unwrap(), false);
        assert_eq!(bv.bit_at(3), None);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1000_0000);
        assert_eq!(bv.byte_at(1), None, "Found {:08b}", bv.byte_at(1).unwrap());

        let val = 0b0110_0011;
        bv.push_byte(val);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1000_1100);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0110_0000);
        assert_eq!(bv.byte_at(2), None);
        //        assert_eq!(val << 3, 0b0001_1000);
        // lts3 = 011 0001_1000
        assert_eq!(bv.len_bits(), 11);
        assert_eq!(bv.bit_index, 11);

        assert_eq!(bv.bit_at(0).unwrap(), true);
        assert_eq!(bv.bit_at(1).unwrap(), false);
        assert_eq!(bv.bit_at(2).unwrap(), false);

        assert_eq!(bv.bit_at(3).unwrap(), false);
        assert_eq!(bv.bit_at(4).unwrap(), true);
        assert_eq!(bv.bit_at(5).unwrap(), true);
        assert_eq!(bv.bit_at(6).unwrap(), false);

        assert_eq!(bv.bit_at(7).unwrap(), false);
        assert_eq!(bv.bit_at(8).unwrap(), false);
        assert_eq!(bv.bit_at(9).unwrap(), true);
        assert_eq!(bv.bit_at(10).unwrap(), true);
        assert_eq!(bv.bit_at(11), None);
        assert_eq!(bv.bit_at(12), None);
        assert_eq!(bv.bit_at(9282), None);
    }

    #[test]
    fn test_push_100_bits() {
        let mut bv = FastBitVector::new(1);
        assert_eq!(bv.len_bits(), 0);
        assert_eq!(bv.bit_index, 0);
        bv.fill(100, true);
        assert_eq!(bv.len_bits(), 100);
        for i in 0..100 {
            assert_eq!(bv.bit_at(i).unwrap(), true);
        }
        assert_eq!(bv.bit_at(100), None);
    }

    #[test]
    #[should_panic(expected = "Invalid count: 10 cannot be greater than 8")]
    fn test_push_u8_panic() {
        let mut bv = FastBitVector::new(20);
        let val = 0b1010_1000;

        bv.push_u8(val, 10, BitOrder::Msb0);
    }

    #[test]
    fn test_push_u8() {
        let mut bv = FastBitVector::new(20);
        let val: u8 = 0b1100_1010;
        bv.push_u8(val, 0, BitOrder::Msb0);
        assert_eq!(bv.len_bits(), 0);
        assert_eq!(bv.byte_at(0), None);

        bv.push_u8(val, 3, BitOrder::Msb0);
        assert_eq!(bv.len_bits(), 3);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1100_0000);

        //now push 3 more
        bv.push_u8(val, 3, BitOrder::Msb0);
        assert_eq!(bv.len_bits(), 6);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1000);

        //now push 0 bits of a byte again
        bv.push_u8(val, 0, BitOrder::Msb0);
        assert_eq!(bv.len_bits(), 6);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1000);

        let val: u8 = 0b1010_0011;
        bv.push_u8(val, 8, BitOrder::Msb0);
        assert_eq!(bv.len_bits(), 14);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1010);
        assert_eq!(bv.byte_at(1).unwrap(), 0b1000_1100);
        assert_eq!(bv.byte_at(2), None);
    }

    #[test]
    #[should_panic(expected = "Invalid count: 11 cannot be greater than 8")]
    fn test_push_u8_trailing_panic() {
        let mut bv = FastBitVector::new(20);
        let val = 0b1010_1000;

        bv.push_u8(val, 11, BitOrder::Lsb0);
    }

    #[test]
    fn test_push_u8_trailing() {
        let mut bv = FastBitVector::new(20);
        let val = 0b1010_0011;

        bv.push_u8(val, 0, BitOrder::Lsb0);
        assert_eq!(bv.len_bits(), 0);

        bv.push_u8(val, 3, BitOrder::Lsb0);
        assert_eq!(bv.len_bits(), 3);
        assert_eq!(bv.byte_at(0).unwrap(), 0b0110_0000);

        //Now push another 8 bits
        let val = 0b0101_1100;
        bv.push_u8(val, 8, BitOrder::Lsb0);
        assert_eq!(bv.len_bits(), 11);
        assert_eq!(bv.byte_at(0).unwrap(), 0b0110_1011);
        assert_eq!(bv.byte_at(1).unwrap(), 0b1000_0000);
        assert_eq!(bv.byte_at(2), None);
    }

    #[test]
    #[should_panic(expected = "Length (7) of val (104), exceeds count (30)")]
    fn test_push_usize_panic() {
        let mut bv = FastBitVector::new(20);
        let val = 0b0110_1000;
        bv.push_u128(val, 30, BitOrder::Msb0);
    }

    #[test]
    #[should_panic(expected = "Length (4) of val (10), exceeds count (5)")]
    fn test_push_usize_trailing_panic() {
        let mut bv = FastBitVector::new(20);
        let val = 0b0000_1010;

        bv.push_u128(val, 5, BitOrder::Msb0);
    }

    #[test]
    fn test_push_usize_trailing() {
        let mut bv = FastBitVector::new(20);
        let val = 0b0110_1010;

        //first push 0 bits
        bv.push_u128(val, 0, BitOrder::Lsb0);
        assert_eq!(bv.len_bits(), 0);

        //first push only 3 bits
        bv.push_u128(val, 3, BitOrder::Lsb0);
        assert_eq!(bv.len_bits(), 3);
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
        let mut bv = FastBitVector::new(20);
        let val = 0b0110_1000;

        //first push 0 bits
        bv.push_u128(val, 0, BitOrder::Msb0);
        assert_eq!(bv.len_bits(), 0);

        //first push only 3 bits
        bv.push_u128(val, 3, BitOrder::Msb0);
        assert_eq!(bv.len_bits(), 3);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1100_0000);
        assert_eq!(bv.byte_at(1), None);

        //now push 8 bits
        let val2 = 0b1100_0011;
        bv.push_u128(val2, 8, BitOrder::Msb0);
        assert_eq!(bv.len_bits(), 11);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1000);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0110_0000);
        assert_eq!(bv.byte_at(2), None);

        //now push 11 bits
        let val3 = 0b1100_0011_1010_0101;
        bv.push_u128(val3, 11, BitOrder::Msb0);
        assert_eq!(bv.len_bits(), 22);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1000);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0111_1000);
        assert_eq!(bv.byte_at(2).unwrap(), 0b0111_0100);
        assert_eq!(bv.byte_at(3), None);

        //now push 5 bits out of a u128
        let val4 = 0b1011_1010 << (mem::size_of::<u128>() * 8) - 8;
        bv.push_u128(val4, 5, BitOrder::Msb0);
        assert_eq!(bv.byte_at(0).unwrap(), 0b1101_1000);
        assert_eq!(bv.byte_at(1).unwrap(), 0b0111_1000);
        assert_eq!(bv.byte_at(2).unwrap(), 0b0111_0110);
        assert_eq!(bv.byte_at(3).unwrap(), 0b1110_0000);
        assert_eq!(bv.byte_at(4), None);
    }

    #[test]
    fn test_read_u8() {
        let mut bv = FastBitVector::new(20);
        bv.push_u8(0b1100_1011, 8, BitOrder::Msb0);
        bv.push_u8(0b1010_0101, 8, BitOrder::Msb0);
        assert_eq!(bv.len_bits(), 16);

        // Read a byte from start = 0
        let (byte, numbits) = bv.read_u8(0, 8);
        assert_eq!(numbits, 8);
        assert_eq!(byte, 0b1100_1011);

        //Read a byte from start = 4
        let (byte, numbits) = bv.read_u8(4, 8);
        assert_eq!(numbits, 8);
        assert_eq!(byte, 0b1011_1010);

        //Read a byte from start = 12
        let (byte, numbits) = bv.read_u8(12, 8);
        assert_eq!(numbits, 4);
        assert_eq!(byte, 0b0000_0101);

        //Read a byte from start = 15
        let (byte, numbits) = bv.read_u8(15, 8);
        assert_eq!(numbits, 1);
        assert_eq!(byte, 0b0000_0001);

        //Read a byte from start = 16
        let (byte, numbits) = bv.read_u8(16, 8);
        assert_eq!(numbits, 0);
        assert_eq!(byte, 0b0000_0000);
    }

    #[test]
    fn test_read_2bits() {
        let mut bv = FastBitVector::new(20);
        bv.push_u8(0b1011_0111, 8, BitOrder::Msb0);
        bv.push_u8(0b00001_0001, 8, BitOrder::Msb0);
        bv.push_u8(0b1100_0011, 8, BitOrder::Msb0);
        bv.push_u8(0b1111_1100, 6, BitOrder::Msb0);
        assert_eq!(bv.bit_index, 30);
        //        let slice = bv.get_slice(9, 11);
        //let (val, read) = slice.as_u128();
        let (val, read) = bv.read_u128(9, 2);
        assert_eq!(read, 2);
        assert_eq!(val, 0b0000_0000);
    }
}
