use crate::bitvec::{bitops, bitvec::BitVector, BitCount, BitOrderConvert};
use core::convert::TryFrom;
use core::ops::Index;
use core::ops::IndexMut;
use core::ops::Range;
use core::ops::RangeFrom;
use core::ops::RangeFull;
use core::ops::RangeInclusive;
use core::ops::RangeTo;
use core::ops::RangeToInclusive;

#[repr(transparent)]
pub struct BitSlice([u8]);

macro_rules! read_unsigned {
    ($i:ident, $b: literal, $read_fn: ident) => {
        pub fn $read_fn(&self, start: usize) -> ($i, BitCount) {
            if start > self.len() {
                panic!(
                    "slice range start index {} out of range for length {}",
                    start,
                    self.len()
                );
            }

            let offset = self.offset();
            let len = self.len() + offset;
            let st_index = start + offset;

            let (val, bit_count) = BitSlice::read_bits_lsb0(&self.0, st_index, len, $b);
            (val as $i, bit_count)
        }
    };
}

macro_rules! read_bits_unsigned {
    ($i:ident, $b: literal, $read_bits_fn: ident) => {
        pub fn $read_bits_fn(&self, start: usize, max_bits: BitCount) -> ($i, BitCount) {
            if start > self.len() {
                panic!(
                    "slice range start index {} out of range for length {}",
                    start,
                    self.len()
                );
            }

            if max_bits > $b {
                panic!(
                    "cannot read more than $b bits into a $i. max_bits={}",
                    max_bits
                );
            }
            let offset = self.offset();
            let len = self.len() + offset;
            let (val, bit_count) = BitSlice::read_bits_lsb0(&self.0, start + offset, len, max_bits);
            (val as $i, bit_count)
        }
    };
}

macro_rules! as_unsigned {
    ($i:ident, $b: literal, $as_fn: ident) => {
        pub fn $as_fn(&self) -> ($i, BitCount) {
            let len = self.len();
            if len > $b {
                panic!("slice of len {} bits is too big to fit into a $i", len);
            }
            let offset = self.offset();
            let (val, count) = BitSlice::read_bits_lsb0(&self.0, offset, len + offset, $b);
            (val as $i, count)
        }
    };
}

macro_rules! try_from {
    ($i:ident, $b: literal) => {
        impl TryFrom<&BitSlice> for $i {
            type Error = String;
            fn try_from(bitslice: &BitSlice) -> Result<Self, Self::Error> {
                let len = bitslice.len();
                if len > $b {
                    return Err(format!(
                        "slice of len {} bits is too big to fit into a $i",
                        len
                    ));
                }
                let offset = bitslice.offset();
                Ok(BitSlice::read_bits_lsb0(&bitslice.0, offset, len + offset, $b).0 as $i)
            }
        }
    };
}

impl BitSlice {
    const OFFSET_BITS: u8 = 3;

    #[inline(always)]
    pub(super) fn unpack_len(val: usize) -> usize {
        bitops::clr_msb_usize(val, Self::OFFSET_BITS)
    }

    #[inline(always)]
    pub(super) fn unpack_offset(val: usize) -> usize {
        bitops::msbn_usize(val, Self::OFFSET_BITS)
    }

    #[inline(always)]
    pub(super) fn pack(len: usize, offset: usize) -> usize {
        bitops::msb_set_usize(len, offset, Self::OFFSET_BITS)
    }

    pub(super) fn check_bounds(start: usize, end: usize, len: usize) {
        if start > end {
            panic!("slice index starts at {} but ends at {}", start, end);
        }

        if start > len {
            panic!(
                "slice range start index {} out of range for length {}",
                start, len
            );
        }

        if end > len {
            panic!(
                "slice range end index {} out of range for length {}",
                end, len
            );
        }
    }

    pub(super) fn index(&self, start: usize, end: usize) -> &BitSlice {
        BitSlice::check_bounds(start, end, self.len());
        unsafe {
            let ptr = self.0.as_ptr().add(start % 8);
            let slice: &[u8] =
                std::slice::from_raw_parts(ptr, BitSlice::pack(end - start, start % 8));

            std::mem::transmute(slice)
        }
    }

    fn index_mut(&mut self, start: usize, end: usize) -> &mut BitSlice {
        BitSlice::check_bounds(start, end, self.len());
        unsafe {
            let ptr = self.0.as_mut_ptr().add(start % 8);
            let slice: &mut [u8] =
                std::slice::from_raw_parts_mut(ptr, BitSlice::pack(end - start, start % 8));

            std::mem::transmute(slice)
        }
    }

    /// zeros out the three most significant bits of the length to
    /// return the actual length.
    pub fn len(&self) -> usize {
        Self::unpack_len(self.0.len())
    }

    /// Returns the 3 most significant bits of the length
    fn offset(&self) -> usize {
        Self::unpack_offset(self.0.len())
    }

    pub fn get(&self, index: usize) -> Option<bool> {
        if index >= self.len() {
            return None;
        }

        let index = index + self.offset();
        BitSlice::get_unchecked(&self.0, index)
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
        BitSlice::set_unchecked(&mut self.0, index, value);
    }

    pub(super) fn get_unchecked(bits: &[u8], index: usize) -> Option<bool> {
        let byte = bits[index / 8];
        return Some(bitops::is_msb_nset(byte, (index % 8) as u8));
    }

    pub(super) fn set_unchecked(bits: &mut [u8], index: usize, value: bool) {
        if value {
            bitops::set_msb_n(&mut bits[index / 8], (index % 8) as u8);
        } else {
            bitops::clr_msb_n(&mut bits[index / 8], (index % 8) as u8);
        }
    }

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
        if start > 7 {
            panic!("start {} cannot be greater than 7", start);
        }
        let count: u8;
        if bit_count < 8 {
            count = bit_count as u8;
        } else {
            count = 8;
        }

        //Cases:
        // start = 0
        // --- read: 8     return full byte
        // --- read: < 8   return MSB `read` bits (shift right and return)
        // start > 0
        // --- read: 8     return LSB `avail` bits (clear the MSB bits and return)
        // --- read: < 8   clear the MSB bits then shift right and return

        match start {
            0 => match count {
                8 => (byte, 8),
                _ => (bitops::shr_u8(byte, 8 - count), count as usize),
            },

            _ => {
                //
                let avail = 8 - start;
                if count >= avail {
                    return (bitops::msb_clr(byte, start), avail as usize);
                }
                return (
                    bitops::shr_u8(bitops::msb_clr(byte, start), avail - count),
                    count as usize,
                );
            }
        }
    }

    pub(super) fn read_bits_msb0(
        bits: &[u8],
        start: usize,
        len: usize,
        max_bits: BitCount,
    ) -> (u128, BitCount) {
        if max_bits > 128 {
            panic!("max_bits cannot exceed 128 bits. max_bits = {}", max_bits);
        }

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
            // println!(
            //     "Doing Read: start: {}, cursor: {}, len: {}, max_bits: {}, bits_remaining: {}",
            //     start, cursor, len, max_bits, bits_remaining
            // );
            let byte = bits[cursor / 8];
            let (byte_val, read) =
                BitSlice::sub_byte_lsb0(byte, (cursor % 8) as u8, bits_remaining);
            if read == 0 {
                //No more to read. So return. TODO: What should we return?
                return (retval, bitsread);
            }
            // Shift left by: 128-read-bitsread
            retval |= bitops::shl(byte_val as u128, (128 - read - bitsread) as u8);
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

try_from!(u8, 8);
try_from!(u16, 16);
try_from!(u32, 32);
try_from!(u64, 64);
try_from!(u128, 128);

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

#[macro_use]
macro_rules! index {
    ($i:ident) => {
        impl Index<Range<usize>> for $i {
            type Output = BitSlice;
            fn index(&self, range: Range<usize>) -> &Self::Output {
                self.index(range.start, range.end)
            }
        }

        impl Index<RangeFrom<usize>> for $i {
            type Output = BitSlice;
            fn index(&self, range: RangeFrom<usize>) -> &Self::Output {
                self.index(range.start, self.len())
            }
        }

        impl Index<RangeInclusive<usize>> for $i {
            type Output = BitSlice;
            fn index(&self, range: RangeInclusive<usize>) -> &Self::Output {
                self.index(*range.start(), *range.end() + 1)
            }
        }

        impl Index<RangeToInclusive<usize>> for $i {
            type Output = BitSlice;
            fn index(&self, range: RangeToInclusive<usize>) -> &Self::Output {
                self.index(0, range.end + 1)
            }
        }

        impl Index<RangeTo<usize>> for $i {
            type Output = BitSlice;
            fn index(&self, range: RangeTo<usize>) -> &Self::Output {
                self.index(0, range.end)
            }
        }

        impl Index<RangeFull> for $i {
            type Output = BitSlice;
            fn index(&self, _: RangeFull) -> &Self::Output {
                self.index(0, self.len())
            }
        }

        impl IndexMut<Range<usize>> for $i {
            fn index_mut(&mut self, range: Range<usize>) -> &mut Self::Output {
                self.index_mut(range.start, range.end)
            }
        }

        impl IndexMut<RangeFrom<usize>> for $i {
            fn index_mut(&mut self, range: RangeFrom<usize>) -> &mut Self::Output {
                self.index_mut(range.start, self.len())
            }
        }

        impl IndexMut<RangeTo<usize>> for $i {
            fn index_mut(&mut self, range: RangeTo<usize>) -> &mut Self::Output {
                self.index_mut(0, range.end)
            }
        }

        impl IndexMut<RangeInclusive<usize>> for $i {
            fn index_mut(&mut self, range: RangeInclusive<usize>) -> &mut Self::Output {
                self.index_mut(*range.start(), *range.end() + 1)
            }
        }

        impl IndexMut<RangeToInclusive<usize>> for $i {
            fn index_mut(&mut self, range: RangeToInclusive<usize>) -> &mut Self::Output {
                self.index_mut(0, range.end + 1)
            }
        }

        impl IndexMut<RangeFull> for $i {
            fn index_mut(&mut self, _: RangeFull) -> &mut Self::Output {
                self.index_mut(0, self.len())
            }
        }
    };
}

index!(BitSlice);
index!(BitVector);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvec::{bitvec::BitVector, BitOrder};
    #[test]
    fn test_slice() {
        let mut bv = BitVector::new(20);

        bv.push_u8(0b1011_0011);
        bv.push_u8(0b1011_0011);
        assert_eq!(bv.get(0), Some(true));
        assert_eq!(bv.get(1), Some(false));

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
        let mut bvec = BitVector::new(20);
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
        let mut bvec = BitVector::new(20);
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
        let mut bvec = BitVector::new(20);
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
}