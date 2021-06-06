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

use crate::bitvec::{traits::BitwiseClearAssign, BitCount, BitOrder};

macro_rules! leading_count {
    ($i: ident, $offset: expr, leading_ones) => {
        $i.leading_ones() as usize;
    };

    ($i: ident, $offset: expr, leading_zeros) => {{
        let mut lz = $i.leading_zeros() as usize;
        if lz > (8 - $offset) {
            lz = 8 - $offset;
        }
        lz
    }};
}

macro_rules! leading_bits {
    ($fn_name: ident) => {
        pub(super) fn $fn_name(bits: &[u8], start: usize, end: usize) -> usize {
            debug_assert!(end > 0, "end cannot be 0");
            debug_assert!(
                start < end,
                "start {} cannot equal or exceed end {}",
                start,
                end
            );

            let sb_idx = start / 8;
            let eb_idx = (end - 1) / 8;
            let mut b_count = 0;
            for byte_c in sb_idx..=eb_idx {
                let byte: u8 = bits[byte_c];
                let ct;
                let offset;
                if byte_c == sb_idx {
                    //special case the first byte
                    offset = start % 8;
                    let b: u8 = byte << offset;
                    ct = leading_count!(b, offset, $fn_name);
                } else {
                    offset = 0;
                    ct = leading_count!(byte, offset, $fn_name);
                }

                b_count += ct as usize;
                let p_bits = (8 - offset);
                if ct < p_bits {
                    break;
                }
            }
            let limit = end - start;
            if b_count > limit {
                b_count = limit;
            }

            return b_count as usize;
        }
    };
}

leading_bits!(leading_ones);
leading_bits!(leading_zeros);

macro_rules! count_bits {
    ($fn_name: ident) => {
        pub(super) fn $fn_name(bits: &[u8], start: usize, end: usize) -> usize {
            debug_assert!(
                start < end,
                "start {} cannot equal or exceed end {}",
                start,
                end
            );

            let sb_idx = start / 8;
            let eb_idx = (end - 1) / 8;
            let mut b_count = 0;
            for byte_c in sb_idx..=eb_idx {
                let mut byte: u8 = bits[byte_c];
                flip_bits!(byte, $fn_name);
                if byte_c == sb_idx {
                    let offset = (start % 8) as u8;
                    byte.clear_msb_assign(offset);
                }
                if byte_c == eb_idx {
                    let offset = (end % 8) as u8;
                    if offset > 0 {
                        byte.clear_lsb_assign(8 - offset);
                    }
                }

                let ct = byte.count_ones();
                b_count += ct;
            }

            return b_count as usize;
        }
    };
}

count_bits!(count_ones);
count_bits!(count_zeros);

macro_rules! trailing_count {
    ($i:ident, $offset: expr, trailing_ones) => {
        $i.trailing_ones() as usize;
    };
    ($i:ident, $offset: expr, trailing_zeros) => {{
        let mut tz = $i.trailing_zeros() as usize;
        if $offset > 0 && tz > $offset {
            tz = $offset;
        }
        tz
    }};
}

macro_rules! trailing_bits {
    ($fn_name: ident) => {
        pub(super) fn $fn_name(bits: &[u8], start: usize, end: usize) -> usize {
            debug_assert!(end > 0, "end cannot be 0");
            debug_assert!(
                start < end,
                "start {} cannot equal or exceed end {}",
                start,
                end
            );

            let sb_idx = start / 8;
            let eb_idx = (end - 1) / 8;
            let mut b_count = 0;
            for byte_c in (sb_idx..=eb_idx).rev() {
                let byte: u8 = bits[byte_c];
                let ct;
                let mut offset = end % 8;
                if byte_c == eb_idx && offset > 0 {
                    let b: u8 = byte >> (8 - offset);
                    ct = trailing_count!(b, offset, $fn_name);
                } else {
                    offset = 8;
                    ct = trailing_count!(byte, offset, $fn_name);
                }
                b_count += ct;
                if ct < offset {
                    break;
                }
            }
            let limit = end - start;
            if b_count > limit {
                b_count = limit;
            }

            return b_count as usize;
        }
    };
}

trailing_bits!(trailing_ones);
trailing_bits!(trailing_zeros);

macro_rules! first_bit {
    ($fn_name: ident) => {
        pub(super) fn $fn_name(bits: &[u8], start: usize, end: usize) -> Option<usize> {
            debug_assert!(end > 0, "end cannot be 0");
            debug_assert!(
                start < end,
                "start {} cannot equal or exceed end {}",
                start,
                end
            );

            let sb_idx = start / 8;
            let eb_idx = (end - 1) / 8;
            let mut idx: usize = sb_idx * 8;
            for byte_c in sb_idx..=eb_idx {
                let mut byte: u8 = bits[byte_c];
                flip_bits!(byte, $fn_name);
                if byte == 0 {
                    idx += 8;
                    continue;
                }

                if byte_c == sb_idx {
                    let offset = start % 8;
                    byte.clear_msb_assign(offset as u8);
                }

                let bit_idx = byte.leading_zeros() as usize;
                idx += bit_idx;
                if idx >= end {
                    break;
                }
                return Some(idx);
            }

            return None;
        }
    };
}

first_bit!(first_one);
first_bit!(first_zero);

macro_rules! last_bit {
    ($fn_name:ident) => {
        pub(super) fn $fn_name(bits: &[u8], start: usize, end: usize) -> Option<usize> {
            debug_assert!(end > 0, "end cannot be 0");
            debug_assert!(
                start < end,
                "start {} cannot equal or exceed end {}",
                start,
                end
            );

            let sb_idx = start / 8;
            let eb_idx = (end - 1) / 8;
            let mut idx: usize = (eb_idx + 1) * 8;
            for byte_c in (sb_idx..=eb_idx).rev() {
                let mut byte: u8 = bits[byte_c];
                flip_bits!(byte, $fn_name);
                if byte == 0 {
                    idx -= 8;
                    continue;
                }

                if byte_c == eb_idx {
                    let offset = end % 8;
                    if offset > 0 {
                        byte.clear_lsb_assign((8 - offset) as u8);
                    }
                }

                let bit_idx = byte.trailing_zeros() as usize;
                idx -= bit_idx;
                if idx <= start {
                    break;
                }
                return Some(idx - 1);
            }
            return None;
        }
    };
}

last_bit!(last_one);
last_bit!(last_zero);

/// Reads bits from the u8 slice starting at `start`. `end` is the
/// last bit in the slice (not included). Total bits that can be read
/// is `end - start`.
///
/// So in the case of a BitVector, we can read bits from `0` to
/// `bitvec.len()`;
///
/// In the case of a BitSlice we can read bits from `start+offset` to
/// `bitslice.len() + offset` where `offset` is the number of bits
/// into the first byte that the slice begins at
pub(super) fn read_bits(
    bits: &[u8],
    start: usize,
    end: usize,
    max_bits: BitCount,
    order: BitOrder,
) -> (u128, BitCount) {
    debug_assert!(
        max_bits <= 128,
        "max_bits cannot exceed 128 bits. max_bits = {}",
        max_bits
    );

    let sb_idx = start / 8;
    let p_bits = 8 - (start % 8);
    let mut b_rem = max_bits;
    let limit = end - start;
    if b_rem > limit {
        b_rem = limit;
    }

    let mut retval: u128 = 0;
    let mut b_read: usize = 0;
    let mut byte_c = sb_idx;
    while b_rem > 0 {
        let byte = bits[byte_c];

        if byte_c == sb_idx {
            retval |= (byte as u128) << ((128 - p_bits) as u128);
            if b_rem >= p_bits {
                b_rem -= p_bits;
                b_read += p_bits;
            } else {
                b_read += b_rem;
                b_rem = 0;
            }
        } else {
            retval |= (byte as u128) << ((128 - b_read - 8) as u128);
            if b_rem < 8 {
                b_read += b_rem;
                b_rem = 0;
            } else {
                b_rem -= 8;
                b_read += 8;
            }
        }
        byte_c += 1;
    }

    retval = retval >> (128 - b_read);
    if order == BitOrder::Lsb0 {
        return (retval, b_read);
    } else {
        return (retval << (128 - b_read), b_read);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvec::bitvec::BitVector;

    #[test]
    fn test_read_bits_12() {
        let mut bv = BitVector::new();
        bv.push_u16(0b1010_1100_0011_0101, None);
        let (val, read) = read_bits(&bv.bits, 2, 16, 12, BitOrder::Lsb0);
        assert_eq!(read, 12);
        assert_eq!(val, 0b10_1100_0011_01);
    }

    #[test]
    fn test_read_bits_3() {
        let mut bv = BitVector::new();
        bv.push_u16(0b1010_1100_0011_0101, None);
        let (val, read) = read_bits(&bv.bits, 2, 16, 3, BitOrder::Msb0);
        assert_eq!(read, 3);
        assert_eq!(val, 0xa000_0000_0000_0000_0000_0000_0000_0000);
    }

    #[test]
    fn test_leading_ones() {
        let mut bv = BitVector::new();
        bv.push_u8(0b1110_0011, None);
        assert_eq!(leading_ones(&bv.bits, 0, bv.len()), 3);
        assert_eq!(leading_ones(&bv.bits, 2, bv.len()), 1);
        assert_eq!(leading_ones(&bv.bits, 3, bv.len()), 0);

        assert_eq!(leading_ones(&bv.bits, 6, bv.len()), 2);

        let mut bv = BitVector::new();
        bv.push_u8(0b1111_1111, None);
        bv.push_u8(0b1111_1111, None);
        bv.push_u8(0b1111_0000, None);
        assert_eq!(leading_ones(&bv.bits, 0, bv.len()), 20);
        assert_eq!(leading_ones(&bv.bits, 8, bv.len()), 12);
        assert_eq!(leading_ones(&bv.bits, 18, bv.len()), 2);
        assert_eq!(leading_ones(&bv.bits, 20, bv.len()), 0);
    }

    #[test]
    fn test_leading_zeros() {
        let mut bv = BitVector::new();
        bv.push_u8(0b0001_1100, Some(8));
        assert_eq!(leading_zeros(&bv.bits, 0, bv.len()), 3);
        assert_eq!(leading_zeros(&bv.bits, 2, bv.len()), 1);
        assert_eq!(leading_zeros(&bv.bits, 3, bv.len()), 0);

        assert_eq!(leading_zeros(&bv.bits, 6, bv.len()), 2);

        let mut bv = BitVector::new();
        bv.push_u8(0b0000_0000, Some(8));
        bv.push_u8(0b0000_0000, Some(8));
        bv.push_u8(0b0000_1111, Some(8));
        assert_eq!(leading_zeros(&bv.bits, 0, bv.len()), 20);
        assert_eq!(leading_zeros(&bv.bits, 8, bv.len()), 12);
        assert_eq!(leading_zeros(&bv.bits, 18, bv.len()), 2);
        assert_eq!(leading_zeros(&bv.bits, 20, bv.len()), 0);

        let mut bv = BitVector::new();
        bv.push_u8(0b1100_0000, Some(8));
        bv.push_u8(0b0000_0011, Some(8));
        assert_eq!(leading_zeros(&bv.bits, 2, bv.len()), 12);
    }

    #[test]
    fn test_count_ones() {
        let mut bv = BitVector::new();
        bv.push_u8(0b1110_0011, None);
        assert_eq!(count_ones(&bv.bits, 0, bv.len()), 5);
        assert_eq!(count_ones(&bv.bits, 2, bv.len()), 3);
        assert_eq!(count_ones(&bv.bits, 3, bv.len()), 2);
        assert_eq!(count_ones(&bv.bits, 6, bv.len()), 2);

        let mut bv = BitVector::new();
        bv.push_u8(0b1011_1101, None);
        bv.push_u8(0b1001_1011, None);
        bv.push_u8(0b1001_0000, None);
        assert_eq!(count_ones(&bv.bits, 0, bv.len()), 13);
        assert_eq!(count_ones(&bv.bits, 8, bv.len()), 7);
        assert_eq!(count_ones(&bv.bits, 18, bv.len()), 1);
        assert_eq!(count_ones(&bv.bits, 20, bv.len()), 0);
    }

    #[test]
    fn test_count_zeros() {
        let mut bv = BitVector::new();
        bv.push_u8(0b0001_1100, Some(8));
        assert_eq!(count_zeros(&bv.bits, 0, bv.len()), 5);
        assert_eq!(count_zeros(&bv.bits, 2, bv.len()), 3);
        assert_eq!(count_zeros(&bv.bits, 3, bv.len()), 2);
        assert_eq!(count_zeros(&bv.bits, 6, bv.len()), 2);

        let mut bv = BitVector::new();
        bv.push_u8(0b0100_0010, Some(8));
        bv.push_u8(0b0110_0100, Some(8));
        bv.push_u8(0b0110_1111, Some(8));
        assert_eq!(count_zeros(&bv.bits, 0, bv.len()), 13);
        assert_eq!(count_zeros(&bv.bits, 8, bv.len()), 7);
        assert_eq!(count_zeros(&bv.bits, 18, bv.len()), 1);
        assert_eq!(count_zeros(&bv.bits, 20, bv.len()), 0);
    }

    #[test]
    fn test_trailing_ones() {
        let mut bv = BitVector::new();
        bv.push_u8(0b0100_0010, Some(8));
        bv.push_u8(0b0110_0100, Some(8));
        bv.push_u8(0b0111_1111, Some(8));

        assert_eq!(trailing_ones(&bv.bits, 0, bv.len()), 7);
        assert_eq!(trailing_ones(&bv.bits, 20, bv.len()), 4);

        let mut bv = BitVector::new();
        bv.push_u8(0b0111_1100, Some(8));
        assert_eq!(trailing_ones(&bv.bits, 0, 6), 5);

        let mut bv = BitVector::new();
        bv.push_u8(0b0000_1111, Some(8));
        bv.push_u8(0b0011_1111, Some(8));
        assert_eq!(trailing_ones(&bv.bits, 0, bv.len()), 6);
    }

    #[test]
    fn test_trailing_zeros() {
        let mut bv = BitVector::new();
        bv.push_u8(0b0100_0010, Some(8));

        assert_eq!(trailing_zeros(&bv.bits, 0, bv.len()), 1);
        assert_eq!(trailing_zeros(&bv.bits, 2, 6), 4);

        let mut bv = BitVector::new();
        bv.push_u8(0b0100_0010, Some(8));
        bv.push_u8(0b0110_0100, Some(8));
        bv.push_u8(0b0000_0011, Some(8));

        assert_eq!(trailing_zeros(&bv.bits, 0, 22), 8);

        let mut bv = BitVector::new();
        bv.push_u8(0b1111_0000, Some(8));
        bv.push_u8(0b1100_0000, Some(8));
        assert_eq!(trailing_zeros(&bv.bits, 0, bv.len()), 6);
    }

    #[test]
    fn test_first_one() {
        let mut bv = BitVector::new();
        bv.push_u8(0b0010_0010, Some(8));
        assert_eq!(first_one(&bv.bits, 0, bv.len()), Some(2));
        assert_eq!(first_one(&bv.bits, 3, bv.len()), Some(6));
        assert_eq!(first_one(&bv.bits, 7, bv.len()), None);

        let mut bv = BitVector::new();
        bv.push_u8(0b0000_0000, Some(8));
        bv.push_u8(0b0100_0010, Some(8));
        assert_eq!(first_one(&bv.bits, 0, bv.len()), Some(9));
        assert_eq!(first_one(&bv.bits, 10, bv.len()), Some(14));

        let mut bv = BitVector::new();
        bv.push_u8(0b0000_0000, Some(8));
        bv.push_u8(0b0000_0000, Some(8));
        bv.push_u8(0b0000_0000, Some(8));
        bv.push_u8(0b0000_0001, Some(8));
        assert_eq!(first_one(&bv.bits, 0, bv.len()), Some(31));
        assert_eq!(first_one(&bv.bits, 30, bv.len()), Some(31));
        assert_eq!(first_one(&bv.bits, 7, 24), None);

        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b0000_0111, Some(8));
        bv.push_u8(0b1111_0100, Some(8));

        assert_eq!(bv.first_one(0), Some(5));
        assert_eq!(bv.first_one(8), Some(8));
        assert_eq!(bv.first_one(12), Some(13));
        assert_eq!(bv.first_one(14), None);
    }

    #[test]
    fn test_first_zero() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1111_1101, Some(8));
        assert_eq!(first_zero(&bv.bits, 0, bv.len()), Some(6));

        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1111_1000, Some(8));
        bv.push_u8(0b0000_1011, Some(8));

        assert_eq!(bv.first_zero(0), Some(5));
        assert_eq!(bv.first_zero(8), Some(8));
        assert_eq!(bv.first_zero(12), Some(13));
        assert_eq!(bv.first_zero(14), None);
    }

    #[test]
    fn test_last_one() {
        let mut bv = BitVector::new();
        bv.push_u8(0b0000_0000, Some(8));
        assert_eq!(last_one(&bv.bits, 0, bv.len()), None);
        assert_eq!(last_one(&bv.bits, 0, bv.len() - 1), None);

        let mut bv = BitVector::new();
        bv.push_u8(0b0000_0001, Some(8));
        assert_eq!(last_one(&bv.bits, 0, bv.len()), Some(7));

        let mut bv = BitVector::new();
        bv.push_u8(0b0000_0001, Some(8));
        bv.push_u8(0b0001_0000, Some(8));

        assert_eq!(last_one(&bv.bits, 0, bv.len()), Some(11));
        assert_eq!(last_one(&bv.bits, 0, 10), Some(7));
    }

    #[test]
    fn test_last_zero() {
        let mut bv = BitVector::new();
        bv.push_u8(0b1111_1111, Some(8));
        assert_eq!(last_zero(&bv.bits, 0, bv.len()), None);

        let mut bv = BitVector::new();
        bv.push_u8(0b1111_1011, Some(8));
        assert_eq!(last_zero(&bv.bits, 3, 7), Some(5));

        let mut bv = BitVector::new();
        bv.push_u8(0b1111_1110, Some(8));
        assert_eq!(last_zero(&bv.bits, 0, bv.len()), Some(7));
        assert_eq!(last_zero(&bv.bits, 0, bv.len() - 1), None);

        let mut bv = BitVector::new();
        bv.push_u8(0b1111_1110, Some(8));
        bv.push_u8(0b1110_1111, Some(8));

        assert_eq!(last_zero(&bv.bits, 0, bv.len()), Some(11));
        assert_eq!(last_zero(&bv.bits, 0, 10), Some(7));
    }
}
