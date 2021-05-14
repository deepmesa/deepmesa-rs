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
/// Clear the count lsb bits
#[allow(unused_parens)]
#[inline(always)]
pub(super) fn clr_lsb(val: &mut u8, count: u8) {
    *val &= (0xFF << count);
}

/// left shift `count` msb bits of src into dst
///
/// let src:u8 = 0b1010_0000;
/// let mut dst: u8 = 0;
/// let count: u8 = 3;
/// shl_into(&mut dst, src, count);
/// assert_eq!(dst, 0b0000_0101);
#[allow(unused_parens)]
#[inline(always)]
pub(super) fn shl_into(dst: &mut u8, src: u8, count: u8) {
    *dst |= (src >> 8 - count);
}

#[inline(always)]
pub(super) fn crop_msb(val: u8, count: u8) -> u8 {
    val << count
}

/// Returns true if the n MSB bits of the val are set
#[inline(always)]
pub(super) fn is_msb_nset(val: u8, n: u8) -> bool {
    let mask = msb_nset(n);
    val & mask == mask
}

/// Returns the val with the `n` MSB bits cleared. Panics if the n is
/// greater than 8
#[inline(always)]
pub(super) fn msb_clr(val: u8, n: u8) -> u8 {
    if n > 8 {
        panic!("n ({}) exceeds 8", n);
    }

    let mask = lsb_ones_unchecked(8 - n);
    val & mask
}

/// Returns a byte with the 'n'th MSB bit set. This method will
/// panic if n is greater than 7
#[inline(always)]
pub(super) fn msb_nset(n: u8) -> u8 {
    if n > 7 {
        panic!("n ({}) exceeds 7", n);
    }

    const VALUES: [u8; 8] = [
        0b1000_0000,
        0b0100_0000,
        0b0010_0000,
        0b0001_0000,
        0b0000_1000,
        0b0000_0100,
        0b0000_0010,
        0b0000_0001,
    ];
    VALUES[n as usize]
    // match n {
    //     0 => 0b1000_0000,
    //     1 => 0b0100_0000,
    //     2 => 0b0010_0000,
    //     3 => 0b0001_0000,
    //     4 => 0b0000_1000,
    //     5 => 0b0000_0100,
    //     6 => 0b0000_0010,
    //     7 => 0b0000_0001,
    //     _ =>
    // }
}

/// Returns a byte with the 'n'th LSB bit cleared. This method will
/// panic if n is greater than 7
#[inline(always)]
pub(super) fn msb_nclr(n: u8) -> u8 {
    if n > 7 {
        panic!("n ({}) exceeds 7", n);
    }

    const VALUES: [u8; 8] = [
        0b0111_1111,
        0b1011_1111,
        0b1101_1111,
        0b1110_1111,
        0b1111_0111,
        0b1111_1011,
        0b1111_1101,
        0b1111_1110,
    ];
    VALUES[n as usize]
}

/// Returns a byte with 'n' lsb bits set to 1
#[inline(always)]
fn lsb_ones_unchecked(n: u8) -> u8 {
    const VALUES: [u8; 9] = [
        0b0000_0000,
        0b0000_0001,
        0b0000_0011,
        0b0000_0111,
        0b0000_1111,
        0b0001_1111,
        0b0011_1111,
        0b0111_1111,
        0b1111_1111,
    ];
    VALUES[n as usize]
}

/// Returns a byte with 'n' lsb bits set to 1
#[inline(always)]
pub(super) fn lsb_ones(n: u8) -> u8 {
    if n > 8 {
        panic!("n ({}) exceeds 8", n);
    }
    lsb_ones_unchecked(n)
}

/// Returns a byte with 'n' MSB bits set to 1
#[inline(always)]
pub(super) fn msb_ones(n: u8) -> u8 {
    if n > 8 {
        panic!("n ({}) exceeds 8", n);
    }

    const VALUES: [u8; 9] = [
        0b0000_0000,
        0b1000_0000,
        0b1100_0000,
        0b1110_0000,
        0b1111_0000,
        0b1111_1000,
        0b1111_1100,
        0b1111_1110,
        0b1111_1111,
    ];
    VALUES[n as usize]
}

/// Sets the 'count' LSB bits to 1
#[inline(always)]
pub(super) fn fill_lsb(byte: &mut u8, count: u8) {
    *byte |= lsb_ones(count);
}

/// Fills the 'count' LSB bits to 1, starting from 'from'
#[allow(unused_parens)]
#[inline(always)]
pub(super) fn fill_lsb_from(byte: &mut u8, count: u8, from: u8) {
    *byte |= (lsb_ones(count) << from - count + 1)
}

/// Returns the 8 bits of the LSB byte
#[inline(always)]
pub(super) fn ls_byte(val: u128) -> u8 {
    (val & 0xFF) as u8
}

/// Shifts the 'val' right by count
#[inline(always)]
pub(super) fn shr_u128(val: u128, count: u8) -> u128 {
    val >> count
}

/// Shifts the 'val' right by count
#[inline(always)]
pub(super) fn shr_u8(val: u8, count: u8) -> u8 {
    val >> count
}

/// Set the n'th bit (starting from the MSB)
#[inline(always)]
pub(super) fn set_msb_n(val: &mut u8, n: u8) {
    let mask = msb_nset(n);
    *val |= mask;
}

/// Clear the n'th bit (starting from the MSB)
#[inline(always)]
pub(super) fn clr_msb_n(val: &mut u8, n: u8) {
    let mask = msb_nclr(n);
    *val &= mask;
}

/// Shifts the 'val' left by count
#[inline(always)]
pub(super) fn shl(val: u128, count: u8) -> u128 {
    val << count
}

/// Returns the 'count' MSB bits of the usize 'val' as a u8. This
/// method will panic if 'count' is greater than 8
#[inline(always)]
pub(super) fn msbn_usize(val: usize, count: u8) -> usize {
    if count > 8 {
        panic!("count {} exceeds 8", count);
    }

    //shift right by 64 - count
    #[cfg(target_pointer_width = "64")]
    {
        val >> (64 - count)
    }

    //shift right by 32 - count
    #[cfg(target_pointer_width = "32")]
    {
        val >> (32 - count)
    }

    //shift right by 64 - count
    #[cfg(target_pointer_width = "16")]
    {
        val >> (16 - count)
    }
}

/// Returns a usize with 'count' msb bits set to zero with all other
/// bits set to one. This method panics if count is greater than 8.
#[inline(always)]

pub(super) fn msb_zeros_usize(count: u8) -> usize {
    if count > 8 {
        panic!("count {} exceeds 8", count);
    }

    #[cfg(target_pointer_width = "64")]
    const VALUES: [usize; 9] = [
        0xff_ff_ff_ff_ff_ff_ff_ff,
        0x7f_ff_ff_ff_ff_ff_ff_ff,
        0x3f_ff_ff_ff_ff_ff_ff_ff,
        0x1f_ff_ff_ff_ff_ff_ff_ff,
        0x0f_ff_ff_ff_ff_ff_ff_ff,
        0x07_ff_ff_ff_ff_ff_ff_ff,
        0x03_ff_ff_ff_ff_ff_ff_ff,
        0x01_ff_ff_ff_ff_ff_ff_ff,
        0x00_ff_ff_ff_ff_ff_ff_ff,
    ];
    #[cfg(target_pointer_width = "32")]
    const VALUES: [usize; 9] = [
        0xff_ff_ff_ff,
        0x7f_ff_ff_ff,
        0x3f_ff_ff_ff,
        0x1f_ff_ff_ff,
        0x0f_ff_ff_ff,
        0x07_ff_ff_ff,
        0x03_ff_ff_ff,
        0x01_ff_ff_ff,
        0x00_ff_ff_ff,
    ];

    #[cfg(target_pointer_width = "16")]
    const VALUES: [usize; 9] = [
        0xff_ff, 0x7f_ff, 0x3f_ff, 0x1f_ff, 0x0f_ff, 0x07_ff, 0x03_fff, 0x01_ff, 0x00_ff,
    ];

    VALUES[count as usize]
}

/// Returns the specified 'val' with the 'count' MSB bits
/// cleared. This method will panic if 'count' is greater than 8
#[inline(always)]
pub(super) fn clr_msb_usize(val: usize, count: u8) -> usize {
    val & msb_zeros_usize(count)
}

/// Take the 'count' least significant bits of 'src' and set them as
/// the 'count' most significant bits of 'dst' and return the
/// result. This method panics if 'count' is greater than 8
#[inline(always)]
pub(super) fn msb_set_usize(dst: usize, src: usize, count: u8) -> usize {
    if count > 8 {
        panic!("count {} exceeds 8", count);
    }

    // Until usize::BITS is in stable
    #[cfg(target_pointer_width = "64")]
    const BITS: usize = 64;
    #[cfg(target_pointer_width = "32")]
    const BITS: usize = 32;
    #[cfg(target_pointer_width = "16")]
    const BITS: usize = 16;

    let src_shl = src << BITS - count as usize;
    let dst_clrd = clr_msb_usize(dst, count);
    dst_clrd | src_shl
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]

    fn test_msbn_usize() {
        #[cfg(target_pointer_width = "64")]
        const TEST_VALUES: [usize; 5] = [
            0xff_ff_ff_ff_ff_ff_ff_ff,
            0x0f_ff_ff_ff_ff_ff_ff_ff,
            0x1f_ff_ff_ff_ff_ff_ff_ff,
            0x10_ff_ff_ff_ff_ff_ff_ff,
            0x10_ff_ff_ff_ff_ff_ff_ff,
        ];

        #[cfg(target_pointer_width = "32")]
        const TEST_VALUES: [usize; 5] = [
            0xff_ff_ff_ff,
            0x0f_ff_ff_ff,
            0x1f_ff_ff_ff,
            0x10_ff_ff_ff,
            0x10_ff_ff_ff,
        ];

        #[cfg(target_pointer_width = "16")]
        const TEST_VALUES: [usize; 5] = [0xff_ff, 0x0f_ff, 0x1f_ff, 0x10_ff, 0x10_ff];

        assert_eq!(msbn_usize(TEST_VALUES[0], 8), 255);
        assert_eq!(msbn_usize(TEST_VALUES[1], 8), 15);
        assert_eq!(msbn_usize(TEST_VALUES[1], 4), 0);
        assert_eq!(msbn_usize(TEST_VALUES[2], 8), 31);
        assert_eq!(msbn_usize(TEST_VALUES[2], 4), 1);
        assert_eq!(msbn_usize(TEST_VALUES[3], 8), 16);
        assert_eq!(msbn_usize(TEST_VALUES[4], 4), 1);
        assert_eq!(msbn_usize(TEST_VALUES[4], 3), 0);
    }

    #[test]
    fn test_clr_msb_usize() {
        #[cfg(target_pointer_width = "64")]
        {
            const TEST_VALUES: [usize; 5] = [
                0xff_ff_ff_ff_ff_ff_ff_ff,
                0xbf_ff_ff_ff_ff_ff_ff_af,
                0x1f_ff_ff_ff_ff_ff_7f_ff,
                0xb0_ff_ff_ff_ff_5f_ff_ff,
                0x10_ff_ff_3f_ff_ff_ff_ff,
            ];

            assert_eq!(clr_msb_usize(TEST_VALUES[0], 3), 0x1f_ff_ff_ff_ff_ff_ff_ff);
            assert_eq!(clr_msb_usize(TEST_VALUES[1], 3), 0x1f_ff_ff_ff_ff_ff_ff_af);
            assert_eq!(clr_msb_usize(TEST_VALUES[2], 4), 0x0f_ff_ff_ff_ff_ff_7f_ff);
            assert_eq!(clr_msb_usize(TEST_VALUES[3], 3), 0x10_ff_ff_ff_ff_5f_ff_ff);
            assert_eq!(clr_msb_usize(TEST_VALUES[4], 4), 0x00_ff_ff_3f_ff_ff_ff_ff);
        }

        #[cfg(target_pointer_width = "32")]
        {
            const TEST_VALUES: [usize; 5] = [
                0xff_ff_ff_bc,
                0xbf_ff_1b_ff,
                0x1f_ff_2f_ff,
                0xb0_fa_ff_ff,
                0x10_ff_ff_3f,
            ];

            assert_eq!(clr_msb_usize(TEST_VALUES[0], 3), 0x1f_ff_ff_bc);
            assert_eq!(clr_msb_usize(TEST_VALUES[1], 3), 0x1f_ff_1b_ff);
            assert_eq!(clr_msb_usize(TEST_VALUES[2], 4), 0x0f_ff_2f_ff);
            assert_eq!(clr_msb_usize(TEST_VALUES[3], 3), 0x10_fa_ff_ff);
            assert_eq!(clr_msb_usize(TEST_VALUES[4], 4), 0x00_ff_ff_3f);
        }

        #[cfg(target_pointer_width = "16")]
        {
            const TEST_VALUES: [usize; 5] = [0xff_bc, 0xbf_1b, 0x1f_2f, 0xb0_fa, 0x10_3f];

            assert_eq!(clr_msb_usize(TEST_VALUES[0], 3), 0x1f_bc);
            assert_eq!(clr_msb_usize(TEST_VALUES[1], 3), 0x1f_1b);
            assert_eq!(clr_msb_usize(TEST_VALUES[2], 4), 0x0f_2f);
            assert_eq!(clr_msb_usize(TEST_VALUES[3], 3), 0x10_fa);
            assert_eq!(clr_msb_usize(TEST_VALUES[4], 4), 0x00_3f);
        }
    }

    #[test]
    fn test_shl_into() {
        let src: u8 = 0b1010_0000;
        let mut dst: u8 = 0;
        let count: u8 = 3;
        shl_into(&mut dst, src, count);
        assert_eq!(dst, 0b0000_0101);
    }

    #[test]
    fn test_msb_clr() {
        let val: u8 = 0b1010_0101;
        assert_eq!(msb_clr(val, 5), 0b0000_0101);
    }
}