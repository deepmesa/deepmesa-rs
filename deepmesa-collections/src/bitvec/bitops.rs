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

/// left shift `count` msb bits of src into dst
///
/// let src:u8 = 0b1010_0000;
/// let mut dst: u8 = 0;
/// let count: u8 = 3;
/// shl_into(&mut dst, src, count);
/// assert_eq!(dst, 0b0000_0101);
#[inline(always)]
pub(super) fn shl_into(dst: &mut u8, src: u8, count: u8) {
    *dst |= src >> 8 - count;
}

/// Returns true if the n MSB bits of the val are set
#[inline(always)]
pub(super) fn is_msb_nset(val: u8, n: u8) -> bool {
    match (val >> (7 - n)) << 7 {
        0 => false,
        _ => true,
    }
}

/// Returns a byte with the 'n'th MSB bit set. This method will
/// panic if n is greater than 7
#[inline(always)]
pub(super) fn msb_nset(n: u8) -> u8 {
    debug_assert!(n <= 7, "n ({}) exceeds 7", n);
    1u8 << (7 - n)
}

/// Returns the specified 'val' with the 'count' MSB bits
/// cleared. This method will panic if 'count' is greater than 8
#[inline(always)]
pub(super) fn clr_msb_usize(val: usize, count: u8) -> usize {
    debug_assert!(count <= 8, "count {} exceeds 8", count);
    (val << count) >> count
}

/// Returns the 8 bits of the LSB byte
#[inline(always)]
pub(super) fn ls_byte(val: u128) -> u8 {
    (val & 0xFF) as u8
}

/// Set the n'th bit (starting from the MSB)
#[inline(always)]
pub(super) fn set_msb_n(val: &mut u8, n: u8) {
    *val |= msb_nset(n);
}

/// Returns the 'count' MSB bits of the usize 'val' as a u8. This
/// method will panic if 'count' is greater than 8
#[inline(always)]
pub(super) fn msbn_usize(val: usize, count: u8) -> usize {
    debug_assert!(count <= 8, "count {} exceeds 8", count);

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

/// Take the 'count' least significant bits of 'src' and set them as
/// the 'count' most significant bits of 'dst' and return the
/// result. This method panics if 'count' is greater than 8
#[inline(always)]
pub(super) fn msb_set_usize(dst: usize, src: usize, count: u8) -> usize {
    debug_assert!(count <= 8, "count {} exceeds 8", count);

    // Until usize::BITS is in stable
    #[cfg(target_pointer_width = "64")]
    let src_shl = src << (64 - count as usize);
    #[cfg(target_pointer_width = "32")]
    let src_shl = src << (32 - count as usize);
    #[cfg(target_pointer_width = "16")]
    let src_shl = src << (16 - count as usize);

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
            let val: usize = 0xff_ff_ff_ff_ff_ff_ff_ff;
            assert_eq!(clr_msb_usize(val, 0), 0xff_ff_ff_ff_ff_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 1), 0x7f_ff_ff_ff_ff_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 2), 0x3f_ff_ff_ff_ff_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 3), 0x1f_ff_ff_ff_ff_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 4), 0x0f_ff_ff_ff_ff_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 5), 0x07_ff_ff_ff_ff_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 6), 0x03_ff_ff_ff_ff_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 7), 0x01_ff_ff_ff_ff_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 8), 0x00_ff_ff_ff_ff_ff_ff_ff);
        }

        #[cfg(target_pointer_width = "32")]
        {
            let val: usize = 0xff_ff_ff_ff;
            assert_eq!(clr_msb_usize(val, 0), 0xff_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 1), 0x7f_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 2), 0x3f_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 3), 0x1f_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 4), 0x0f_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 5), 0x07_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 6), 0x03_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 7), 0x01_ff_ff_ff);
            assert_eq!(clr_msb_usize(val, 8), 0x00_ff_ff_ff);
        }

        #[cfg(target_pointer_width = "16")]
        {
            let val: usize = 0xff_ff;
            assert_eq!(clr_msb_usize(val, 0), 0xff_ff);
            assert_eq!(clr_msb_usize(val, 1), 0x7f_ff);
            assert_eq!(clr_msb_usize(val, 2), 0x3f_ff);
            assert_eq!(clr_msb_usize(val, 3), 0x1f_ff);
            assert_eq!(clr_msb_usize(val, 4), 0x0f_ff);
            assert_eq!(clr_msb_usize(val, 5), 0x07_ff);
            assert_eq!(clr_msb_usize(val, 6), 0x03_ff);
            assert_eq!(clr_msb_usize(val, 7), 0x01_ff);
            assert_eq!(clr_msb_usize(val, 8), 0x00_ff);
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
    fn test_is_msb_nset() {
        assert_eq!(is_msb_nset(0b1000_0000, 0), true);
        assert_eq!(is_msb_nset(0b0100_0000, 1), true);
        assert_eq!(is_msb_nset(0b0010_0000, 2), true);
        assert_eq!(is_msb_nset(0b0001_0000, 3), true);
        assert_eq!(is_msb_nset(0b0000_1000, 4), true);
        assert_eq!(is_msb_nset(0b0000_0100, 5), true);
        assert_eq!(is_msb_nset(0b0000_0010, 6), true);
        assert_eq!(is_msb_nset(0b0000_0001, 7), true);

        assert_eq!(is_msb_nset(0b0000_0000, 0), false);
        assert_eq!(is_msb_nset(0b0000_0000, 1), false);
        assert_eq!(is_msb_nset(0b0000_0000, 2), false);
        assert_eq!(is_msb_nset(0b0000_0000, 3), false);
        assert_eq!(is_msb_nset(0b0000_0000, 4), false);
        assert_eq!(is_msb_nset(0b0000_0000, 5), false);
        assert_eq!(is_msb_nset(0b0000_0000, 6), false);
        assert_eq!(is_msb_nset(0b0000_0000, 7), false);
    }
}
