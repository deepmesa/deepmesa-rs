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

use crate::bitvec::BitCount;

const MSB_ONES: [u8; 9] = [
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

const LSB_ONES: [u8; 9] = [
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

const MSB_NTH_ZERO: [u8; 8] = [
    0b0111_1111,
    0b1011_1111,
    0b1101_1111,
    0b1110_1111,
    0b1111_0111,
    0b1111_1011,
    0b1111_1101,
    0b1111_1110,
];

const LSB_NTH_ZERO: [u8; 8] = [
    0b1111_1110,
    0b1111_1101,
    0b1111_1011,
    0b1111_0111,
    0b1110_1111,
    0b1101_1111,
    0b1011_1111,
    0b0111_1111,
];

pub trait BitwiseClear {
    type Output;
    /// Returns a value with the `n` LSB bits of `self` cleared.
    /// # Examples
    /// ```
    /// use deepmesa::collections::bitvec::BitwiseClear;
    ///
    /// let val:u8 = 0b1011_1100;
    /// assert_eq!(val.clear_lsb(4), 0b1011_0000);
    /// ```
    fn clear_lsb(self, n: u8) -> Self::Output;
    /// Returns a value with the `n` MSB bits of `self` cleared.
    /// # Examples
    /// ```
    /// use deepmesa::collections::bitvec::BitwiseClear;
    ///
    /// let val:u8 = 0b1011_1100;
    /// assert_eq!(val.clear_msb(4), 0b0000_1100);
    /// ```
    fn clear_msb(self, n: u8) -> Self::Output;
    /// Returns a value with the `nth` LSB bit of `self` cleared.
    /// # Examples
    /// ```
    /// use deepmesa::collections::bitvec::BitwiseClear;
    ///
    /// let val:u8 = 0b1011_1100;
    /// assert_eq!(val.clear_lsb_nth(3), 0b1011_0100);
    /// ```
    fn clear_lsb_nth(self, n: u8) -> Self::Output;
    /// Returns a value with the `nth` MSB bit of `self` cleared.
    /// # Examples
    /// ```
    /// use deepmesa::collections::bitvec::BitwiseClear;
    ///
    /// let val:u8 = 0b1011_1100;
    /// assert_eq!(val.clear_msb_nth(3), 0b1010_1100);
    /// ```
    fn clear_msb_nth(self, n: u8) -> Self::Output;
}

pub trait BitwiseClearAssign {
    /// Clears `n` LSB bits of `self`
    /// # Examples
    /// ```
    /// use deepmesa::collections::bitvec::BitwiseClearAssign;
    ///
    /// let mut val:u8 = 0b1011_1100;
    /// val.clear_lsb_assign(4);
    /// assert_eq!(val, 0b1011_0000);
    /// ```
    fn clear_lsb_assign(&mut self, n: u8);
    /// Clears `n` MSB bits of `self`
    /// # Examples
    /// ```
    /// use deepmesa::collections::bitvec::BitwiseClearAssign;
    ///
    /// let mut val:u8 = 0b1011_1100;
    /// val.clear_msb_assign(4);
    /// assert_eq!(val, 0b0000_1100);
    /// ```
    fn clear_msb_assign(&mut self, n: u8);
    /// Clears `nth` LSB bit of `self`
    /// # Examples
    /// ```
    /// use deepmesa::collections::bitvec::BitwiseClearAssign;
    ///
    /// let mut val:u8 = 0b1011_1100;
    /// val.clear_lsb_nth_assign(3);
    /// assert_eq!(val, 0b1011_0100);
    /// ```

    fn clear_lsb_nth_assign(&mut self, n: u8);
    /// Clears `nth` MSB bit of `self`
    /// # Examples
    /// ```
    /// use deepmesa::collections::bitvec::BitwiseClearAssign;
    ///
    /// let mut val:u8 = 0b1011_1100;
    /// val.clear_msb_nth_assign(3);
    /// assert_eq!(val, 0b1010_1100);
    /// ```
    fn clear_msb_nth_assign(&mut self, n: u8);
}

pub trait NotLsb {
    type Output;
    fn not_lsb(self, n: u8) -> Self::Output;
}

pub trait NotLsbAssign {
    fn not_lsb_assign(&mut self, n: u8);
}

pub trait NotMsb {
    type Output;
    fn not_msb(self, n: u8) -> Self::Output;
}

pub trait NotMsbAssign {
    fn not_msb_assign(&mut self, n: u8);
}

pub trait NotPartial {
    type Output;
    fn not_partial(self, start: u8, len: u8) -> Self::Output;
}

pub trait NotPartialAssign {
    fn not_partial_assign(&mut self, start: u8, len: u8);
}

pub trait BitwiseLsb<Rhs = bool> {
    type Output;
    fn and_lsb(self, n: u8, rhs: Rhs) -> Self::Output;
    fn or_lsb(self, n: u8, rhs: Rhs) -> Self::Output;
    fn xor_lsb(self, n: u8, rhs: Rhs) -> Self::Output;
}

pub trait BitwiseMsb<Rhs = bool> {
    type Output;
    fn and_msb(self, n: u8, rhs: Rhs) -> Self::Output;
    fn or_msb(self, n: u8, rhs: Rhs) -> Self::Output;
    fn xor_msb(self, n: u8, rhs: Rhs) -> Self::Output;
}

pub trait BitwisePartial<Rhs = bool> {
    type Output;
    fn and_partial(self, start: u8, len: u8, rhs: Rhs) -> Self::Output;
    fn or_partial(self, start: u8, len: u8, rhs: Rhs) -> Self::Output;
    fn xor_partial(self, start: u8, len: u8, rhs: Rhs) -> Self::Output;
}

pub trait BitwiseLsbAssign<Rhs = bool> {
    fn and_lsb_assign(&mut self, n: u8, rhs: Rhs);
    fn or_lsb_assign(&mut self, n: u8, rhs: Rhs);
    fn xor_lsb_assign(&mut self, n: u8, rhs: Rhs);
}

pub trait BitwiseMsbAssign<Rhs = bool> {
    fn and_msb_assign(&mut self, n: u8, rhs: Rhs);
    fn or_msb_assign(&mut self, n: u8, rhs: Rhs);
    fn xor_msb_assign(&mut self, n: u8, rhs: Rhs);
}

pub trait BitwisePartialAssign<Rhs = bool> {
    fn and_partial_assign(&mut self, start: u8, len: u8, rhs: Rhs);
    fn or_partial_assign(&mut self, start: u8, len: u8, rhs: Rhs);
    fn xor_partial_assign(&mut self, start: u8, len: u8, rhs: Rhs);
}

macro_rules! bounds_check {
    ($v: ident, $l: expr) => {
        debug_assert!(
            $v <= $l,
            concat!(stringify!($v), " ({}) ", "exceeds {}"),
            $v,
            $l
        );
    };
}

impl BitwiseClear for u8 {
    type Output = u8;
    #[inline(always)]
    fn clear_lsb(self, n: u8) -> Self::Output {
        bounds_check!(n, 8);
        self & MSB_ONES[8 - n as usize]
    }
    #[inline(always)]
    fn clear_msb(self, n: u8) -> Self::Output {
        bounds_check!(n, 8);
        self & LSB_ONES[8 - n as usize]
    }

    #[inline(always)]
    fn clear_lsb_nth(self, n: u8) -> Self::Output {
        bounds_check!(n, 7);
        self & LSB_NTH_ZERO[n as usize]
    }
    #[inline(always)]
    fn clear_msb_nth(self, n: u8) -> Self::Output {
        bounds_check!(n, 7);
        self & MSB_NTH_ZERO[n as usize]
    }
}

impl BitwiseClearAssign for u8 {
    #[inline(always)]
    fn clear_lsb_assign(&mut self, n: u8) {
        bounds_check!(n, 8);
        *self &= MSB_ONES[8 - n as usize];
    }

    #[inline(always)]
    fn clear_msb_assign(&mut self, n: u8) {
        bounds_check!(n, 8);
        *self &= LSB_ONES[8 - n as usize];
    }

    #[inline(always)]
    fn clear_lsb_nth_assign(&mut self, n: u8) {
        bounds_check!(n, 7);
        *self &= LSB_NTH_ZERO[n as usize];
    }

    #[inline(always)]
    fn clear_msb_nth_assign(&mut self, n: u8) {
        bounds_check!(n, 7);
        *self &= MSB_NTH_ZERO[n as usize];
    }
}

impl BitwiseLsb<u8> for u8 {
    type Output = u8;
    #[inline(always)]
    fn and_lsb(self, n: u8, rhs: u8) -> Self::Output {
        bounds_check!(n, 8);
        return self & (rhs | MSB_ONES[8 - n as usize]);
    }
    #[inline(always)]
    fn or_lsb(self, n: u8, rhs: u8) -> Self::Output {
        bounds_check!(n, 8);
        return self | (rhs & LSB_ONES[n as usize]);
    }

    #[inline(always)]
    fn xor_lsb(self, n: u8, rhs: u8) -> Self::Output {
        bounds_check!(n, 8);
        return self ^ (rhs & LSB_ONES[n as usize]);
    }
}

impl BitwiseLsb<bool> for u8 {
    type Output = u8;
    #[inline(always)]
    fn and_lsb(self, n: u8, rhs: bool) -> Self::Output {
        bounds_check!(n, 8);
        if !rhs {
            return self & MSB_ONES[8 - n as usize];
        }
        return self;
    }
    #[inline(always)]
    fn or_lsb(self, n: u8, rhs: bool) -> Self::Output {
        bounds_check!(n, 8);
        if rhs {
            return self | LSB_ONES[n as usize];
        }
        return self;
    }

    #[inline(always)]
    fn xor_lsb(self, n: u8, rhs: bool) -> Self::Output {
        bounds_check!(n, 8);
        if rhs {
            return self ^ LSB_ONES[n as usize];
        }
        return self;
    }
}

impl NotLsb for u8 {
    type Output = u8;
    #[inline(always)]
    fn not_lsb(self, n: u8) -> Self::Output {
        bounds_check!(n, 8);
        return !(self ^ MSB_ONES[8 - n as usize]);
    }
}

impl BitwiseLsbAssign<bool> for u8 {
    #[inline(always)]
    fn and_lsb_assign(&mut self, n: u8, rhs: bool) {
        bounds_check!(n, 8);
        if !rhs {
            *self &= MSB_ONES[8 - n as usize];
        }
    }
    #[inline(always)]
    fn or_lsb_assign(&mut self, n: u8, rhs: bool) {
        bounds_check!(n, 8);
        if rhs {
            *self |= LSB_ONES[n as usize];
        }
    }

    #[inline(always)]
    fn xor_lsb_assign(&mut self, n: u8, rhs: bool) {
        bounds_check!(n, 8);
        if rhs {
            *self ^= LSB_ONES[n as usize];
        }
    }
}

impl BitwiseLsbAssign<u8> for u8 {
    #[inline(always)]
    fn and_lsb_assign(&mut self, n: u8, rhs: u8) {
        bounds_check!(n, 8);
        *self &= rhs | MSB_ONES[8 - n as usize];
    }

    #[inline(always)]
    fn or_lsb_assign(&mut self, n: u8, rhs: u8) {
        bounds_check!(n, 8);
        *self |= rhs & LSB_ONES[n as usize];
    }

    #[inline(always)]
    fn xor_lsb_assign(&mut self, n: u8, rhs: u8) {
        bounds_check!(n, 8);
        *self ^= rhs & LSB_ONES[n as usize];
    }
}

impl NotLsbAssign for u8 {
    #[inline(always)]
    fn not_lsb_assign(&mut self, n: u8) {
        bounds_check!(n, 8);
        *self = !(*self ^ MSB_ONES[8 - n as usize]);
    }
}

impl BitwiseMsb<bool> for u8 {
    type Output = u8;
    #[inline(always)]
    fn and_msb(self, n: u8, rhs: bool) -> Self::Output {
        bounds_check!(n, 8);
        if !rhs {
            return self & LSB_ONES[8 - n as usize];
        }
        return self;
    }
    #[inline(always)]
    fn or_msb(self, n: u8, rhs: bool) -> Self::Output {
        bounds_check!(n, 8);
        if rhs {
            return self | MSB_ONES[n as usize];
        }
        return self;
    }
    #[inline(always)]
    fn xor_msb(self, n: u8, rhs: bool) -> Self::Output {
        bounds_check!(n, 8);
        if rhs {
            return self ^ MSB_ONES[n as usize];
        }
        return self;
    }
}

impl BitwiseMsb<u8> for u8 {
    type Output = u8;
    #[inline(always)]
    fn and_msb(self, n: u8, rhs: u8) -> Self::Output {
        bounds_check!(n, 8);
        return self & (rhs | LSB_ONES[8 - n as usize]);
    }
    #[inline(always)]
    fn or_msb(self, n: u8, rhs: u8) -> Self::Output {
        bounds_check!(n, 8);
        return self | (rhs & MSB_ONES[n as usize]);
    }
    #[inline(always)]
    fn xor_msb(self, n: u8, rhs: u8) -> Self::Output {
        bounds_check!(n, 8);
        return self ^ (rhs & MSB_ONES[n as usize]);
    }
}

impl NotMsb for u8 {
    type Output = u8;
    #[inline(always)]
    fn not_msb(self, n: u8) -> Self::Output {
        bounds_check!(n, 8);
        return !(self ^ LSB_ONES[8 - n as usize]);
    }
}

impl BitwiseMsbAssign<bool> for u8 {
    #[inline(always)]
    fn and_msb_assign(&mut self, n: u8, rhs: bool) {
        bounds_check!(n, 8);
        if !rhs {
            *self &= LSB_ONES[8 - n as usize];
        }
    }
    #[inline(always)]
    fn or_msb_assign(&mut self, n: u8, rhs: bool) {
        bounds_check!(n, 8);
        if rhs {
            *self |= MSB_ONES[n as usize];
        }
    }
    #[inline(always)]
    fn xor_msb_assign(&mut self, n: u8, rhs: bool) {
        bounds_check!(n, 8);
        if rhs {
            *self ^= MSB_ONES[n as usize];
        }
    }
}

impl BitwiseMsbAssign<u8> for u8 {
    #[inline(always)]
    fn and_msb_assign(&mut self, n: u8, rhs: u8) {
        bounds_check!(n, 8);
        *self &= rhs | LSB_ONES[8 - n as usize];
    }
    #[inline(always)]
    fn or_msb_assign(&mut self, n: u8, rhs: u8) {
        bounds_check!(n, 8);
        *self |= rhs & MSB_ONES[n as usize];
    }
    #[inline(always)]
    fn xor_msb_assign(&mut self, n: u8, rhs: u8) {
        bounds_check!(n, 8);
        *self ^= rhs & MSB_ONES[n as usize];
    }
}

impl NotMsbAssign for u8 {
    #[inline(always)]
    fn not_msb_assign(&mut self, n: u8) {
        bounds_check!(n, 8);
        *self = !(*self ^ LSB_ONES[8 - n as usize]);
    }
}

impl BitwisePartial<bool> for u8 {
    type Output = u8;
    #[inline(always)]
    // `start` starts from MSB
    fn and_partial(self, start: u8, len: u8, rhs: bool) -> Self::Output {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);
        if !rhs {
            return self & (LSB_ONES[8 - start as usize] ^ MSB_ONES[(start + len) as usize]);
        }
        return self;
    }

    #[inline(always)]
    fn or_partial(self, start: u8, len: u8, rhs: bool) -> Self::Output {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);
        if rhs {
            return self | (LSB_ONES[8 - start as usize] & MSB_ONES[(start + len) as usize]);
        }
        return self;
    }

    #[inline(always)]
    fn xor_partial(self, start: u8, len: u8, rhs: bool) -> Self::Output {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);
        if rhs {
            return self ^ (LSB_ONES[8 - start as usize] & MSB_ONES[(start + len) as usize]);
        }
        return self;
    }
}

impl BitwisePartial<u8> for u8 {
    type Output = u8;
    #[inline(always)]
    fn and_partial(self, start: u8, len: u8, rhs: u8) -> Self::Output {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);
        // ...._....
        // ..^._.    start = 2, len = 3
        // 11rr_r111
        // 0011_1111 LSB_ONES[8-start]
        // 1111_1100 MSB_ONES[start+len]
        // 1100_0011 XOR
        // rrrr_rrrr RHS
        // 11rr_rr11 |
        // ...._.... &
        // ..xx_xx..

        return self & (rhs | (LSB_ONES[8 - start as usize] ^ MSB_ONES[(start + len) as usize]));
    }

    #[inline(always)]
    fn or_partial(self, start: u8, len: u8, rhs: u8) -> Self::Output {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);
        return self | (rhs & (LSB_ONES[8 - start as usize] & MSB_ONES[(start + len) as usize]));
    }

    #[inline(always)]
    fn xor_partial(self, start: u8, len: u8, rhs: u8) -> Self::Output {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);
        return self ^ (rhs & (LSB_ONES[8 - start as usize] & MSB_ONES[(start + len) as usize]));
    }
}

impl NotPartial for u8 {
    type Output = u8;
    #[inline(always)]
    fn not_partial(self, start: u8, len: u8) -> Self::Output {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);
        return !(self ^ (LSB_ONES[8 - start as usize] ^ MSB_ONES[(start + len) as usize]));
    }
}

impl BitwisePartialAssign<bool> for u8 {
    #[inline(always)]
    fn and_partial_assign(&mut self, start: u8, len: u8, rhs: bool) {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);
        if !rhs {
            *self &= LSB_ONES[8 - start as usize] ^ MSB_ONES[(start + len) as usize];
        }
    }

    #[inline(always)]
    fn or_partial_assign(&mut self, start: u8, len: u8, rhs: bool) {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);

        if rhs {
            *self |= LSB_ONES[8 - start as usize] & MSB_ONES[(start + len) as usize];
        }
    }

    #[inline(always)]
    fn xor_partial_assign(&mut self, start: u8, len: u8, rhs: bool) {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);

        if rhs {
            *self ^= LSB_ONES[8 - start as usize] & MSB_ONES[(start + len) as usize];
        }
    }
}

impl BitwisePartialAssign<u8> for u8 {
    #[inline(always)]
    fn and_partial_assign(&mut self, start: u8, len: u8, rhs: u8) {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);
        *self &= rhs | (LSB_ONES[8 - start as usize] ^ MSB_ONES[(start + len) as usize]);
    }

    #[inline(always)]
    fn or_partial_assign(&mut self, start: u8, len: u8, rhs: u8) {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);

        *self |= rhs & (LSB_ONES[8 - start as usize] & MSB_ONES[(start + len) as usize]);
    }

    #[inline(always)]
    fn xor_partial_assign(&mut self, start: u8, len: u8, rhs: u8) {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);

        *self ^= rhs & (LSB_ONES[8 - start as usize] & MSB_ONES[(start + len) as usize]);
    }
}

impl NotPartialAssign for u8 {
    #[inline(always)]
    fn not_partial_assign(&mut self, start: u8, len: u8) {
        bounds_check!(start, 7);
        bounds_check!(len, 8 - start);
        *self = !(*self ^ (LSB_ONES[8 - start as usize] ^ MSB_ONES[(start + len) as usize]));
    }
}

///
/// Given a specified number of bits, shift them left (towards the
/// MSB) to produce an ordering such that those bits are counted from
/// the MSB to the LSB
///
/// # Examples
/// ```
/// use deepmesa::collections::bitvec::AsMsb0;
///
/// let val: u8 = 0b0000_1100;
/// let converted = val.as_msb0(4);
/// assert_eq!(converted, 0b1100_0000);
/// ```
///
/// If the bitcount equals the size of `Self` (in bits) then the value
/// is unchanged.
///
/// # Examples
/// ```
/// use deepmesa::collections::bitvec::AsMsb0;
///
/// let val: u8 = 0b1010_1100;
/// let converted = val.as_msb0(8);
/// assert_eq!(converted, 0b1010_1100);
/// ```
pub trait AsMsb0 {
    fn as_msb0(&self, n: BitCount) -> Self;
}

///
/// Given a specified number of bits, shift them right (towards the
/// LSB) to produce an ordering such that those bits are counted from
/// the LSB to the MSB
///
/// # Examples
/// ```
/// use deepmesa::collections::bitvec::AsLsb0;
///
/// let val: u8 = 0b1100_0000;
/// let converted = val.as_lsb0(4);
/// assert_eq!(converted, 0b0000_1100);
/// ```
///
/// If the bitcount equals the size of `Self` (in bits) then the value
/// is unchanged.
///
/// # Examples
/// ```
/// use deepmesa::collections::bitvec::AsLsb0;
///
/// let val: u8 = 0b1010_1100;
/// let converted = val.as_lsb0(8);
/// assert_eq!(converted, 0b1010_1100);
/// ```
pub trait AsLsb0 {
    fn as_lsb0(&self, n: BitCount) -> Self;
}

macro_rules! impl_as_lsb0 {
    ($t: ty, $sz:literal) => {
        impl AsLsb0 for $t {
            fn as_lsb0(&self, n: BitCount) -> Self {
                const TYPE_LEN: usize = $sz;
                if n == 0 {
                    return *self;
                }

                if n > TYPE_LEN {
                    panic!(
                        "Cannot convert BitOrder for BitCount ({}) > {}",
                        n, TYPE_LEN
                    );
                }
                if n == TYPE_LEN {
                    return *self;
                }
                return *self >> (TYPE_LEN - n);
            }
        }
    };
}

macro_rules! impl_as_msb0 {
    ($t:ty, $sz:literal) => {
        impl AsMsb0 for $t {
            fn as_msb0(&self, n: BitCount) -> Self {
                const TYPE_LEN: usize = $sz;
                if n == 0 {
                    return *self;
                }
                if n > TYPE_LEN {
                    panic!(
                        "Cannot convert BitOrder for BitCount ({}) > {}",
                        n, TYPE_LEN
                    );
                }
                if n == TYPE_LEN {
                    return *self;
                }
                return *self << (TYPE_LEN - n);
            }
        }
    };
}

impl_as_lsb0!(u8, 8);
impl_as_lsb0!(u16, 16);
impl_as_lsb0!(u32, 32);
impl_as_lsb0!(u64, 64);
impl_as_lsb0!(u128, 128);

impl_as_msb0!(u8, 8);
impl_as_msb0!(u16, 16);
impl_as_msb0!(u32, 32);
impl_as_msb0!(u64, 64);
impl_as_msb0!(u128, 128);

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem;
    use rand::Rng;

    #[test]
    fn test_clear_msb() {
        assert_eq!(0b1010_0101.clear_msb(5), 0b0000_0101);
    }

    #[test]
    fn test_clear_lsb() {
        assert_eq!(0b1010_1110.clear_lsb(0), 0b1010_1110);
        assert_eq!(0b1010_1110.clear_lsb(5), 0b1010_0000);
        assert_eq!(0b1010_1110.clear_lsb(2), 0b1010_1100);
    }

    #[test]
    fn test_not_lsb_assign() {
        let mut val = 0b1010_0011;
        val.not_lsb_assign(5);
        assert_eq!(val, 0b1011_1100);

        let mut val = 0b1111_0000;
        val.not_lsb_assign(8);
        assert_eq!(val, 0b0000_1111);

        let mut val = 0b1111_0000;
        val.not_lsb_assign(0);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.not_lsb_assign(1);
        assert_eq!(val, 0b1111_0001);

        let mut val = 0b1111_0010;
        val.not_lsb_assign(3);
        assert_eq!(val, 0b1111_0101);
    }

    #[test]
    fn test_not_msb_assign() {
        let mut val = 0b1010_0011;
        val.not_msb_assign(3);
        assert_eq!(val, 0b0100_0011);

        let mut val = 0b1111_0000;
        val.not_msb_assign(8);
        assert_eq!(val, 0b000_1111);

        let mut val = 0b1111_0000;
        val.not_msb_assign(0);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.not_msb_assign(1);
        assert_eq!(val, 0b0111_0000);

        let mut val = 0b1111_0010;
        val.not_msb_assign(5);
        assert_eq!(val, 0b0000_1010);
    }

    #[test]
    fn test_or_lsb_assign() {
        let mut val = 0b1010_0011;
        val.or_lsb_assign(5, true);
        assert_eq!(val, 0b1011_1111);

        let mut val = 0b1010_0011;
        val.or_lsb_assign(5, false);
        assert_eq!(val, 0b1010_0011);

        let mut val = 0b1111_0000;
        val.or_lsb_assign(8, true);
        assert_eq!(val, 0b1111_1111);

        let mut val = 0b1111_0000;
        val.or_lsb_assign(8, false);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.or_lsb_assign(0, true);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.or_lsb_assign(0, false);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.or_lsb_assign(1, true);
        assert_eq!(val, 0b1111_0001);

        let mut val = 0b1111_0011;
        val.or_lsb_assign(1, false);
        assert_eq!(val, 0b1111_0011);

        let mut val = 0b1111_0010;
        val.or_lsb_assign(3, true);
        assert_eq!(val, 0b1111_0111);

        let mut val = 0b1111_0010;
        val.or_lsb_assign(3, false);
        assert_eq!(val, 0b1111_0010);
    }

    #[test]
    fn test_or_msb_assign() {
        let mut val = 0b1010_0011;
        val.or_msb_assign(5, true);
        assert_eq!(val, 0b1111_1011);

        let mut val = 0b1010_0011;
        val.or_msb_assign(5, false);
        assert_eq!(val, 0b1010_0011);

        let mut val = 0b1111_0000;
        val.or_msb_assign(8, true);
        assert_eq!(val, 0b1111_1111);

        let mut val = 0b1111_0000;
        val.or_msb_assign(8, false);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.or_msb_assign(0, true);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.or_msb_assign(0, false);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b0000_1111;
        val.or_msb_assign(1, true);
        assert_eq!(val, 0b1000_1111);

        let mut val = 0b0000_0011;
        val.or_msb_assign(1, false);
        assert_eq!(val, 0b0000_0011);

        let mut val = 0b1010_0010;
        val.or_msb_assign(3, true);
        assert_eq!(val, 0b1110_0010);

        let mut val = 0b1111_0010;
        val.or_msb_assign(3, false);
        assert_eq!(val, 0b1111_0010);
    }

    #[test]
    fn test_xor_lsb_assign() {
        let mut val = 0b1010_0011;
        val.xor_lsb_assign(5, true);
        assert_eq!(val, 0b1011_1100);

        let mut val = 0b1010_0011;
        val.xor_lsb_assign(5, false);
        assert_eq!(val, 0b1010_0011);

        let mut val = 0b1111_0000;
        val.xor_lsb_assign(8, true);
        assert_eq!(val, 0b0000_1111);

        let mut val = 0b1111_0000;
        val.xor_lsb_assign(8, false);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.xor_lsb_assign(0, true);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.xor_lsb_assign(0, false);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.xor_lsb_assign(1, true);
        assert_eq!(val, 0b1111_0001);

        let mut val = 0b1111_0011;
        val.xor_lsb_assign(1, false);
        assert_eq!(val, 0b1111_0011);

        let mut val = 0b1111_0010;
        val.xor_lsb_assign(3, true);
        assert_eq!(val, 0b1111_0101);

        let mut val = 0b1111_0010;
        val.xor_lsb_assign(3, false);
        assert_eq!(val, 0b1111_0010);
    }

    #[test]
    fn test_xor_msb_assign() {
        let mut val = 0b1010_0011;
        val.xor_msb_assign(5, true);
        assert_eq!(val, 0b0101_1011);

        let mut val = 0b1010_0011;
        val.xor_msb_assign(5, false);
        assert_eq!(val, 0b1010_0011);

        let mut val = 0b1111_0000;
        val.xor_msb_assign(8, true);
        assert_eq!(val, 0b0000_1111);

        let mut val = 0b1111_0000;
        val.xor_msb_assign(8, false);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.xor_msb_assign(0, true);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b1111_0000;
        val.xor_msb_assign(0, false);
        assert_eq!(val, 0b1111_0000);

        let mut val = 0b0000_1111;
        val.xor_msb_assign(1, true);
        assert_eq!(val, 0b1000_1111);

        let mut val = 0b0000_0011;
        val.xor_msb_assign(1, false);
        assert_eq!(val, 0b0000_0011);

        let mut val = 0b1010_0010;
        val.xor_msb_assign(3, true);
        assert_eq!(val, 0b0100_0010);

        let mut val = 0b1111_0010;
        val.xor_msb_assign(3, false);
        assert_eq!(val, 0b1111_0010);
    }

    #[test]
    fn test_and_msb_u8() {
        let val = 0b1010_0011;
        assert_eq!(val.and_msb(0, 0b1100_0011), val);
        assert_eq!(val.and_msb(3, 0b1100_0011), 0b1000_0011);
        assert_eq!(val.and_msb(8, 0b1100_0011), 0b1000_0011);
        assert_eq!(val.and_msb(8, 0b0000_0000), 0b0000_0000);
        assert_eq!(val.and_msb(8, 0b1111_1111), val);
        assert_eq!(val.and_msb(3, 0b1111_1111), val);
        assert_eq!(val.and_msb(3, 0b0000_0000), 0b0000_0011);
    }

    #[test]
    fn test_and_msb_assign_u8() {
        let val = 0b1010_0011;
        let mut res = val;
        res.and_msb_assign(0, 0b1100_0011);
        assert_eq!(res, val);

        let mut res = val;
        res.and_msb_assign(3, 0b1100_0011);
        assert_eq!(res, 0b1000_0011);

        let mut res = val;
        res.and_msb_assign(8, 0b1100_0011);
        assert_eq!(res, 0b1000_0011);

        let mut res = val;
        res.and_msb_assign(8, 0b0000_0000);
        assert_eq!(res, 0b0000_0000);

        let mut res = val;
        res.and_msb_assign(8, 0b1111_1111);
        assert_eq!(res, val);

        let mut res = val;
        res.and_msb_assign(3, 0b1111_1111);
        assert_eq!(res, val);

        let mut res = val;
        res.and_msb_assign(3, 0b0000_0000);
        assert_eq!(res, 0b0000_0011);
    }

    #[test]
    fn test_and_lsb_u8() {
        let val = 0b1010_0011;
        assert_eq!(val.and_lsb(0, 0b1100_0011), val);
        assert_eq!(val.and_lsb(3, 0b1100_0101), 0b1010_0001);
        assert_eq!(val.and_lsb(8, 0b1100_0101), 0b1000_0001);
        assert_eq!(val.and_lsb(8, 0b0000_0000), 0b0000_0000);
        assert_eq!(val.and_lsb(8, 0b1111_1111), val);
        assert_eq!(val.and_lsb(3, 0b1111_1111), val);
        assert_eq!(val.and_lsb(3, 0b0000_0000), 0b1010_0000);
    }
    #[test]
    fn test_and_lsb_assign_u8() {
        let val = 0b1010_0011;

        let mut res = val;
        res.and_lsb_assign(0, 0b1100_0011);
        assert_eq!(res, val);

        let mut res = val;
        res.and_lsb_assign(3, 0b1100_0101);
        assert_eq!(res, 0b1010_0001);

        let mut res = val;
        res.and_lsb_assign(8, 0b1100_0101);
        assert_eq!(res, 0b1000_0001);

        let mut res = val;
        res.and_lsb_assign(8, 0b0000_0000);
        assert_eq!(res, 0b0000_0000);

        let mut res = val;
        res.and_lsb_assign(8, 0b1111_1111);
        assert_eq!(res, val);

        let mut res = val;
        res.and_lsb_assign(3, 0b1111_1111);
        assert_eq!(res, val);

        let mut res = val;
        res.and_lsb_assign(3, 0b0000_0000);
        assert_eq!(res, 0b1010_0000);
    }

    #[test]
    fn test_or_msb_u8() {
        let val = 0b1010_0011;
        assert_eq!(val.or_msb(0, 0b1100_0011), val);
        assert_eq!(val.or_msb(3, 0b1100_0101), 0b1110_0011);
        assert_eq!(val.or_msb(8, 0b1100_0101), 0b1110_0111);
        assert_eq!(val.or_msb(8, 0b0000_0000), val);
        assert_eq!(val.or_msb(8, 0b1111_1111), 0b1111_1111);
        assert_eq!(val.or_msb(3, 0b1111_1111), 0b1110_0011);
        assert_eq!(val.or_msb(3, 0b0000_0000), val);
    }
    #[test]
    fn test_or_msb_assign_u8() {
        let val = 0b1010_0011;

        let mut res = val;
        res.or_msb_assign(0, 0b1100_0011);
        assert_eq!(res, val);

        let mut res = val;
        res.or_msb_assign(3, 0b1100_0101);
        assert_eq!(res, 0b1110_0011);

        let mut res = val;
        res.or_msb_assign(8, 0b1100_0101);
        assert_eq!(res, 0b1110_0111);

        let mut res = val;
        res.or_msb_assign(8, 0b0000_0000);
        assert_eq!(res, val);

        let mut res = val;
        res.or_msb_assign(8, 0b1111_1111);
        assert_eq!(res, 0b1111_1111);

        let mut res = val;
        res.or_msb_assign(3, 0b1111_1111);
        assert_eq!(res, 0b1110_0011);

        let mut res = val;
        res.or_msb_assign(3, 0b0000_0000);
        assert_eq!(res, val);
    }

    #[test]
    fn test_or_lsb_u8() {
        let val = 0b1010_0011;
        assert_eq!(val.or_lsb(0, 0b1100_0011), val);
        assert_eq!(val.or_lsb(3, 0b1100_0101), 0b1010_0111);
        assert_eq!(val.or_lsb(8, 0b1100_0101), 0b1110_0111);
        assert_eq!(val.or_lsb(8, 0b0000_0000), val);
        assert_eq!(val.or_lsb(8, 0b1111_1111), 0b1111_1111);
        assert_eq!(val.or_lsb(3, 0b1111_1111), 0b1010_0111);
        assert_eq!(val.or_lsb(3, 0b0000_0000), val);
    }
    #[test]
    fn test_or_lsb_assign_u8() {
        let val = 0b1010_0011;

        let mut res = val;
        res.or_lsb_assign(0, 0b1100_0011);
        assert_eq!(res, val);

        let mut res = val;
        res.or_lsb_assign(3, 0b1100_0101);
        assert_eq!(res, 0b1010_0111);

        let mut res = val;
        res.or_lsb_assign(8, 0b1100_0101);
        assert_eq!(res, 0b1110_0111);

        let mut res = val;
        res.or_lsb_assign(8, 0b0000_0000);
        assert_eq!(res, val);

        let mut res = val;
        res.or_lsb_assign(8, 0b1111_1111);
        assert_eq!(res, 0b1111_1111);

        let mut res = val;
        res.or_lsb_assign(3, 0b1111_1111);
        assert_eq!(res, 0b1010_0111);

        let mut res = val;
        res.or_lsb_assign(3, 0b0000_0000);
        assert_eq!(res, val);
    }

    #[test]
    fn test_xor_msb_u8() {
        let val = 0b1010_0011;
        assert_eq!(val.xor_msb(0, 0b1100_0011), val);
        //                                  0b1010_0011;
        assert_eq!(val.xor_msb(3, 0b1100_0101), 0b0110_0011);
        //                                                  0110_0011
        assert_eq!(val.xor_msb(8, 0b1100_0101), 0b0110_0110);
        assert_eq!(val.xor_msb(8, 0b0000_0000), val);
        assert_eq!(val.xor_msb(8, 0b1111_1111), 0b0101_1100);
        assert_eq!(val.xor_msb(3, 0b1111_1111), 0b0100_0011);
        assert_eq!(val.xor_msb(3, 0b0000_0000), val);
    }
    #[test]
    fn test_xor_msb_assign_u8() {
        let val = 0b1010_0011;

        let mut res = val;
        res.xor_msb_assign(0, 0b1100_0011);
        assert_eq!(res, val);

        let mut res = val;
        res.xor_msb_assign(3, 0b1100_0101);
        assert_eq!(res, 0b0110_0011);

        let mut res = val;
        res.xor_msb_assign(8, 0b1100_0101);
        assert_eq!(res, 0b0110_0110);

        let mut res = val;
        res.xor_msb_assign(8, 0b0000_0000);
        assert_eq!(res, val);

        let mut res = val;
        res.xor_msb_assign(8, 0b1111_1111);
        assert_eq!(res, 0b0101_1100);

        let mut res = val;
        res.xor_msb_assign(3, 0b1111_1111);
        assert_eq!(res, 0b0100_0011);

        let mut res = val;
        res.xor_msb_assign(3, 0b0000_0000);
        assert_eq!(res, val);
    }

    #[test]
    fn test_xor_lsb_u8() {
        let val = 0b1010_0011;
        assert_eq!(val.xor_lsb(0, 0b1100_0011), val);
        assert_eq!(val.xor_lsb(3, 0b1100_0101), 0b1010_0110);
        assert_eq!(val.xor_lsb(8, 0b1100_0101), 0b0110_0110);
        assert_eq!(val.xor_lsb(8, 0b0000_0000), val);
        assert_eq!(val.xor_lsb(8, 0b1111_1111), 0b0101_1100);
        assert_eq!(val.xor_lsb(3, 0b1111_1111), 0b1010_0100);
        assert_eq!(val.xor_lsb(3, 0b0000_0000), val);
    }
    #[test]
    fn test_xor_lsb_assign_u8() {
        let val = 0b1010_0011;

        let mut res = val;
        res.xor_lsb_assign(0, 0b1100_0011);
        assert_eq!(res, val);

        let mut res = val;
        res.xor_lsb_assign(3, 0b1100_0101);
        assert_eq!(res, 0b1010_0110);

        let mut res = val;
        res.xor_lsb_assign(8, 0b1100_0101);
        assert_eq!(res, 0b0110_0110);

        let mut res = val;
        res.xor_lsb_assign(8, 0b0000_0000);
        assert_eq!(res, val);

        let mut res = val;
        res.xor_lsb_assign(8, 0b1111_1111);
        assert_eq!(res, 0b0101_1100);

        let mut res = val;
        res.xor_lsb_assign(3, 0b1111_1111);
        assert_eq!(res, 0b1010_0100);

        let mut res = val;
        res.xor_lsb_assign(3, 0b0000_0000);
        assert_eq!(res, val);
    }

    #[test]
    fn test_and_partial_bool() {
        let val: u8 = 0b1011_0011;
        assert_eq!(val.and_partial(0, 8, true), val);
        assert_eq!(val.and_partial(0, 8, false), 0b0000_0000);

        assert_eq!(val.and_partial(0, 0, true), val);
        assert_eq!(val.and_partial(0, 0, false), val);

        assert_eq!(val.and_partial(0, 1, true), val);
        assert_eq!(val.and_partial(0, 1, false), 0b0011_0011);

        assert_eq!(val.and_partial(7, 1, true), val);
        assert_eq!(val.and_partial(7, 1, false), 0b1011_0010);

        assert_eq!(val.and_partial(2, 3, true), val);
        assert_eq!(val.and_partial(2, 3, false), 0b1000_0011);
    }

    #[test]
    fn test_and_partial_assign_bool() {
        let val: u8 = 0b1011_0011;

        let mut res = val;
        res.and_partial_assign(0, 8, true);
        assert_eq!(res, val);

        let mut res = val;
        res.and_partial_assign(0, 8, false);
        assert_eq!(res, 0b0000_0000);

        let mut res = val;
        res.and_partial_assign(0, 0, true);
        assert_eq!(res, val);

        let mut res = val;
        res.and_partial_assign(0, 0, false);
        assert_eq!(res, val);

        let mut res = val;
        res.and_partial_assign(0, 1, true);
        assert_eq!(res, val);

        let mut res = val;
        res.and_partial_assign(0, 1, false);
        assert_eq!(res, 0b0011_0011);

        let mut res = val;
        res.and_partial_assign(7, 1, true);
        assert_eq!(res, val);

        let mut res = val;
        res.and_partial_assign(7, 1, false);
        assert_eq!(res, 0b1011_0010);

        let mut res = val;
        res.and_partial_assign(2, 3, true);
        assert_eq!(res, val);

        let mut res = val;
        res.and_partial_assign(2, 3, false);
        assert_eq!(res, 0b1000_0011);
    }

    #[test]
    fn test_or_partial_bool() {
        let val: u8 = 0b1011_0011;
        assert_eq!(val.or_partial(0, 8, true), 0b1111_1111);
        assert_eq!(val.or_partial(0, 8, false), val);

        assert_eq!(val.or_partial(0, 0, true), val);
        assert_eq!(val.or_partial(0, 0, false), val);

        assert_eq!(val.or_partial(0, 1, true), 0b1011_0011);
        assert_eq!(val.or_partial(0, 1, false), val);

        assert_eq!(val.or_partial(7, 1, true), 0b1011_0011);
        assert_eq!(val.or_partial(7, 1, false), val);

        assert_eq!(val.or_partial(2, 3, true), 0b1011_1011);
        assert_eq!(val.or_partial(2, 3, false), val);
    }

    #[test]
    fn test_or_partial_assign_bool() {
        let val: u8 = 0b1011_0011;
        let mut res = val;
        res.or_partial_assign(0, 8, true);
        assert_eq!(res, 0b1111_1111);

        let mut res = val;
        res.or_partial_assign(0, 8, false);
        assert_eq!(res, val);

        let mut res = val;
        res.or_partial_assign(0, 0, true);
        assert_eq!(res, val);

        let mut res = val;
        res.or_partial_assign(0, 0, false);
        assert_eq!(res, val);

        let mut res = val;
        res.or_partial_assign(0, 1, true);
        assert_eq!(res, 0b1011_0011);

        let mut res = val;
        res.or_partial_assign(0, 1, false);
        assert_eq!(res, val);

        let mut res = val;
        res.or_partial_assign(7, 1, true);
        assert_eq!(res, 0b1011_0011);

        let mut res = val;
        res.or_partial_assign(7, 1, false);
        assert_eq!(res, val);

        let mut res = val;
        res.or_partial_assign(2, 3, true);
        assert_eq!(res, 0b1011_1011);

        let mut res = val;
        res.or_partial_assign(2, 3, false);
        assert_eq!(res, val);
    }

    #[test]
    fn test_xor_partial_bool() {
        let val: u8 = 0b1011_0011;
        assert_eq!(val.xor_partial(0, 8, true), 0b0100_1100);
        assert_eq!(val.xor_partial(0, 8, false), val);

        assert_eq!(val.xor_partial(0, 0, true), val);
        assert_eq!(val.xor_partial(0, 0, false), val);

        assert_eq!(val.xor_partial(0, 1, true), 0b0011_0011);
        assert_eq!(val.xor_partial(0, 1, false), val);

        assert_eq!(val.xor_partial(7, 1, true), 0b1011_0010);
        assert_eq!(val.xor_partial(7, 1, false), val);

        assert_eq!(val.xor_partial(2, 3, true), 0b1000_1011);
        assert_eq!(val.xor_partial(2, 3, false), val);
    }

    #[test]
    fn test_xor_partial_assign_bool() {
        let val: u8 = 0b1011_0011;

        let mut res = val;
        res.xor_partial_assign(0, 8, true);
        assert_eq!(res, 0b0100_1100);

        let mut res = val;
        res.xor_partial_assign(0, 8, false);
        assert_eq!(res, val);

        let mut res = val;
        res.xor_partial_assign(0, 0, true);
        assert_eq!(res, val);

        let mut res = val;
        res.xor_partial_assign(0, 0, false);
        assert_eq!(res, val);

        let mut res = val;
        res.xor_partial_assign(0, 1, true);
        assert_eq!(res, 0b0011_0011);

        let mut res = val;
        res.xor_partial_assign(0, 1, false);
        assert_eq!(res, val);

        let mut res = val;
        res.xor_partial_assign(7, 1, true);
        assert_eq!(res, 0b1011_0010);

        let mut res = val;
        res.xor_partial_assign(7, 1, false);
        assert_eq!(res, val);

        let mut res = val;
        res.xor_partial_assign(2, 3, true);
        assert_eq!(res, 0b1000_1011);

        let mut res = val;
        res.xor_partial_assign(2, 3, false);
        assert_eq!(res, val);
    }

    #[test]
    fn test_and_partial_u8() {
        let val: u8 = 0b1011_0011;
        assert_eq!(val.and_partial(0, 8, 0b1100_0101), 0b1000_0001);
        assert_eq!(val.and_partial(0, 0, 0b1100_0101), val);
        assert_eq!(val.and_partial(0, 1, 0b0100_0101), 0b0011_0011);
        assert_eq!(val.and_partial(7, 1, 0b0000_0000), 0b1011_0010);
        assert_eq!(val.and_partial(2, 3, 0b0000_0000), 0b1000_0011);
    }

    #[test]
    fn test_and_partial_assign_u8() {
        let val: u8 = 0b1011_0011;

        let mut res = val;
        res.and_partial_assign(0, 8, 0b1100_0101);
        assert_eq!(res, 0b1000_0001);

        let mut res = val;
        res.and_partial_assign(0, 0, 0b1100_0101);
        assert_eq!(res, val);

        let mut res = val;
        res.and_partial_assign(0, 1, 0b0100_0101);
        assert_eq!(res, 0b0011_0011);

        let mut res = val;
        res.and_partial_assign(7, 1, 0b0000_0000);
        assert_eq!(res, 0b1011_0010);

        let mut res = val;
        res.and_partial_assign(2, 3, 0b0000_0000);
        assert_eq!(res, 0b1000_0011);
    }

    #[test]
    fn test_or_partial_u8() {
        let val: u8 = 0b1011_0011;
        assert_eq!(val.or_partial(0, 8, 0b1100_0101), 0b1111_0111);
        assert_eq!(val.or_partial(0, 0, 0b1100_0101), val);
        assert_eq!(val.or_partial(0, 1, 0b0100_0101), 0b1011_0011);
        assert_eq!(val.or_partial(7, 1, 0b0000_0000), 0b1011_0011);
        assert_eq!(val.or_partial(2, 3, 0b0000_0000), 0b1011_0011);
    }

    #[test]
    fn test_or_partial_assign_u8() {
        let val: u8 = 0b1011_0011;

        let mut res = val;
        res.or_partial_assign(0, 8, 0b1100_0101);
        assert_eq!(res, 0b1111_0111);

        let mut res = val;
        res.or_partial_assign(0, 0, 0b1100_0101);
        assert_eq!(res, val);

        let mut res = val;
        res.or_partial_assign(0, 1, 0b0100_0101);
        assert_eq!(res, 0b1011_0011);

        let mut res = val;
        res.or_partial_assign(7, 1, 0b0000_0000);
        assert_eq!(res, 0b1011_0011);

        let mut res = val;
        res.or_partial_assign(2, 3, 0b0000_0000);
        assert_eq!(res, 0b1011_0011);
    }

    #[test]
    fn test_xor_partial_u8() {
        let val: u8 = 0b1011_0011;
        assert_eq!(val.xor_partial(0, 8, 0b1100_0101), 0b0111_0110);
        assert_eq!(val.xor_partial(0, 0, 0b1100_0101), val);
        assert_eq!(val.xor_partial(0, 1, 0b1100_0101), 0b0011_0011);
        assert_eq!(val.xor_partial(7, 1, 0b0000_0000), 0b1011_0011);
        assert_eq!(val.xor_partial(2, 3, 0b0000_0000), 0b1011_0011);
        assert_eq!(val.xor_partial(2, 3, 0b1111_1111), 0b1000_1011);
    }

    #[test]
    fn test_xor_partial_assign_u8() {
        let val: u8 = 0b1011_0011;

        let mut res = val;
        res.xor_partial_assign(0, 8, 0b1100_0101);
        assert_eq!(res, 0b0111_0110);

        let mut res = val;
        res.xor_partial_assign(0, 0, 0b1100_0101);
        assert_eq!(res, val);

        let mut res = val;
        res.xor_partial_assign(0, 1, 0b1100_0101);
        assert_eq!(res, 0b0011_0011);

        let mut res = val;
        res.xor_partial_assign(7, 1, 0b0000_0000);
        assert_eq!(res, 0b1011_0011);

        let mut res = val;
        res.xor_partial_assign(2, 3, 0b0000_0000);
        assert_eq!(res, 0b1011_0011);

        let mut res = val;
        res.xor_partial_assign(2, 3, 0b1111_1111);
        assert_eq!(res, 0b1000_1011);
    }

    macro_rules! gen_test {
        ($ty:ident, $test_name:ident) => {
            #[test]
            pub fn $test_name() {
                let bitlen = mem::size_of::<$ty>() * 8;
                let pow2: $ty = 2;

                let mut rng = rand::thread_rng();
                let rand: $ty = rng.gen::<$ty>();

                //test msb0_to_lsb0 $t
                assert_eq!(rand.as_lsb0(bitlen), rand);
                let converted = rand.as_lsb0(5);

                assert_eq!(converted, rand / pow2.pow(bitlen as u32 - 5) as $ty);

                //test lsb0_to_msb0
                let rand: $ty = converted;

                assert_eq!(rand.as_msb0(bitlen), rand);
                assert_eq!(rand.as_msb0(5), rand * pow2.pow(bitlen as u32 - 5) as $ty);
            }
        };
    }

    gen_test! {u8,test_bit_order_convert_u8}
    gen_test! {u16,test_bit_order_convert_u16}
    gen_test! {u32,test_bit_order_convert_u32}
    gen_test! {u64,test_bit_order_convert_u64}
    gen_test! {u128,test_bit_order_convert_u128}

    #[test]
    pub fn test_convert_zero() {
        let val: u8 = 0b0000_0000;
        assert_eq!(0, val.as_lsb0(0));
        assert_eq!(0, val.as_msb0(0));
    }
}
