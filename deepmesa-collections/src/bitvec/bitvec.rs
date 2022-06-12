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
    bitslice::BitSlice,
    bytes,
    iter::{Iter, IterMut, IterOnes, IterU128, IterU16, IterU32, IterU64, IterU8, IterZeros},
    traits::{AsMsb0, BitwiseClear, BitwiseClearAssign},
    BitCount, BitOrder,
};
use core::fmt;
use core::fmt::Debug;
use core::ops::BitAnd;
use core::ops::BitAndAssign;
use core::ops::BitOr;
use core::ops::BitOrAssign;
use core::ops::BitXor;
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

/// A fast contiguous growable array of bits allocated on the heap
/// that allows storing and manipulating an arbitrary number of
/// bits. This collection is backed by a [`Vector<u8>`](Vec) which
/// manages the underlying memory.
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
///
/// In addition to the [`new()`](#method.new) and
/// [`with_capacity()`](#method.with_capacity) methods, the
/// [`bitvector!`](macro.bitvector.html) macro is also provided for convenient
/// initialization.
///
/// # Examples
/// ```
/// use deepmesa::collections::BitVector;
/// use deepmesa::collections::bitvector;
///
/// let bv = bitvector![0,1,1,0];
/// assert_eq!(bv.len(), 4);
/// ```
///
/// # Memory Management
///
/// Memory is managed by an underlying [`Vec<u8>`](Vec) and all
/// methods operate on bytes whenever possible for
/// efficiency. Internally the BitVector maintains a count of the
/// number of bits currently held by the BitVector and the actual
/// number of bytes stored maybe greater than eight times the number
/// of bits. All bits stored past the number of active bits are zeroed
/// out but this is not guaranteed to be true in future versions of
/// the BitVector and should be relied up for correctness.
///
/// The BitVector can also return mutable and immutable pointers and
/// slices to the underlying [`Vec<u8>`](Vec). Modifying
/// the underlying Vector can cause undefined behavior in the
/// BitVector.
///
/// # Slices
///
/// Slices are implemented by the [`BitSlice`](BitSlice) which is a
/// view into a range within the [`BitVector`](BitVector). A BitSlice
/// is a wrapper around a slice of bytes with the 3 most significant
/// bits of the slice length used to store the bit offset into the
/// first byte of the slice. The rest of the bits of the length are
/// used to store the length of the slice in bits.
///
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
    (
        $(#[$outer:meta])*
        $iter_fn: ident, $iter_type: ident
    ) => {
        $(#[$outer])*
        pub fn $iter_fn(&self) -> $iter_type {
            $iter_type::new(&self.bits, 0, self.bit_len)
        }
    };
}

macro_rules! check_push_bounds {
    ($t: ty, $sz:literal, $bit_count: expr) => {
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
    (
        $(#[$outer:meta])*
        $i:ident, $sz: literal, $push_bits_fn: ident
    ) => {
        $(#[$outer])*
        pub fn $push_bits_fn(&mut self, val: $i, bit_count: BitCount, order: BitOrder) -> BitCount {
            if bit_count == 0 {
                return 0;
            }

            check_push_bounds!($i, $sz, bit_count);

            match order {
                BitOrder::Msb0 => self.push_bits_msb0((val as u128).as_msb0($sz), bit_count),
                BitOrder::Lsb0 => {
                    self.push_bits_msb0((val as u128).as_msb0(bit_count), bit_count)
                }
            }
        }
    };
}

macro_rules! push_unsigned {
    (
        $(#[$outer:meta])*
        $i:ident, $b: literal, $push_fn: ident
    ) => {
        $(#[$outer])*
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

            self.push_bits_msb0((val as u128).as_msb0(count), count)
        }
    };
}

macro_rules! read_unsigned {
    (
        $(#[$outer:meta])*
        $i:ident, $max_bits: literal, $read_fn: ident
    ) => {
        $(#[$outer])*
        pub fn $read_fn(&self, start: usize) -> ($i, BitCount) {
            start_bounds_check!(start, self.bit_len);
            let (val, bit_count) = bytes::read_bits(&self.bits, start, self.bit_len, $max_bits, BitOrder::Lsb0);
            (val as $i, bit_count)
        }
    };
}

macro_rules! read_bits_unsigned {
    (
        $(#[$outer:meta])*
        $i:ident, $max_bits: literal, $read_bits_fn: ident
    ) => {
        $(#[$outer])*
        pub fn $read_bits_fn(&self, start: usize, max_bits: BitCount) -> ($i, BitCount) {
            start_bounds_check!(start, self.bit_len);

            if max_bits > $max_bits {
                panic!(
                    "cannot read more than $b bits into a $i. max_bits={}",
                    max_bits
                );
            }

            match max_bits {
                0=> (0,0),
                _ => {
                    let (val, bit_count) =
                        bytes::read_bits(&self.bits, start, self.bit_len, max_bits, BitOrder::Lsb0);
                    (val as $i, bit_count)
                }
            }
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

    /// Returns the number of bits in the [`BitVector`](BitVector)
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

    /// Returns true if the [`BitVector`](BitVector) contains no bits.
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

    /// Clears the [`BitVector`](BitVector), removing all the
    /// bits. This method has no effect on the allocated capacity of
    /// the [`BitVector`](BitVector).
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

    /// Returns an iterator over the bits of this
    /// [`BitVector`](BitVector)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b101, None);
    ///
    /// let mut iter = bv.iter();
    /// assert_eq!(iter.next(), Some(true));
    /// assert_eq!(iter.next(), Some(false));
    /// assert_eq!(iter.next(), Some(true));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter {
        Iter::new(&self.bits, 0, self.bit_len)
    }

    /// Returns a mutable iterator that allows modifyingthe bits of
    /// this [`BitVector`](BitVector)
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1011_1100, Some(8));
    /// bv.push_u8(0b0011_1001, Some(8));
    /// let iter = bv.iter_mut();
    /// for mut bit in iter {
    ///     *bit = true;
    /// }
    /// assert_eq!(bv.read_u16(0), (0b1111_1111_1111_1111, 16));
    /// ```
    pub fn iter_mut(&mut self) -> IterMut {
        let len = self.len();
        IterMut::new(&mut self.bits, 0, len)
    }

    /// Counts the number of bits from the specified `start` index to
    /// the first bit set to `0`. Panics if start is non-zero and
    /// greater than or equal to the length of the `BitVector`.
    ///
    /// Returns `0` if the `BitVector` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.leading_ones(0), 0);
    ///
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b0011_1101, Some(8));
    ///
    /// assert_eq!(bv.leading_ones(0), 5);
    /// assert_eq!(bv.leading_ones(8), 0);
    /// assert_eq!(bv.leading_ones(10), 4);
    /// ```
    pub fn leading_ones(&self, start: usize) -> usize {
        match self.bit_len {
            0 => 0,
            _ => {
                start_bounds_check!(start, self.bit_len);
                bytes::leading_ones(&self.bits, start, self.bit_len)
            }
        }
    }

    /// Counts the number of bits from the specified `start` index to
    /// the first bit set to `1`. Panics if start is non-zero and
    /// greater than or equal to the length of the `BitVector`.
    ///
    /// Returns `0` if the `BitVector` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.leading_zeros(0), 0);
    ///
    /// bv.push_u8(0b0000_0111, Some(8));
    /// bv.push_u8(0b1100_0010, Some(8));
    ///
    /// assert_eq!(bv.leading_zeros(0), 5);
    /// assert_eq!(bv.leading_zeros(8), 0);
    /// assert_eq!(bv.leading_zeros(10), 4);
    /// ```
    pub fn leading_zeros(&self, start: usize) -> usize {
        match self.bit_len {
            0 => 0,
            _ => {
                start_bounds_check!(start, self.bit_len);
                bytes::leading_zeros(&self.bits, start, self.bit_len)
            }
        }
    }

    /// Counts the number of bits from end of the BitVector to the
    /// specified `start` index or to the first bit set to `0`
    /// whichever is smaller. Panics if start is non-zero and greater
    /// than or equal to the length of the `BitVector`.
    ///
    /// Returns `0` if the `BitVector` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.trailing_ones(0), 0);
    ///
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b0011_1111, Some(8));
    ///
    /// assert_eq!(bv.trailing_ones(0), 6);
    /// assert_eq!(bv.trailing_ones(8), 6);
    /// assert_eq!(bv.leading_ones(12), 4);
    /// ```
    pub fn trailing_ones(&self, start: usize) -> usize {
        match self.bit_len {
            0 => 0,
            _ => {
                start_bounds_check!(start, self.bit_len);
                bytes::trailing_ones(&self.bits, start, self.bit_len)
            }
        }
    }

    /// Counts the number of bits from end of the BitVector to the
    /// specified `start` index or to the first bit set to `1`
    /// whichever is smaller. Panics if start is non-zero and greater
    /// than or equal to the length of the `BitVector`.
    ///
    /// Returns `0` if the `BitVector` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.trailing_zeros(0), 0);
    ///
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b1100_0000, Some(8));
    ///
    /// assert_eq!(bv.trailing_zeros(0), 6);
    /// //assert_eq!(bv.trailing_zeros(8), 6);
    /// //assert_eq!(bv.trailing_zeros(12), 4);
    /// ```
    pub fn trailing_zeros(&self, start: usize) -> usize {
        match self.bit_len {
            0 => 0,
            _ => {
                start_bounds_check!(start, self.bit_len);
                bytes::trailing_zeros(&self.bits, start, self.bit_len)
            }
        }
    }

    /// Counts the number of bits from the specified `start` that are
    /// set to `1` in the BitVector. Panics if start is non-zero and
    /// greater than or equal to the length of the `BitVector`.
    ///
    /// Returns `0` if the `BitVector` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.count_ones(0), 0);
    ///
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b1100_0000, Some(8));
    ///
    /// assert_eq!(bv.count_ones(0), 7);
    /// assert_eq!(bv.count_ones(8), 2);
    /// assert_eq!(bv.count_ones(12), 0);
    /// ```
    pub fn count_ones(&self, start: usize) -> usize {
        match self.bit_len {
            0 => 0,
            _ => {
                start_bounds_check!(start, self.bit_len);
                bytes::count_ones(&self.bits, start, self.bit_len)
            }
        }
    }

    /// Counts the number of bits from the specified `start` that are
    /// set to `0` in the BitVector. Panics if start is non-zero and
    /// greater than or equal to the length of the `BitVector`.
    ///
    /// Returns `0` if the `BitVector` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.count_zeros(0), 0);
    ///
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b0000_1111, Some(8));
    ///
    /// assert_eq!(bv.count_zeros(0), 7);
    /// assert_eq!(bv.count_zeros(8), 4);
    /// assert_eq!(bv.count_zeros(12), 0);
    /// ```
    pub fn count_zeros(&self, start: usize) -> usize {
        match self.bit_len {
            0 => 0,
            _ => {
                start_bounds_check!(start, self.bit_len);
                bytes::count_zeros(&self.bits, start, self.bit_len)
            }
        }
    }

    /// Returns the index of the first bit after the specified `start`
    /// that is set to `0`. Returns `None` if the `BitVector` is empty
    /// or if there are no zero bits.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.first_zero(0), None);
    ///
    /// bv.push_u8(0b1111_1000, Some(8));
    /// bv.push_u8(0b0000_1011, Some(8));
    ///
    /// assert_eq!(bv.first_zero(0), Some(5));
    /// assert_eq!(bv.first_zero(8), Some(8));
    /// assert_eq!(bv.first_zero(12), Some(13));
    /// assert_eq!(bv.first_zero(14), None);
    /// ```
    pub fn first_zero(&self, start: usize) -> Option<usize> {
        match self.bit_len {
            0 => None,
            _ => {
                start_bounds_check!(start, self.bit_len);
                bytes::first_zero(&self.bits, start, self.bit_len)
            }
        }
    }

    /// Returns the index of the first bit after the specified `start`
    /// that is set to `1`. Returns `None` if the `BitVector` is empty
    /// or if there are no one bits.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.first_one(0), None);
    ///
    /// bv.push_u8(0b0000_0111, Some(8));
    /// bv.push_u8(0b1111_0100, Some(8));
    ///
    /// assert_eq!(bv.first_one(0), Some(5));
    /// assert_eq!(bv.first_one(8), Some(8));
    /// assert_eq!(bv.first_one(12), Some(13));
    /// assert_eq!(bv.first_one(14), None);
    /// ```
    pub fn first_one(&self, start: usize) -> Option<usize> {
        match self.bit_len {
            0 => None,
            _ => {
                start_bounds_check!(start, self.bit_len);
                bytes::first_one(&self.bits, start, self.bit_len)
            }
        }
    }

    /// Returns the index of the last bit set to `0` after the
    /// specified `start`. Returns `None` if the `BitVector` is empty
    /// or if there are no zero bits.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.last_zero(0), None);
    ///
    /// bv.push_u8(0b1101_1011, Some(8));
    ///
    /// assert_eq!(bv.last_zero(0), Some(5));
    /// assert_eq!(bv.last_zero(6), None);
    /// ```
    pub fn last_zero(&self, start: usize) -> Option<usize> {
        match self.bit_len {
            0 => None,
            _ => {
                start_bounds_check!(start, self.bit_len);
                bytes::last_zero(&self.bits, start, self.bit_len)
            }
        }
    }

    /// Returns the index of the last bit set to `1` after the
    /// specified `start`. Returns `None` if the `BitVector` is empty
    /// or if there are no one bits.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.last_one(0), None);
    ///
    /// bv.push_u8(0b0010_0100, Some(8));
    ///
    /// assert_eq!(bv.last_one(0), Some(5));
    /// assert_eq!(bv.last_one(6), None);
    /// ```
    pub fn last_one(&self, start: usize) -> Option<usize> {
        match self.bit_len {
            0 => None,
            _ => {
                start_bounds_check!(start, self.bit_len);
                bytes::last_one(&self.bits, start, self.bit_len)
            }
        }
    }

    /// Returns an immutable reference to the first bit in the
    /// `BitVector` or None if the `BitVector` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.first(), None);
    ///
    /// bv.push_u8(0b0010_0100, Some(8));
    ///
    /// assert_eq!(bv.first().as_deref(), Some(&false));
    /// ```
    pub fn first(&self) -> Option<BitRef<bool>> {
        match self.bit_len {
            0 => None,
            _ => {
                let bit = bit_at_unchecked!(0, self.bits);
                Some(BitRef::<bool>::new(bit))
            }
        }
    }

    /// Returns a mutable reference to the first bit in the
    /// `BitVector` or None if the `BitVector` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.first(), None);
    ///
    /// bv.push_u8(0b0010_0100, Some(8));
    ///
    /// assert_eq!(bv.first_mut().as_deref(), Some(&false));
    /// *bv.first_mut().unwrap() = true;
    /// assert_eq!(bv.first_mut().as_deref(), Some(&true));
    /// ```
    pub fn first_mut(&mut self) -> Option<BitRefMut<bool>> {
        match self.bit_len {
            0 => None,
            _ => {
                let bit = bit_at_unchecked!(0, self.bits);

                let byte_ptr = self.bits[0..0].as_mut_ptr();
                return Some(BitRefMut::<bool>::new(bit, byte_ptr, 0));
            }
        }
    }

    /// Returns an immutable reference to the last bit in the
    /// `BitVector` or None if the `BitVector` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.last(), None);
    ///
    /// bv.push_u8(0b0010_0101, Some(8));
    ///
    /// assert_eq!(bv.last().as_deref(), Some(&true));
    /// ```
    pub fn last(&self) -> Option<BitRef<bool>> {
        match self.bit_len {
            0 => None,
            _ => {
                let bit = bit_at_unchecked!(self.bit_len - 1, self.bits);
                Some(BitRef::<bool>::new(bit))
            }
        }
    }

    /// Returns a mutable reference to the last bit in the
    /// `BitVector` or None if the `BitVector` is empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// assert_eq!(bv.first(), None);
    ///
    /// bv.push_u8(0b0010_0101, Some(8));
    ///
    /// assert_eq!(bv.last_mut().as_deref(), Some(&true));
    /// *bv.last_mut().unwrap() = false;
    /// assert_eq!(bv.last_mut().as_deref(), Some(&false));
    /// ```
    pub fn last_mut(&mut self) -> Option<BitRefMut<bool>> {
        match self.bit_len {
            0 => None,
            _ => {
                let bit_idx = self.len() - 1;
                let bit = bit_at_unchecked!(bit_idx, self.bits);

                let byte_idx = bit_idx / 8;
                let byte_ptr = self.bits[byte_idx..byte_idx].as_mut_ptr();
                return Some(BitRefMut::<bool>::new(bit, byte_ptr, bit_idx));
            }
        }
    }

    /// Iterates over all the bits in the `BitVector` that are set to
    /// `1`.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b0010_0101, Some(8));
    ///
    /// let mut iter = bv.iter_ones();
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(5));
    /// assert_eq!(iter.next(), Some(7));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_ones(&self) -> IterOnes {
        IterOnes::new(&self.bits, 0, self.bit_len)
    }

    /// Iterates over all the bits in the `BitVector` that are set to
    /// `0`.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::with_capacity(20);
    /// bv.push_u8(0b1101_1010, Some(8));
    ///
    /// let mut iter = bv.iter_zeros();
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(5));
    /// assert_eq!(iter.next(), Some(7));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_zeros(&self) -> IterZeros {
        IterZeros::new(&self.bits, 0, self.bit_len)
    }

    iter_unsigned!(
        /// Returns an iterator that iterates over the
        /// [`BitVector`](BitVector) 8 bits at a time. Each invocation
        /// of `iter.next` returns a [`u8`] value and the number of bits
        /// read.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
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
        /// let mut iter = bv.iter_u8();
        /// assert_eq!(iter.next(), Some((0b0101_1101, 8)));
        /// assert_eq!(iter.next(), Some((0b0011_1010, 8)));
        /// assert_eq!(iter.next(), None);
        /// ```
        iter_u8,
        IterU8
    );
    iter_unsigned!(
        /// Returns an iterator that iterates over the bitvector 16
        /// bits at a time. Each invocation of `iter.next` returns a
        /// [`u16`] value and the number of bits read.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
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
        /// let mut iter = bv.iter_u16();
        /// assert_eq!(iter.next(), Some((0b0101_1101_0011_1010, 16)));
        /// assert_eq!(iter.next(), None);
        /// ```
        iter_u16,
        IterU16
    );
    iter_unsigned!(
        /// Returns an iterator that iterates over the bitvector 32
        /// bits at a time. Each invocation of `iter.next` returns a
        /// [`u32`] value and the number of bits read.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
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
        /// let mut iter = bv.iter_u32();
        /// assert_eq!(iter.next(), Some((0b0101_1101_0011_1010_1111_0011_1100_0000, 32)));
        /// assert_eq!(iter.next(), None);
        /// ```
        iter_u32,
        IterU32
    );
    iter_unsigned!(
        /// Returns an iterator that iterates over the bitvector 64
        /// bits at a time. Each invocation of `iter.next` returns a
        /// [`u64`] value and the number of bits read.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
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
        /// let mut iter = bv.iter_u64();
        /// assert_eq!(iter.next(), Some((u64::MAX, 64)));
        /// assert_eq!(iter.next(), None);
        /// ```
        iter_u64,
        IterU64
    );
    iter_unsigned!(
        /// Returns an iterator that iterates over the bitvector 128
        /// bits at a time. Each invocation of `iter.next` returns a
        /// [`u128`] value and the number of bits read.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
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
        /// let mut iter = bv.iter_u128();
        /// assert_eq!(iter.next(), Some((u128::MAX, 128)));
        /// assert_eq!(iter.next(), None);
        /// ```
        iter_u128,
        IterU128
    );

    read_unsigned!(
        /// Reads upto 8 bits from this [`BitVector`](BitVector) into
        /// a [`u8`] starting at the specified `start` position. This
        /// method will panic if `start` is greater than or equal to
        /// the length of the BitVector.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u8(0b0011_0110, Some(8));
        ///
        /// let (val, read) = bv.read_u8(0);
        /// assert_eq!(read, 8);
        /// assert_eq!(val, 0b0011_0110);
        ///
        /// let (val, read) = bv.read_u8(4);
        /// assert_eq!(read, 4);
        /// assert_eq!(val, 0b0000_0110);
        /// ```
        u8,
        8,
        read_u8
    );
    read_unsigned!(
        /// Reads upto 16 bits from this [`BitVector`](BitVector) into
        /// a [`u16`] starting at the specified `start` position. This
        /// method will panic if `start` is greater than or equal to
        /// the length of the BitVector.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// let mut bv = BitVector::new();
        /// bv.push_u16(0b0011_0110_1100_0011, Some(16));
        ///
        /// let (val, read) = bv.read_u16(0);
        /// assert_eq!(read, 16);
        /// assert_eq!(val, 0b0011_0110_1100_0011);
        ///
        /// let (val, read) = bv.read_u16(4);
        /// assert_eq!(read, 12);
        /// assert_eq!(val, 0b0000_0110_1100_0011);
        /// ```
        u16,
        16,
        read_u16
    );
    read_unsigned!(
        /// Reads upto 32 bits from this [`BitVector`](BitVector) into
        /// a [`u32`] starting at the specified `start` position. This
        /// method will panic if `start` is greater than or equal to
        /// the length of the BitVector.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
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
        /// let (val, read) = bv.read_u32(0);
        /// assert_eq!(read, 32);
        //
        /// assert_eq!(val, 0b0011_0110_1100_0011_1100_1010_0100_1100);
        ///
        /// let (val, read) = bv.read_u16(16);
        /// assert_eq!(read, 16);
        /// assert_eq!(val, 0b1100_1010_0100_1100);
        /// ```
        u32,
        32,
        read_u32
    );
    read_unsigned!(
        /// Reads upto 64 bits from this [`BitVector`](BitVector) into
        /// a [`u64`] starting at the specified `start` position. This
        /// method will panic if `start` is greater than or equal to
        /// the length of the BitVector.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
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
        /// let (val, read) = bv.read_u64(20);
        /// assert_eq!(read, 12);
        //
        /// assert_eq!(val, 0b1010_0100_1100);
        ///
        /// let (val, read) = bv.read_u64(16);
        /// assert_eq!(read, 16);
        /// assert_eq!(val, 0b1100_1010_0100_1100);
        /// ```
        u64,
        64,
        read_u64
    );
    read_unsigned!(
        /// Reads upto 128 bits from this [`BitVector`](BitVector)
        /// into a [`u128`] starting at the specified `start`
        /// position. This method will panic if `start` is greater
        /// than or equal to the length of the BitVector.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
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
        /// let (val, read) = bv.read_u128(20);
        /// assert_eq!(read, 12);
        //
        /// assert_eq!(val, 0b1010_0100_1100);
        ///
        /// let (val, read) = bv.read_u128(16);
        /// assert_eq!(read, 16);
        /// assert_eq!(val, 0b1100_1010_0100_1100);
        /// ```
        u128,
        128,
        read_u128
    );

    read_bits_unsigned!(
        /// Reads upto `max_bits` bits from this
        /// [`BitVector`](BitVector) into a [`u8`] starting at the
        /// specified `start` position. This method will panic if
        /// `max_bits` is greater than 8 or if `start` is greater than
        /// or equal to the length of the BitVector.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// Here is an illustrative example for a bitvector with 8
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
        /// let (val, read) = bv.read_bits_u8(2, 4);
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
        /// [`BitVector`](BitVector) into a [`u16`] starting at the
        /// specified `start` position. This method will panic if
        /// `max_bits` is greater than 16 or if `start` is greater
        /// than or equal to the length of the BitVector.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// Here is an illustrative example for a bitvector with 8
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
        /// let (val, read) = bv.read_bits_u16(2, 4);
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
        /// [`BitVector`](BitVector) into a [`u32`] starting at the
        /// specified `start` position. This method will panic if
        /// `max_bits` is greater than 32 or if `start` is greater
        /// than or equal to the length of the BitVector.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// Here is an illustrative example for a bitvector with 8
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
        /// let (val, read) = bv.read_bits_u32(2, 4);
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
        /// [`BitVector`](BitVector) into a [`u64`] starting at the
        /// specified `start` position. This method will panic if
        /// `max_bits` is greater than 64 or if `start` is greater
        /// than or equal to the length of the BitVector.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// Here is an illustrative example for a bitvector with 8
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
        /// let (val, read) = bv.read_bits_u64(2, 4);
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
        /// [`BitVector`](BitVector) into a [`u128`] starting at the
        /// specified `start` position. This method will panic if
        /// `max_bits` is greater than 128 or if `start` is greater
        /// than or equal to the length of the BitVector.
        ///
        /// The bits are read from the lower to the higher index from
        /// the BitVector and shifted right, so the bit at the lower
        /// index is the MSB of returned value while the bit at the
        /// highest index is the LSB.
        ///
        /// Here is an illustrative example for a bitvector with 8
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
        /// let (val, read) = bv.read_bits_u128(2, 4);
        /// assert_eq!(read,4);
        /// assert_eq!(val, 0b0000_1101);
        /// assert_eq!(val, 13);
        /// ```
        ///
        u128,
        128,
        read_bits_u128
    );

    push_bits_unsigned!(
        /// Pushes at most `count` bits from the specified [`u8`] `val` to
        /// the end of the BitVector. The bits to be pushed are
        /// counted depending on the `order`. If the `count` is equal
        /// to 8 the order is ignored and all bits are pushed from the
        /// MSB (bit position 7) to the LSB (bit position 0). If the
        /// count is less than 8, then the bits are pushed in the
        /// specified Order as follows:
        ///
        /// If the order is Msb0, the leading `count` bits starting from the
        /// MSB (from bit position 7) are pushed to the end of the
        /// BitVector
        ///
        /// If the order is Lsb0, then trailing `count` bits starting from
        /// the LSB (from bit position 0) are pushed to the end of the
        /// BitVector.
        ///
        /// This method will panic, if the count is greater than 8. If
        /// the `count` is 0, then no bits are pushed and the method
        /// has no effect.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// use deepmesa::collections::bitvec::BitOrder;
        ///
        /// let mut bv = BitVector::new();
        /// let val:u8 = 0b1100_0101;
        /// bv.push_bits_u8(val, 3, BitOrder::Msb0);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], true);
        /// assert_eq!(bv[2], false);
        ///
        /// bv.clear();
        /// bv.push_bits_u8(val, 3, BitOrder::Lsb0);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        ///
        /// ```
        u8,
        8,
        push_bits_u8
    );

    push_bits_unsigned!(
        /// Pushes at most `count` bits from the specified [`u16`]
        /// `val` to the end of the BitVector. The bits to be pushed
        /// are counted depending on the `order`. If the `count` is
        /// equal to 16 the order is ignored and all bits are pushed
        /// from the MSB (bit position 15) to the LSB (bit position
        /// 0). If the count is less than 16, then the bits are pushed
        /// in the specified Order as follows:
        ///
        /// If the order is Msb0, the leading `count` bits starting from the
        /// MSB (from bit position 15) are pushed to the end of the
        /// BitVector
        ///
        /// If the order is Lsb0, then trailing `count` bits starting from
        /// the LSB (from bit position 0) are pushed to the end of the
        /// BitVector.
        ///
        /// This method will panic, if the count is greater than
        /// 16. If the `count` is 0, then no bits are pushed and the
        /// method has no effect.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// use deepmesa::collections::bitvec::BitOrder;
        ///
        /// let mut bv = BitVector::new();
        /// let val:u16 = 0b1100_0000_0000_0101;
        /// bv.push_bits_u16(val, 3, BitOrder::Msb0);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], true);
        /// assert_eq!(bv[2], false);
        ///
        /// bv.clear();
        /// bv.push_bits_u16(val, 3, BitOrder::Lsb0);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        ///
        /// ```
        u16,
        16,
        push_bits_u16
    );
    push_bits_unsigned!(
        /// Pushes at most `count` bits from the specified [`u32`]
        /// `val` to the end of the BitVector. The bits to be pushed
        /// are counted depending on the `order`. If the `count` is
        /// equal to 32 the order is ignored and all bits are pushed
        /// from the MSB (bit position 31) to the LSB (bit position
        /// 0). If the count is less than 32, then the bits are pushed
        /// in the specified Order as follows:
        ///
        /// If the order is Msb0, the leading `count` bits starting from the
        /// MSB (from bit position 31) are pushed to the end of the
        /// BitVector
        ///
        /// If the order is Lsb0, then trailing `count` bits starting from
        /// the LSB (from bit position 0) are pushed to the end of the
        /// BitVector.
        ///
        /// This method will panic, if the count is greater than
        /// 32. If the `count` is 0, then no bits are pushed and the
        /// method has no effect.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// use deepmesa::collections::bitvec::BitOrder;
        ///
        /// let mut bv = BitVector::new();
        /// let val:u32 = 0b1100_0000_0000_0000_0000_0000_0000_0101;
        /// bv.push_bits_u32(val, 3, BitOrder::Msb0);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], true);
        /// assert_eq!(bv[2], false);
        ///
        /// bv.clear();
        /// bv.push_bits_u32(val, 3, BitOrder::Lsb0);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        ///
        /// ```
        u32,
        32,
        push_bits_u32
    );
    push_bits_unsigned!(
        /// Pushes at most `count` bits from the specified [`u64`] `val` to
        /// the end of the BitVector. The bits to be pushed are
        /// counted depending on the `order`. If the `count` is equal
        /// to 64 the order is ignored and all bits are pushed from the
        /// MSB (bit position 63) to the LSB (bit position 0). If the
        /// count is less than 64, then the bits are pushed in the
        /// specified Order as follows:
        ///
        /// If the order is Msb0, the leading `count` bits starting from the
        /// MSB (from bit position 63) are pushed to the end of the
        /// BitVector
        ///
        /// If the order is Lsb0, then trailing `count` bits starting from
        /// the LSB (from bit position 0) are pushed to the end of the
        /// BitVector.
        ///
        /// This method will panic, if the count is greater than
        /// 64. If the `count` is 0, then no bits are pushed and the
        /// method has no effect.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// use deepmesa::collections::bitvec::BitOrder;
        ///
        /// let mut bv = BitVector::new();
        /// // 4 MSB bits are 1100 and 4 LSB bits are 0101
        /// let val:u64 = 0xc0_00_00_00_00_00_00_05;
        /// bv.push_bits_u64(val, 3, BitOrder::Msb0);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], true);
        /// assert_eq!(bv[2], false);
        ///
        /// bv.clear();
        /// bv.push_bits_u64(val, 3, BitOrder::Lsb0);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        ///
        /// ```
        u64,
        64,
        push_bits_u64
    );
    push_bits_unsigned!(
        /// Pushes at most `count` bits from the specified [`u128`]
        /// `val` to the end of the BitVector. The bits to be pushed
        /// are counted depending on the `order`. If the `count` is
        /// equal to 128 the order is ignored and all bits are pushed
        /// from the MSB (bit position 127) to the LSB (bit position
        /// 0). If the count is less than 128, then the bits are
        /// pushed in the specified Order as follows:
        ///
        /// If the order is Msb0, the leading `count` bits starting from the
        /// MSB (from bit position 127) are pushed to the end of the
        /// BitVector
        ///
        /// If the order is Lsb0, then trailing `count` bits starting from
        /// the LSB (from bit position 0) are pushed to the end of the
        /// BitVector.
        ///
        /// This method will panic, if the count is greater than
        /// 128. If the `count` is 0, then no bits are pushed and the
        /// method has no effect.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        /// use deepmesa::collections::bitvec::BitOrder;
        ///
        /// let mut bv = BitVector::new();
        /// // 4 MSB bits are 1100 and 4 LSB bits are 0101
        /// let val:u128 = 0xc0_00_00_00_00_00_00_00_00_00_00_00_00_00_00_05;
        /// bv.push_bits_u128(val, 3, BitOrder::Msb0);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], true);
        /// assert_eq!(bv[2], false);
        ///
        /// bv.clear();
        /// bv.push_bits_u128(val, 3, BitOrder::Lsb0);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        ///
        /// ```
        u128,
        128,
        push_bits_u128
    );

    push_unsigned!(
        /// Pushes bits from the specified [`u8`] `val` excluding the
        /// leading zeros unless the `min_width` is specified. The
        /// `min_width` is the minimum number of bits to push
        /// (including leading zeros for padding). If the `min_width`
        /// is specified, then leading zeros are pushed before pushing
        /// the bits in the u8 to the BitVector.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        ///
        /// let mut bv = BitVector::new();
        /// let val:u8 = 0b101;
        /// bv.push_u8(val, None);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        ///
        /// bv.clear();
        /// bv.push_u8(val, Some(5));
        /// assert_eq!(bv.len(), 5);
        /// assert_eq!(bv[0], false);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        /// assert_eq!(bv[3], false);
        /// assert_eq!(bv[4], true);
        /// ```
        u8,
        8,
        push_u8
    );
    push_unsigned!(
        /// Pushes bits from the specified [`u16`] `val` excluding the
        /// leading zeros unless the `min_width` is specified. The
        /// `min_width` is the minimum number of bits to push
        /// (including leading zeros for padding). If the `min_width`
        /// is specified, then leading zeros are pushed before pushing
        /// the bits in the u16 to the BitVector.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        ///
        /// let mut bv = BitVector::new();
        /// let val:u16 = 0b101;
        /// bv.push_u16(val, None);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        ///
        /// bv.clear();
        /// bv.push_u16(val, Some(5));
        /// assert_eq!(bv.len(), 5);
        /// assert_eq!(bv[0], false);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        /// assert_eq!(bv[3], false);
        /// assert_eq!(bv[4], true);
        /// ```
        u16,
        16,
        push_u16
    );
    push_unsigned!(
        /// Pushes bits from the specified [`u32`] `val` excluding the
        /// leading zeros unless the `min_width` is specified. The
        /// `min_width` is the minimum number of bits to push
        /// (including leading zeros for padding). If the `min_width`
        /// is specified, then leading zeros are pushed before pushing
        /// the bits in the u32 to the BitVector.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        ///
        /// let mut bv = BitVector::new();
        /// let val:u32 = 0b101;
        /// bv.push_u32(val, None);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        ///
        /// bv.clear();
        /// bv.push_u32(val, Some(5));
        /// assert_eq!(bv.len(), 5);
        /// assert_eq!(bv[0], false);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        /// assert_eq!(bv[3], false);
        /// assert_eq!(bv[4], true);
        /// ```
        u32,
        32,
        push_u32
    );
    push_unsigned!(
        /// Pushes bits from the specified [`u64`] `val` excluding the
        /// leading zeros unless the `min_width` is specified. The
        /// `min_width` is the minimum number of bits to push
        /// (including leading zeros for padding). If the `min_width`
        /// is specified, then leading zeros are pushed before pushing
        /// the bits in the u64 to the BitVector.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        ///
        /// let mut bv = BitVector::new();
        /// let val:u64 = 0b101;
        /// bv.push_u64(val, None);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        ///
        /// bv.clear();
        /// bv.push_u64(val, Some(5));
        /// assert_eq!(bv.len(), 5);
        /// assert_eq!(bv[0], false);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        /// assert_eq!(bv[3], false);
        /// assert_eq!(bv[4], true);
        /// ```
        u64,
        64,
        push_u64
    );
    push_unsigned!(
        /// Pushes bits from the specified [`u128`] `val` excluding the
        /// leading zeros unless the `min_width` is specified. The
        /// `min_width` is the minimum number of bits to push
        /// (including leading zeros for padding). If the `min_width`
        /// is specified, then leading zeros are pushed before pushing
        /// the bits in the u128 to the BitVector.
        ///
        /// # Examples
        /// ```
        /// use deepmesa::collections::BitVector;
        ///
        /// let mut bv = BitVector::new();
        /// let val:u128 = 0b101;
        /// bv.push_u128(val, None);
        /// assert_eq!(bv.len(), 3);
        /// assert_eq!(bv[0], true);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        ///
        /// bv.clear();
        /// bv.push_u128(val, Some(5));
        /// assert_eq!(bv.len(), 5);
        /// assert_eq!(bv[0], false);
        /// assert_eq!(bv[1], false);
        /// assert_eq!(bv[2], true);
        /// assert_eq!(bv[3], false);
        /// assert_eq!(bv[4], true);
        /// ```
        u128,
        128,
        push_u128
    );

    /// Returns an immutable reference to a [BitSlice](BitSlice)
    /// containing all the bits of the BitVector. This call is
    /// equivalent to &bv[..].
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b1011_1100, None);
    /// let slice = bv.as_bitslice();
    /// assert_eq!(slice.len(), 8);
    /// let slice = &bv[..];
    /// assert_eq!(slice.len(), 8);
    /// ```
    pub fn as_bitslice(&self) -> &BitSlice {
        self.index(0..self.bit_len)
    }

    /// Returns a mutable reference to a [BitSlice](BitSlice)
    /// containing all the bits of the BitVector. This call is
    /// equivalent to &mut bv[..].
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b1011_1100, None);
    /// let slice = bv.as_mut_bitslice();
    /// assert_eq!(slice.len(), 8);
    /// let slice = &mut bv[..];
    /// assert_eq!(slice.len(), 8);
    /// ```
    pub fn as_mut_bitslice(&mut self) -> &mut BitSlice {
        self.index_mut(0..self.bit_len)
    }

    /// Returns an immutable slice of the underlying [`Vec<u8>`](Vec)
    /// containing the u8 values that encode the bits of the
    /// BitVector. Reading the bytes directly from this raw slice is
    /// not recommended since the BitVector manages the bytes in the
    /// underlying [`Vector`](Vec).
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b0100_1101, Some(8));
    /// let raw_slice = bv.as_raw_slice();
    /// assert_eq!(raw_slice.len(), 1);
    /// assert_eq!(raw_slice, &[0x4D]);
    /// ```
    pub fn as_raw_slice(&self) -> &[u8] {
        unsafe {
            let ptr = self.bits.as_ptr();
            std::slice::from_raw_parts(ptr, self.bits.len())
        }
    }

    /// Returns a mutable slice of the underlying [`Vec<u8>`](Vec)
    /// containing the u8 values that encode the bits of the
    /// BitVector. Reading from or modifying the bytes directly in
    /// this raw slice is not recommended since the BitVector manages
    /// the bytes in the underlying [`Vector`](Vec).
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b0100_1101, Some(8));
    /// let raw_slice = bv.as_mut_raw_slice();
    /// assert_eq!(raw_slice.len(), 1);
    /// assert_eq!(raw_slice, &[0x4D]);
    /// ```
    pub fn as_mut_raw_slice(&mut self) -> &mut [u8] {
        unsafe {
            let ptr = self.bits.as_mut_ptr();
            std::slice::from_raw_parts_mut(ptr, self.bits.len())
        }
    }

    /// Returns a raw pointer to the underlying [`Vec<u8>`](Vec) containing
    /// the u8 values that encode the bits of the BitVector. Reading
    /// from the bytes directly from this raw pointer is not
    /// recommended since the BitVector manages the bytes in the
    /// underlying [`Vector`](Vec).
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b0100_1101, Some(8));
    /// let raw_ptr = bv.as_raw_ptr();
    /// ```
    pub fn as_raw_ptr(&self) -> *const u8 {
        self.bits.as_ptr()
    }

    /// Returns a mutable raw pointer to the underlying [`Vec<u8>`](Vec)
    /// containing the u8 values that encode the bits of the
    /// BitVector. Reading from or writing to the bytes directly in
    /// this raw pointer is not recommended since the BitVector
    /// manages the bytes in the underlying [`Vector`](Vec).
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b0100_1101, Some(8));
    /// let raw_ptr = bv.as_mut_raw_ptr();
    /// ```
    pub fn as_mut_raw_ptr(&mut self) -> *mut u8 {
        self.bits.as_mut_ptr()
    }

    /// Moves all the bits of `other` into `self`, leaving `other`
    /// empty.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b1101, None);
    /// let mut other = BitVector::new();
    /// other.push_u8(0b1111_0011, Some(8));
    /// bv.append(&mut other);
    /// assert_eq!(bv.len(), 12);
    /// assert_eq!(other.len(), 0);
    /// ```
    pub fn append(&mut self, other: &mut BitVector) {
        let mut iter = other.iter_u8();
        while let Some((val, bitcount)) = iter.next() {
            self.push_u8(val, Some(bitcount));
        }

        other.clear()
    }

    /// Copies all the bits from the specified [BitSlice] into the
    /// BitVector.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b1101, None);
    /// let mut other = BitVector::new();
    /// other.push_u8(0b1111_0011, Some(8));
    /// let other_slice = &other[..];
    /// bv.extend_from_bitslice(other_slice);
    /// assert_eq!(bv.len(), 12);
    /// ```
    pub fn extend_from_bitslice(&mut self, other: &BitSlice) {
        let mut iter = other.iter_u8();
        while let Some((val, bitcount)) = iter.next() {
            self.push_u8(val, Some(bitcount));
        }
    }

    /// Creates a new BitVector by copying the contents of the
    /// specified [BitSlice].
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.push_u8(0b1101, None);
    ///
    /// let bv2 = BitVector::from_bitslice(&bv[..]);
    /// assert_eq!(bv2.len(), 4);
    /// ```
    pub fn from_bitslice(slice: &BitSlice) -> Self {
        let mut bv = BitVector::with_capacity(slice.len());
        let mut iter = slice.iter_u8();
        while let Some((val, bitcount)) = iter.next() {
            bv.push_u8(val, Some(bitcount));
        }
        bv
    }

    /// Creates a new BitVector with a bit repeated `len` times
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let bv = BitVector::repeat(true, 4);
    /// assert_eq!(bv.len(), 4);
    /// ```
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
    /// specified index is set or `None` if the index is greater than
    /// or equal to the number of bits in the BitVector.
    ///
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

        return Some(bit_at_unchecked!(index, self.bits));
    }

    pub fn get_mut(&mut self, index: usize) -> Option<BitRefMut<bool>> {
        if index >= self.bit_len {
            return None;
        }
        let bit = bit_at_unchecked!(index, self.bits);

        let byte_idx = index / 8;
        let byte_ptr = self.bits[byte_idx..byte_idx].as_mut_ptr();
        return Some(BitRefMut::<bool>::new(bit, byte_ptr, index));
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

    /// Extends the BitVector by pushing the specified `bit`, `count`
    /// times to the end of the BitVector.
    ///
    /// # Examples
    /// ```
    /// use deepmesa::collections::BitVector;
    ///
    /// let mut bv = BitVector::new();
    /// bv.fill(true, 4);
    /// assert_eq!(bv.len(), 4);
    /// ```
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
            "BitVector {{ bit_len: {}, capacity_bits: {}, bits:\n",
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
                            b_expr!(*byte $op (s_byte).as_msb0(s_bits));
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
    use crate::bitvector;
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
    }

    #[test]
    fn test_get_mut() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1011_1100, None);
        assert_eq!(bv[2], true);
        *bv.get_mut(2).unwrap() = false;
        assert_eq!(bv[2], false);

        assert_eq!(bv[7], false);
        *bv.get_mut(7).unwrap() = true;
        assert_eq!(bv[7], true);
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
    fn test_read_bits_bounds_exceeds() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1011_0101_0011_1100, Some(16));
        bv.read_bits_u8(19, 5);
    }

    #[test]
    #[should_panic(expected = "start index 16 out of range for length 16")]
    fn test_read_bits_bounds_equals() {
        let mut bv = BitVector::with_capacity(128);
        bv.push_u16(0b1011_0101_0011_1100, Some(16));
        bv.read_bits_u8(16, 5);
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
        let bv = bitvector!();
        assert_eq!(bv.len(), 0);
        let bv = bitvector![1, 0, 1, 1];
        assert_eq!(bv.len(), 4);
        assert_eq!(bv.read_u8(0), (0b1011, 4));
        let bv = bitvector![1;100];
        assert_eq!(bv.len(), 100);
        assert_eq!(bv.read_u64(0), (u64::MAX, 64));
        assert_eq!(bv.read_u32(64), (u32::MAX, 32));
        assert_eq!(bv.read_u8(96), (0b1111, 4));
    }

    #[test]
    fn test_iter_mut() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1011_1100, Some(8));
        bv.push_u8(0b0011_1001, Some(8));
        let iter = bv.iter_mut();
        for mut bit in iter {
            *bit = true;
        }

        assert_eq!(bv.read_u8(0), (0b1111_1111, 8));
        assert_eq!(bv.read_u8(8), (0b1111_1111, 8));
        for mut bit in bv.iter_mut() {
            *bit = false;
        }
        assert_eq!(bv.read_u8(0), (0b0000_0000, 8));
        assert_eq!(bv.read_u8(8), (0b0000_0000, 8));
    }

    #[test]
    fn test_first() {
        let mut bv = BitVector::with_capacity(20);
        assert_eq!(bv.first(), None);

        bv.push_u8(0b1011_1100, None);
        assert_eq!(bv[0], true);
        assert_eq!(*(bv.first().unwrap()), true);
        assert_eq!(bv.first().as_deref(), Some(&true));
    }

    #[test]
    fn test_first_mut() {
        let mut bv = BitVector::with_capacity(20);
        assert_eq!(bv.first_mut(), None);
        bv.push_u8(0b1011_1100, None);
        assert_eq!(bv[0], true);
        assert_eq!(*(bv.first_mut().unwrap()), true);
        *bv.first_mut().unwrap() = false;
        assert_eq!(*(bv.first_mut().unwrap()), false);
        assert_eq!(bv.first().as_deref(), Some(&false));
        assert_eq!(bv[0], false);
    }

    #[test]
    fn test_last() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b1011_1100, None);
        assert_eq!(bv[7], false);
        assert_eq!(*(bv.last().unwrap()), false);
        assert_eq!(bv.last().as_deref(), Some(&false));
        assert_eq!(bv[7], false);
    }

    #[test]
    fn test_last_mut() {
        let mut bv = BitVector::with_capacity(20);
        bv.push_u8(0b0000_0000, Some(8));
        assert_eq!(bv[7], false);
        assert_eq!(*(bv.last_mut().unwrap()), false);
        *bv.last_mut().unwrap() = true;
        assert_eq!(*(bv.last().unwrap()), true);
        assert_eq!(bv.last().as_deref(), Some(&true));
        assert_eq!(bv[7], true);
    }

    #[test]
    fn test_count_ones() {
        let bv = BitVector::new();
        assert_eq!(bv.count_ones(0), 0);
    }

    #[test]
    fn test_count_zeros() {
        let bv = BitVector::new();
        assert_eq!(bv.count_zeros(0), 0);
    }
}
