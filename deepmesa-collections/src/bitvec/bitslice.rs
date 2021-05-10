use crate::bitvec::{bitvec::BitVector, Numbits};
use core::ops::Index;
use core::ops::Range;
use core::ops::RangeFrom;
use core::ops::RangeFull;
use core::ops::RangeInclusive;
use core::ops::RangeTo;
use core::ops::RangeToInclusive;

#[derive(Debug)]
pub struct BitSlice<'a> {
    bitvec: &'a BitVector,
    start: usize,
    end: usize,
}

pub trait Slice<R> {
    fn slice(&self, range: R) -> BitSlice;
}

impl Slice<Range<usize>> for BitVector {
    fn slice(&self, range: Range<usize>) -> BitSlice {
        return BitSlice::new(self, range.start, range.end);
    }
}

impl Slice<RangeFrom<usize>> for BitVector {
    fn slice(&self, range: RangeFrom<usize>) -> BitSlice {
        return BitSlice::new(self, range.start, self.len());
    }
}

impl Slice<RangeTo<usize>> for BitVector {
    fn slice(&self, range: RangeTo<usize>) -> BitSlice {
        return BitSlice::new(self, 0, range.end);
    }
}

impl Slice<RangeFull> for BitVector {
    fn slice(&self, _: RangeFull) -> BitSlice {
        return BitSlice::new(self, 0, self.len());
    }
}

impl Slice<RangeInclusive<usize>> for BitVector {
    fn slice(&self, range: RangeInclusive<usize>) -> BitSlice {
        return BitSlice::new(self, *range.start(), *range.end() + 1);
    }
}

impl Slice<RangeToInclusive<usize>> for BitVector {
    fn slice(&self, range: RangeToInclusive<usize>) -> BitSlice {
        return BitSlice::new(self, 0, range.end + 1);
    }
}

impl<'a> BitSlice<'a> {
    pub fn new(bitvec: &'a BitVector, start: usize, end: usize) -> BitSlice {
        if start > end {
            panic!("slice index starts at {} but ends at {}", start, end,);
        }

        if start > bitvec.len() {
            panic!(
                "slice range start index {} out of range for bitvector of length {}",
                start,
                bitvec.len()
            );
        }

        if end > bitvec.len() {
            panic!(
                "slice range end index {} out of range for bitvector of length {}",
                end,
                bitvec.len()
            );
        }

        return BitSlice { bitvec, start, end };
    }

    pub fn start(&self) -> usize {
        self.start
    }

    pub fn end(&self) -> usize {
        self.end
    }

    pub fn bit_at(&self, index: usize) -> Option<bool> {
        self.bitvec.bit_at(index)
    }

    pub fn len(&self) -> usize {
        self.end - self.start
    }

    pub fn as_u8(&self) -> (u8, Numbits) {
        self.bitvec.read_u8(self.start, self.end - self.start)
    }

    pub fn as_u16(&self) -> (u16, Numbits) {
        self.bitvec.read_u16(self.start, self.end - self.start)
    }

    pub fn as_u32(&self) -> (u32, Numbits) {
        self.bitvec.read_u32(self.start, self.end - self.start)
    }

    pub fn as_u64(&self) -> (u64, Numbits) {
        self.bitvec.read_u64(self.start, self.end - self.start)
    }

    pub fn as_u128(&self) -> (u128, Numbits) {
        self.bitvec.read_u128(self.start, self.end - self.start)
    }
}

impl<'a> Index<usize> for BitSlice<'a> {
    type Output = bool;
    fn index(&self, index: usize) -> &Self::Output {
        if index >= self.end {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                (self.end - self.start + 1),
                index
            );
        }

        match self.bit_at(self.start + index) {
            None => panic!(
                "index out of bounds: the len is {} but the index is {}",
                (self.end - self.start + 1),
                index
            ),
            Some(true) => &true,
            Some(false) => &false,
        }
    }
}
