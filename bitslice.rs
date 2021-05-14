use crate::bitvec::{bitvec::BitVector, Numbits, Slice, SliceMut};
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
    len: usize,
}

#[derive(Debug)]
pub struct BitSliceMut<'a> {
    bitvec: &'a mut BitVector,
    start: usize,
    len: usize,
}

fn check_bounds(start: usize, end: usize, len: usize) {
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

impl Slice<Range<usize>> for BitVector {
    fn slice(&self, range: Range<usize>) -> BitSlice {
        check_bounds(range.start, range.end, self.len());
        return BitSlice::new(self, range.start, range.end - range.start);
    }
}

impl Slice<RangeFrom<usize>> for BitVector {
    fn slice(&self, range: RangeFrom<usize>) -> BitSlice {
        check_bounds(range.start, self.len(), self.len());
        return BitSlice::new(self, range.start, self.len() - range.start);
    }
}

impl Slice<RangeTo<usize>> for BitVector {
    fn slice(&self, range: RangeTo<usize>) -> BitSlice {
        check_bounds(0, range.end, self.len());
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
        check_bounds(*range.start(), *range.end() + 1, self.len());
        return BitSlice::new(self, *range.start(), *range.end() - *range.start() + 1);
    }
}

impl Slice<RangeToInclusive<usize>> for BitVector {
    fn slice(&self, range: RangeToInclusive<usize>) -> BitSlice {
        check_bounds(0, range.end + 1, self.len());
        return BitSlice::new(self, 0, range.end + 1);
    }
}

impl SliceMut<Range<usize>> for BitVector {
    fn slice_mut(&mut self, range: Range<usize>) -> BitSliceMut {
        check_bounds(range.start, range.end, self.len());
        return BitSliceMut::new(self, range.start, range.end - range.start);
    }
}

impl SliceMut<RangeFrom<usize>> for BitVector {
    fn slice_mut(&mut self, range: RangeFrom<usize>) -> BitSliceMut {
        check_bounds(range.start, self.len(), self.len());
        return BitSliceMut::new(self, range.start, self.len() - range.start);
    }
}

impl SliceMut<RangeTo<usize>> for BitVector {
    fn slice_mut(&mut self, range: RangeTo<usize>) -> BitSliceMut {
        check_bounds(0, range.end, self.len());
        return BitSliceMut::new(self, 0, range.end);
    }
}

impl SliceMut<RangeFull> for BitVector {
    fn slice_mut(&mut self, _: RangeFull) -> BitSliceMut {
        return BitSliceMut::new(self, 0, self.len());
    }
}

impl SliceMut<RangeInclusive<usize>> for BitVector {
    fn slice_mut(&mut self, range: RangeInclusive<usize>) -> BitSliceMut {
        check_bounds(*range.start(), *range.end() + 1, self.len());
        return BitSliceMut::new(self, *range.start(), *range.end() - *range.start() + 1);
    }
}

impl SliceMut<RangeToInclusive<usize>> for BitVector {
    fn slice_mut(&mut self, range: RangeToInclusive<usize>) -> BitSliceMut {
        check_bounds(0, range.end + 1, self.len());
        return BitSliceMut::new(self, 0, range.end + 1);
    }
}

impl<'a> Slice<Range<usize>> for BitSlice<'a> {
    fn slice(&self, range: Range<usize>) -> BitSlice {
        check_bounds(range.start, range.end, self.len());
        return BitSlice::new(
            self.bitvec,
            self.start + range.start,
            range.end - range.start,
        );
    }
}

impl<'a> Slice<RangeFrom<usize>> for BitSlice<'a> {
    fn slice(&self, range: RangeFrom<usize>) -> BitSlice {
        check_bounds(range.start, self.len(), self.len());
        let start = self.start + range.start;
        return BitSlice::new(self.bitvec, start, self.len() - range.start);
    }
}

impl<'a> Slice<RangeTo<usize>> for BitSlice<'a> {
    fn slice(&self, range: RangeTo<usize>) -> BitSlice {
        check_bounds(0, range.end, self.len());
        return BitSlice::new(self.bitvec, self.start, range.end);
    }
}

impl<'a> Slice<RangeFull> for BitSlice<'a> {
    fn slice(&self, _: RangeFull) -> BitSlice {
        return BitSlice::new(self.bitvec, self.start, self.len);
    }
}

impl<'a> Slice<RangeInclusive<usize>> for BitSlice<'a> {
    fn slice(&self, range: RangeInclusive<usize>) -> BitSlice {
        check_bounds(*range.start(), *range.end() + 1, self.len());
        return BitSlice::new(
            self.bitvec,
            self.start + *range.start(),
            *range.end() - *range.start() + 1,
        );
    }
}

impl<'a> Slice<RangeToInclusive<usize>> for BitSlice<'a> {
    fn slice(&self, range: RangeToInclusive<usize>) -> BitSlice {
        check_bounds(0, range.end + 1, self.len());
        return BitSlice::new(self.bitvec, self.start, range.end + 1);
    }
}

impl<'a> SliceMut<Range<usize>> for BitSliceMut<'a> {
    fn slice_mut(&mut self, range: Range<usize>) -> BitSliceMut {
        check_bounds(range.start, range.end, self.len());
        return BitSliceMut::new(
            self.bitvec,
            self.start + range.start,
            range.end - range.start,
        );
    }
}

impl<'a> SliceMut<RangeFrom<usize>> for BitSliceMut<'a> {
    fn slice_mut(&mut self, range: RangeFrom<usize>) -> BitSliceMut {
        check_bounds(range.start, self.len(), self.len());
        let start = self.start + range.start;
        return BitSliceMut::new(self.bitvec, start, self.len() - range.start);
    }
}

impl<'a> SliceMut<RangeTo<usize>> for BitSliceMut<'a> {
    fn slice_mut(&mut self, range: RangeTo<usize>) -> BitSliceMut {
        check_bounds(0, range.end, self.len());
        return BitSliceMut::new(self.bitvec, self.start, range.end);
    }
}

impl<'a> SliceMut<RangeFull> for BitSliceMut<'a> {
    fn slice_mut(&mut self, _: RangeFull) -> BitSliceMut {
        return BitSliceMut::new(self.bitvec, self.start, self.len);
    }
}

impl<'a> SliceMut<RangeInclusive<usize>> for BitSliceMut<'a> {
    fn slice_mut(&mut self, range: RangeInclusive<usize>) -> BitSliceMut {
        check_bounds(*range.start(), *range.end() + 1, self.len());
        return BitSliceMut::new(
            self.bitvec,
            self.start + *range.start(),
            *range.end() - *range.start() + 1,
        );
    }
}

impl<'a> SliceMut<RangeToInclusive<usize>> for BitSliceMut<'a> {
    fn slice_mut(&mut self, range: RangeToInclusive<usize>) -> BitSliceMut {
        check_bounds(0, range.end + 1, self.len());
        return BitSliceMut::new(self.bitvec, self.start, range.end + 1);
    }
}

impl<'a> BitSliceMut<'a> {
    pub fn new(bitvec: &'a mut BitVector, start: usize, len: usize) -> BitSliceMut {
        return BitSliceMut { bitvec, start, len };
    }

    pub fn set(&mut self, index: usize, bit: bool) {
        if index >= self.len {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len, index
            );
        }
        self.bitvec.set(self.start + index, bit);
    }

    pub fn read_u8(&self, start: usize, max: Numbits) -> (u8, Numbits) {
        self.bitvec.read_u8(self.start + start, max)
    }

    pub fn read_u16(&self, start: usize, max: Numbits) -> (u16, Numbits) {
        self.bitvec.read_u16(self.start + start, max)
    }

    pub fn read_u32(&self, start: usize, max: Numbits) -> (u32, Numbits) {
        self.bitvec.read_u32(self.start + start, max)
    }

    pub fn read_u64(&self, start: usize, max: Numbits) -> (u64, Numbits) {
        self.bitvec.read_u64(self.start + start, max)
    }

    pub fn read_u128(&self, start: usize, max: Numbits) -> (u128, Numbits) {
        self.bitvec.read_u128(self.start + start, max)
    }

    pub fn as_u8(&self) -> (u8, Numbits) {
        self.bitvec.read_u8(self.start, self.len)
    }

    pub fn as_u16(&self) -> (u16, Numbits) {
        self.bitvec.read_u16(self.start, self.len)
    }

    pub fn as_u32(&self) -> (u32, Numbits) {
        self.bitvec.read_u32(self.start, self.len)
    }

    pub fn as_u64(&self) -> (u64, Numbits) {
        self.bitvec.read_u64(self.start, self.len)
    }

    pub fn as_u128(&self) -> (u128, Numbits) {
        self.bitvec.read_u128(self.start, self.len)
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl<'a> BitSlice<'a> {
    pub fn new(bitvec: &'a BitVector, start: usize, len: usize) -> BitSlice {
        return BitSlice { bitvec, start, len };
    }

    pub fn bit_at(&self, index: usize) -> Option<bool> {
        self.bitvec.get(index)
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn as_u8(&self) -> (u8, Numbits) {
        self.bitvec.read_u8(self.start, self.len)
    }

    pub fn as_u16(&self) -> (u16, Numbits) {
        self.bitvec.read_u16(self.start, self.len)
    }

    pub fn as_u32(&self) -> (u32, Numbits) {
        self.bitvec.read_u32(self.start, self.len)
    }

    pub fn as_u64(&self) -> (u64, Numbits) {
        self.bitvec.read_u64(self.start, self.len)
    }

    pub fn as_u128(&self) -> (u128, Numbits) {
        self.bitvec.read_u128(self.start, self.len)
    }
}

impl<'a> Index<usize> for BitSlice<'a> {
    type Output = bool;
    fn index(&self, index: usize) -> &Self::Output {
        if index >= self.len {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len, index
            );
        }

        match self.bit_at(self.start + index) {
            None => panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len, index
            ),
            Some(true) => &true,
            Some(false) => &false,
        }
    }
}

#[cfg(test)]
impl<'a> BitSlice<'a> {
    pub fn start(&self) -> usize {
        self.start
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bitvec::Slice;

    #[test]
    fn test_slice_range() {
        let mut bv = BitVector::new(20);
        bv.push_u8(0b1010_1100);
        let s = bv.slice(1..6); //[01011]
        assert_eq!(s.start(), 1);
        assert_eq!(s.len(), 5);
        assert_eq!(s.as_u8(), (11, 5));

        //now lets subslice s
        let ss = s.slice(1..4); //[101]
        assert_eq!(ss.start(), 2);
        assert_eq!(ss.len(), 3);
        assert_eq!(ss.as_u8(), (5, 3));

        let s = bv.slice(1..8); //[010_1100]
        assert_eq!(s.start(), 1);
        assert_eq!(s.len(), 7);
        assert_eq!(s.as_u8(), (44, 7));

        let ss = s.slice(1..7); //[10_1100]
        assert_eq!(ss.start(), 2);
        assert_eq!(ss.len(), 6);
        assert_eq!(ss.as_u8(), (44, 6));
    }

    #[test]
    fn test_slice_range_full() {
        let mut bv = BitVector::new(20);
        bv.push_u8(0b1010_1100);
        let s = bv.slice(1..6); //[01011]
        let ss = s.slice(..); //[01011]
        assert_eq!(ss.start(), 1);
        assert_eq!(ss.len(), 5);
        assert_eq!(ss.as_u8(), (11, 5));
    }

    #[test]
    fn test_slice_range_from() {
        let mut bv = BitVector::new(20);
        bv.push_u8(0b1010_1100);
        let s = bv.slice(1..6); //[01011]
        let ss = s.slice(2..); //[011]
        assert_eq!(ss.start(), 3);
        assert_eq!(ss.len(), 3);
        assert_eq!(ss.as_u8(), (3, 3));
    }

    #[test]
    fn test_slice_range_to() {
        let mut bv = BitVector::new(20);
        bv.push_u8(0b1010_1100);
        let s = bv.slice(1..6); //[01011]
        let ss = s.slice(..4); //[0101]
        assert_eq!(ss.start(), 1);
        assert_eq!(ss.len(), 4);
        assert_eq!(ss.as_u8(), (5, 4));
    }

    #[test]
    fn test_slice_range_inclusive() {
        let mut bv = BitVector::new(20);
        bv.push_u8(0b1010_1100);
        let s = bv.slice(1..6); //[01011]
        let ss = s.slice(1..=4); //[1011]
        assert_eq!(ss.start(), 2);
        assert_eq!(ss.len(), 4);
        assert_eq!(ss.as_u8(), (11, 4));
    }

    #[test]
    fn test_slice_range_to_inclusive() {
        let mut bv = BitVector::new(20);
        bv.push_u8(0b1010_1100);
        let s = bv.slice(1..6); //[01011]
        let ss = s.slice(..=3); //[0101]
        assert_eq!(ss.start(), 1);
        assert_eq!(ss.len(), 4);
        assert_eq!(ss.as_u8(), (5, 4));
    }
}
