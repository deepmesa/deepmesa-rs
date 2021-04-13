use crate::bitvec::{bitvec::FastBitVector, Numbits};
use std::ops::Index;

#[derive(Debug)]
pub struct FastBitSlice<'a> {
    bitvec: &'a FastBitVector,
    start: usize,
    end: usize,
}

impl<'a> FastBitSlice<'a> {
    pub fn new(bitvec: &'a FastBitVector, start: usize, end: usize) -> FastBitSlice {
        return FastBitSlice { bitvec, start, end };
    }

    pub fn bit_at(&self, index: usize) -> Option<bool> {
        self.bitvec.bit_at(index)
    }

    pub fn len(&self) -> usize {
        self.end - self.start + 1
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

impl<'a> Index<usize> for FastBitSlice<'a> {
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
