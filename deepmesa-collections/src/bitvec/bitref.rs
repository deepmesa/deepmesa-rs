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

use crate::bitvec::{bitops, traits::BitwiseClearAssign};

use core::marker;
use core::ops::Deref;
use core::ops::DerefMut;

#[derive(Debug, PartialEq)]
pub struct BitRef<'a, T> {
    bit: bool,
    _marker: marker::PhantomData<&'a T>,
}

#[derive(Debug, PartialEq)]
pub struct BitRefMut<'a, T> {
    bit: bool,
    mut_bit: bool,
    byte_ptr: *mut u8,
    _marker: marker::PhantomData<&'a T>,
    bit_index: usize,
}

impl<'a, T> BitRef<'a, T> {
    pub(super) fn new(bit: bool) -> BitRef<'a, T> {
        BitRef {
            bit,
            _marker: marker::PhantomData,
        }
    }
}

impl<'a, T> BitRefMut<'a, T> {
    pub(super) fn new(bit: bool, byte_ptr: *mut u8, bit_index: usize) -> BitRefMut<'a, T> {
        BitRefMut {
            bit,
            mut_bit: bit,
            byte_ptr: byte_ptr,
            _marker: marker::PhantomData,
            bit_index: bit_index,
        }
    }
}

impl<'a, T> Drop for BitRefMut<'a, T> {
    fn drop(&mut self) {
        if self.bit != self.mut_bit {
            if self.byte_ptr == core::ptr::null_mut() {
                panic!("Cannot assign to immutable BitRefMut");
            }

            if self.mut_bit {
                unsafe {
                    bitops::set_msb_n(&mut *self.byte_ptr, (self.bit_index % 8) as u8);
                }
            } else {
                unsafe {
                    (*self.byte_ptr).clear_msb_nth_assign((self.bit_index % 8) as u8);
                }
            }
        }
    }
}

impl<'a, T> Deref for BitRef<'a, T> {
    type Target = bool;
    fn deref(&self) -> &Self::Target {
        &self.bit
    }
}

impl<'a, T> Deref for BitRefMut<'a, T> {
    type Target = bool;
    fn deref(&self) -> &Self::Target {
        &self.mut_bit
    }
}

impl<'a, T> DerefMut for BitRefMut<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.mut_bit
    }
}
