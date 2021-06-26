/*
   Golomb Coding: A lossless data compression method using codes
   invented by Solomon W. Golomb in the 1960s.

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

use crate::prefix::golomb;
use crate::prefix::unary;
use deepmesa_collections::bitvec::bitvec::BitVector;
use deepmesa_collections::bitvec::BitOrder;

/// Encodes unsigned values using Golomb Encoding.
///
/// Each value is encoded in two parts using a tunable parameter - a
/// quotient in unary a remainder in truncated binary.
///
/// The golomb encoder, encodes the data in a [`BitVector`]. The
/// [`.encode()`](#method.encode) accepts a [`u128`] value and
/// pushes encoded bits to the [`BitVector`].
///
/// The encoder maintains a count of number of values encoded
/// ([`.elements()`](#method.elements)), the number of bits used
/// to encode those elements
/// ([`.encoded_len()`](#method.encoded_len)) and the compression
/// ratio ([`.comp_ratio()`](#method.comp_ratio)). The compression
/// ratio is the average number of bits per value needed to encode
/// all the values.
///
/// # Examples
/// ```
/// use deepmesa::encoding::GolombEncoder;
///
/// let param = 6;
/// let mut ge = GolombEncoder::new(param);
///
/// // encode 9
/// ge.encode(9);
/// assert_eq!(ge.elements(), 1);
/// assert_eq!(ge.encoded_len(), 5);
/// assert_eq!(ge.comp_ratio(), 5.0);
///
/// // Get the underlying BitVector.
/// let encoded = ge.encoded();
/// assert_eq!(encoded.read_u8(0), (0b10100, 5));
///
/// ```
///
/// Encoded bits can be decoded using the [`GolombDecoder`].
pub struct GolombEncoder {
    pub(super) bitvec: BitVector,
    pub(super) elements: usize,
    pub(super) b: u128,
    pub(super) c: usize,
    pub(super) u: u128,
}

/// Decodes encoded bits using Golomb Encoding.
///
/// The decoder accepts a [`BitVector`] with encoded bits and
/// decodes each value on each invocation of the
/// [`.decode()`](#method.decode) method.
///
/// The decoder returns an iterator, but is an iterator itself as
/// well.
///
/// # Examples
/// ```
/// use deepmesa::encoding::GolombEncoder;
/// use deepmesa::encoding::GolombDecoder;
///
/// let param = 6;
/// let mut ge = GolombEncoder::new(param);
/// ge.encode(9);
/// ge.encode(13);
///
/// // Decoder needs to be mutable to use the decode method
///
/// let mut dec = GolombDecoder::new(ge.encoded(), param);
/// assert_eq!(dec.decode(), Some(9));
/// assert_eq!(dec.decode(), Some(13));
/// assert_eq!(dec.decode(), None);
///
/// // use the iterator if you don't want to use a mutable
/// // decoder
/// let dec = GolombDecoder::new(ge.encoded(), param);
/// let mut iter = dec.iter();
///
/// assert_eq!(iter.next(), Some(9));
/// assert_eq!(iter.next(), Some(13));
/// assert_eq!(iter.next(), None);
///
/// // Or use the decoder as an iterator
/// let mut dec = GolombDecoder::new(ge.encoded(), param);
/// for val in dec {
///     println!("Value: {}", val);
/// }
/// ```
pub struct GolombDecoder<'a> {
    pub(super) bitvec: &'a BitVector,
    pub(super) cursor: usize,
    pub(super) b: u128,
    pub(super) c: usize,
    pub(super) u: u128,
}

impl GolombEncoder {
    /// Creates a new [`GolombDecoder`] with a tunable parameter
    pub fn new(param: u128) -> GolombEncoder {
        let c = (param as f64).log2() as usize;
        let u = 2u128.pow((c + 1) as u32) - param;
        GolombEncoder {
            bitvec: BitVector::with_capacity(1024),
            elements: 0,
            b: param,
            c,
            u,
        }
    }

    /// Encodes the specified [`u128`] `val`
    pub fn encode(&mut self, val: u128) {
        let q = (val - 1) / self.b;
        let r = val - (q * self.b) - 1;
        unary::encode(&mut self.bitvec, q);
        if r < self.u {
            //c bits of r
            self.bitvec.push_bits_u128(r, self.c, BitOrder::Lsb0);
        } else {
            self.bitvec
                .push_bits_u128(r + self.u, (self.c + 1) as usize, BitOrder::Lsb0);
        }
        self.elements += 1;
    }

    /// Returns an immutable reference to the underlying
    /// [`BitVector`] containing the encoded bits.
    pub fn encoded(&self) -> &BitVector {
        &self.bitvec
    }

    /// Returns the length in bits of the underlying
    /// [`BitVector`] containing the encoded bits.
    pub fn encoded_len(&self) -> usize {
        self.bitvec.len()
    }

    /// Returns the number of elements encoded in the
    /// underlying [`BitVector`].
    pub fn elements(&self) -> usize {
        self.elements
    }

    /// Returns the compression ratio of the encoded
    /// elements. This is simply the
    /// [`.encoded_len()`](#method.encoded_len()) divided by
    /// the number of [`.elements()`](#method.elements());
    pub fn comp_ratio(&self) -> f64 {
        self.bitvec.len() as f64 / self.elements as f64
    }
}

impl<'a> GolombDecoder<'a> {
    /// Creates a new [`GolombDecoder`] with a tunable parameter and
    /// the specified [`BitVector`] containing the encoded bits.
    pub fn new(bitvec: &'a BitVector, param: u128) -> GolombDecoder {
        let c = (param as f64).log2() as usize;
        let u = 2u128.pow((c + 1) as u32) - param;

        GolombDecoder {
            bitvec: bitvec,
            cursor: 0,
            b: param,
            c,
            u,
        }
    }

    /// Decodes the next available encoded element using an
    /// internal cursor. Returns the decoded value or None if
    /// there are no more elements to decode.
    pub fn decode(&mut self) -> Option<u128> {
        match decode(&self.bitvec, self.cursor, self.b, self.c, self.u) {
            None => None,
            Some((val, bits_read)) => {
                self.cursor += bits_read;
                Some(val)
            }
        }
    }

    /// Decodes upto `max_elements` from the encoded
    /// bits. Returns a vector containing the decoded
    /// elements. If there are no elements to decode then this
    /// method will return an empty [`Vec`].
    pub fn decode_many(&self, max_elements: usize) -> Vec<u128> {
        let mut vec = Vec::<u128>::with_capacity(max_elements);
        let mut ct = 0;

        let mut iter = self.iter();
        loop {
            match iter.next() {
                None => return vec,
                Some(val) => {
                    vec.push(val);
                    ct += 1;
                    if ct >= max_elements {
                        return vec;
                    }
                }
            }
        }
    }

    /// Returns an iterator that iterates over the encoded
    /// elements and decodes them on every invocation.
    pub fn iter(&self) -> GolombDecodingIterator {
        GolombDecodingIterator::<'a>::new(self.bitvec, self.b)
    }
}

pub struct GolombDecodingIterator<'a> {
    pub(super) bitvec: &'a BitVector,
    pub(super) cursor: usize,
    pub(super) b: u128,
    pub(super) c: usize,
    pub(super) u: u128,
}

impl<'a> GolombDecodingIterator<'a> {
    pub(super) fn new(bitvec: &'a BitVector, param: u128) -> GolombDecodingIterator<'a> {
        let c = (param as f64).log2() as usize;
        let u = 2u128.pow((c + 1) as u32) - param;

        GolombDecodingIterator {
            bitvec,
            cursor: 0,
            b: param,
            c,
            u,
        }
    }
}

impl<'a> Iterator for GolombDecoder<'a> {
    type Item = u128;
    fn next(&mut self) -> Option<Self::Item> {
        self.decode()
    }
}

impl<'a> Iterator for GolombDecodingIterator<'a> {
    type Item = u128;
    fn next(&mut self) -> Option<Self::Item> {
        match golomb::decode(self.bitvec, self.cursor, self.b, self.c, self.u) {
            None => None,
            Some((val, bits_read)) => {
                self.cursor += bits_read;
                Some(val)
            }
        }
    }
}

pub(super) fn decode(
    bitvec: &BitVector,
    index: usize,
    b: u128,
    c: usize,
    u: u128,
) -> Option<(u128, usize)> {
    match unary::decode(bitvec, index) {
        None => return None,
        Some((q, unary_bits)) => {
            let cursor = index + unary_bits;
            match bitvec.get(cursor) {
                None => panic!("invalid input. Expected valid bit at index {}", cursor),
                Some(true) => {
                    let (r, read_bits) = bitvec.read_bits_u128(cursor, c + 1);
                    return Some((q * b + r - u + 1, unary_bits + read_bits));
                }
                Some(false) => {
                    let (r, read_bits) = bitvec.read_bits_u128(cursor, c);
                    return Some((q * b + r + 1, unary_bits + read_bits));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_decode() {
        let param = 6;
        let mut ge = GolombEncoder::new(param);
        ge.encode(9);
        ge.encode(13);
        let mut gd = GolombDecoder::new(ge.encoded(), param);
        assert_eq!(gd.decode(), Some(9));
        assert_eq!(gd.decode(), Some(13));
    }
}
