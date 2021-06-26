use deepmesa_collections::bitvec::bitvec::BitVector;
use deepmesa_collections::bitvec::BitOrder;

use crate::prefix::gamma;
use crate::prefix::unary;

impl_encoder!(
    /// Encodes unsigned values using Gamma Encoding.
    ///
    /// Each value is encoded in two parts - a length and an
    /// offset. The length is encoded in unary and the offset is the
    /// binary representation with the leading `1` removed.
    ///
    /// # Examples
    /// ```text
    /// decimal 2 = 0000_0010
    /// encoding for decimal 2 = 10_0
    ///
    /// decimal 13 = 0000_1101
    /// encoding for decimal 13 = 1110_101
    /// ```
    ///
    /// The gamma encoder, encodes the data in a [`BitVector`]. The
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
    /// use deepmesa::encoding::GammaEncoder;
    ///
    /// let mut ge = GammaEncoder::new();
    ///
    /// // encode 2
    /// ge.encode(2);
    /// assert_eq!(ge.elements(), 1);
    /// assert_eq!(ge.encoded_len(), 3);
    /// assert_eq!(ge.comp_ratio(), 3.0);
    ///
    /// // Get the underlying BitVector.
    /// let encoded = ge.encoded();
    /// assert_eq!(encoded.read_u8(0), (0b100, 3));
    ///
    /// // encode 13
    /// ge.encode(13);
    /// assert_eq!(ge.elements(), 2);
    /// assert_eq!(ge.encoded_len(), 10);
    /// assert_eq!(ge.comp_ratio(), 5.0);
    ///
    /// let encoded = ge.encoded();
    /// assert_eq!(encoded.read_u16(3), (0b1110_101, 7));
    /// ```
    ///
    /// Encoded bits can be decoded using the [`GammaDecoder`].
    GammaEncoder,
    encode
);

impl_decoder!(
    /// Decodes encoded bits using Gamma Encoding.
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
    /// use deepmesa::encoding::GammaEncoder;
    /// use deepmesa::encoding::GammaDecoder;
    ///
    /// let mut ge = GammaEncoder::new();
    /// ge.encode(2);
    /// ge.encode(13);
    ///
    /// // Decoder needs to be mutable to use the decode method
    ///
    /// let mut dec = GammaDecoder::new(ge.encoded());
    /// assert_eq!(dec.decode(), Some(2));
    /// assert_eq!(dec.decode(), Some(13));
    /// assert_eq!(dec.decode(), None);
    ///
    /// // use the iterator if you don't want to use a mutable
    /// // decoder
    /// let dec = GammaDecoder::new(ge.encoded());
    /// let mut iter = dec.iter();
    ///
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(13));
    /// assert_eq!(iter.next(), None);
    ///
    /// // Or use the decoder as an iterator
    /// let mut dec = GammaDecoder::new(ge.encoded());
    /// for val in dec {
    ///     println!("Value: {}", val);
    /// }
    /// ```
    GammaDecoder,
    decode,
    GammaDecodingIterator
);

decoding_iter!(GammaDecodingIterator, gamma::decode);

pub(super) fn encode(bitvec: &mut BitVector, val: u128) {
    let lz: usize = val.leading_zeros() as usize;
    let offset_len = crate::prefix::U128_BITS - (lz + 1);
    //encode the unary by that amount
    unary::encode(bitvec, offset_len as u128);
    //Append the gamma offset to the bitvec
    bitvec.push_bits_u128(val, offset_len, BitOrder::Lsb0);
}

pub(super) fn decode(bitvec: &BitVector, index: usize) -> Option<(u128, usize)> {
    match unary::decode(bitvec, index) {
        None => return None,
        Some((offset_len, unary_bits)) => {
            if offset_len == 0 {
                return Some((1, unary_bits));
            }
            let cursor = index + unary_bits;
            let (val, read_bits) = bitvec.read_bits_u128(cursor, offset_len as usize);
            debug_assert!(
                read_bits as u128 == offset_len,
                "failed to read {} bits. Only read {} bits",
                offset_len,
                read_bits
            );

            // set the bit after the msb to 1 and return it
            return Some((val | (1 as u128) << offset_len, unary_bits + read_bits));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_4() {
        let mut ge = GammaEncoder::new();
        ge.encode(4); //110,00
        let enc = ge.encoded();
        assert_eq!(enc.len(), 5);
        assert_eq!(enc[0..5].as_u8(), (0b110_00, 5));
        assert_eq!(ge.elements(), 1);

        let mut dec = GammaDecoder::new(&ge.encoded());
        // call decode to decode the first value (13)
        let val = dec.decode();
        assert_eq!(val, Some(4));
    }

    #[test]
    fn test_encode_decode() {
        let mut ge = GammaEncoder::new();
        ge.encode(13); // 1110101
        let enc = ge.encoded();
        assert_eq!(enc.len(), 7);
        assert_eq!(enc[0..7].as_u8(), (0b1110_101, 7));
        assert_eq!(ge.elements(), 1);

        ge.encode(24); // 1_1110_1000
        let enc = ge.encoded();
        assert_eq!(enc.len(), 16);
        assert_eq!(enc[7..].as_u16(), (0b1_1110_1000, 9));
        assert_eq!(ge.elements(), 2);

        ge.encode(511); // 1111_1111_0,111_1111_1
        let enc = ge.encoded();
        assert_eq!(enc.len(), 33);
        assert_eq!(enc[16..].as_u32(), (0b1111_1111_0111_1111_1, 17));
        assert_eq!(ge.elements(), 3);

        //now create a decoder
        let mut dec = GammaDecoder::new(&ge.encoded());
        // call decode to decode the first value (13)
        let val = dec.decode();
        assert_eq!(val, Some(13));
        assert_eq!(dec.cursor, 7);
        //now call decode again to decode the next value (24)
        let val = dec.decode();
        assert_eq!(val, Some(24));
        assert_eq!(dec.cursor, 16);

        //now call decode again to decode the next value (511)
        let val = dec.decode();
        assert_eq!(val, Some(511));
        assert_eq!(dec.cursor, 33);
    }
}
