use deepmesa_collections::bitvec::bitvec::BitVector;
use deepmesa_collections::bitvec::BitOrder;

use crate::prefix::delta;
use crate::prefix::gamma;

impl_encoder!(
    /// Encodes unsigned values using Delta Encoding.
    ///
    /// Each value is encoded in two parts - a length and an
    /// offset. The length is encoded in Gamma and the offset is the
    /// binary representation with the leading `1` removed.
    ///
    /// # Examples
    /// ```text
    /// decimal 2 = 0000_0010
    /// encoding for decimal 2 = 100_0
    ///
    /// decimal 13 = 0000_1101
    /// encoding for decimal 13 = 10_1_101
    /// ```
    ///
    /// The delta encoder, encodes the data in a [`BitVector`]. The
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
    /// use deepmesa::encoding::DeltaEncoder;
    ///
    /// let mut de = DeltaEncoder::new();
    ///
    /// // encode 2
    /// de.encode(2);
    /// assert_eq!(de.elements(), 1);
    /// assert_eq!(de.encoded_len(), 2);
    /// assert_eq!(de.comp_ratio(), 2.0);
    ///
    /// // Get the underlying BitVector.
    /// let encoded = de.encoded();
    /// assert_eq!(encoded.read_u8(0), (0b00, 2));
    ///
    /// // encode 13
    /// de.encode(13);
    /// assert_eq!(de.elements(), 2);
    /// assert_eq!(de.encoded_len(), 8);
    /// assert_eq!(de.comp_ratio(), 4.0);
    ///
    /// let encoded = de.encoded();
    /// assert_eq!(encoded.read_u16(2), (0b101_101, 6));
    /// ```
    ///
    /// Encoded bits can be decoded using the [`DeltaDecoder`].
    DeltaEncoder,
    encode
);

impl_decoder!(
    /// Decodes encoded bits using Delta Encoding.
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
    /// use deepmesa::encoding::DeltaEncoder;
    /// use deepmesa::encoding::DeltaDecoder;
    ///
    /// let mut de = DeltaEncoder::new();
    /// de.encode(2);
    /// de.encode(13);
    ///
    /// // Decoder needs to be mutable to use the decode method
    ///
    /// let mut dec = DeltaDecoder::new(de.encoded());
    /// assert_eq!(dec.decode(), Some(2));
    /// assert_eq!(dec.decode(), Some(13));
    /// assert_eq!(dec.decode(), None);
    ///
    /// // use the iterator if you don't want to use a mutable
    /// // decoder
    /// let dec = DeltaDecoder::new(de.encoded());
    /// let mut iter = dec.iter();
    ///
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(13));
    /// assert_eq!(iter.next(), None);
    ///
    /// // Or use the decoder as an iterator
    /// let mut dec = DeltaDecoder::new(de.encoded());
    /// for val in dec {
    ///     println!("Value: {}", val);
    /// }
    /// ```
    DeltaDecoder,
    decode,
    DeltaDecodingIterator
);

decoding_iter!(DeltaDecodingIterator, delta::decode);

pub(super) fn encode(bitvec: &mut BitVector, val: u128) {
    //Chop off the MSB 1 bit and count the remaining bits to get the offset len
    let lz: usize = val.leading_zeros() as usize;
    let offset_len = crate::prefix::U128_BITS - (lz + 1);
    //encode the offset in gamma code by that amount
    gamma::encode(bitvec, offset_len as u128);
    //Append the delta offset to the bitvec
    bitvec.push_bits_u128(val, offset_len, BitOrder::Lsb0);
}

pub(super) fn decode(bitvec: &BitVector, index: usize) -> Option<(u128, usize)> {
    //first decode the gamma prefix
    match gamma::decode(bitvec, index) {
        None => return None,
        Some((offset_len, gamma_bits)) => {
            if offset_len == 0 {
                return Some((1, gamma_bits));
            }

            let cursor = index + gamma_bits;
            let (val, read_bits) = bitvec.read_bits_u128(cursor, offset_len as usize);
            debug_assert!(
                read_bits as u128 == offset_len,
                "failed to read {} bits. Only read {} bits",
                offset_len,
                read_bits
            );

            // set the bit after the msb to 1 and return it
            return Some((val | (1 as u128) << offset_len, gamma_bits + read_bits));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_decode() {
        let mut de = DeltaEncoder::new();
        de.encode(13); //Delta code: 10,1,101
        let enc = de.encoded(); //

        assert_eq!(enc.len(), 6);
        assert_eq!(enc[0..6].as_u8(), (0b10_1_101, 6));
        assert_eq!(de.elements(), 1);

        de.encode(24); // Delta Code: 110,00,1000
        let enc = de.encoded();
        assert_eq!(enc.len(), 15);
        assert_eq!(enc[6..].as_u16(), (0b110_00_1000, 9));
        assert_eq!(de.elements(), 2);

        de.encode(511); // Delta Code: 1110,000,1111_1111
        let enc = de.encoded();
        assert_eq!(enc.len(), 30);
        assert_eq!(enc[15..].as_u16(), (0b1110_000_1111_1111, 15));
        assert_eq!(de.elements(), 3);

        //now create a decoder
        let mut dec = DeltaDecoder::new(&de.encoded());
        // call decode to decode the first value (13)
        let val = dec.decode();
        assert_eq!(val, Some(13));
        assert_eq!(dec.cursor, 6);
        //now call decode again to decode the next value (24)
        let val = dec.decode();
        assert_eq!(
            val,
            Some(24),
            "val={:08b}, expected: {:08b}",
            val.unwrap(),
            24
        );
        assert_eq!(dec.cursor, 15);

        //now call decode again to decode the next value (511)
        let val = dec.decode();
        assert_eq!(val, Some(511));
        assert_eq!(dec.cursor, 30);
    }

    #[test]
    fn test_encode_decode_2() {
        let mut de = DeltaEncoder::new();
        de.encode(2);
        let mut dec = DeltaDecoder::new(&de.encoded());
        // call decode to decode the first value (13)
        let val = dec.decode();
        assert_eq!(val, Some(2));
    }
}
