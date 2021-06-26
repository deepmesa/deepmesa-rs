use crate::prefix::unary;
use deepmesa_collections::bitvec::bitvec::BitVector;

impl_encoder!(
    /// Encodes unsigned values using Unary Encoding.
    ///
    /// Each value is encoded as a sequence of `1` bits followed by a
    /// `0` bit.
    ///
    /// # Examples
    /// ```text
    /// decimal 2 = 0000_0010
    /// encoding for decimal 2 = 110
    ///
    /// decimal 12 = 0000_0101
    /// encoding for decimal 12 = 1111_1111_1111_0
    /// ```
    ///
    /// The unary encoder, encodes the data in a [`BitVector`]. The
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
    /// use deepmesa::encoding::UnaryEncoder;
    ///
    /// let mut vbe = UnaryEncoder::new();
    ///
    /// // encode 2
    /// vbe.encode(2);
    /// assert_eq!(vbe.elements(), 1);
    /// assert_eq!(vbe.encoded_len(), 3);
    /// assert_eq!(vbe.comp_ratio(), 3.0);
    ///
    /// // Get the underlying BitVector.
    /// let encoded = vbe.encoded();
    /// assert_eq!(encoded.read_u8(0), (0b110, 3));
    ///
    /// // encode 12
    /// vbe.encode(12);
    /// assert_eq!(vbe.elements(), 2);
    /// assert_eq!(vbe.encoded_len(), 16);
    /// assert_eq!(vbe.comp_ratio(), 8.0);
    ///
    /// let encoded = vbe.encoded();
    /// assert_eq!(encoded.read_u16(3), (0b1111_1111_1111_0, 13));
    /// ```
    ///
    /// Encoded bits can be decoded using the [`UnaryDecoder`].
    UnaryEncoder,
    encode
);

impl_decoder!(
    /// Decodes encoded bits using Unary Encoding.
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
    /// use deepmesa::encoding::UnaryEncoder;
    /// use deepmesa::encoding::UnaryDecoder;
    ///
    /// let mut ue = UnaryEncoder::new();
    /// ue.encode(2);
    /// ue.encode(12);
    ///
    /// // Decoder needs to be mutable to use the decode method
    ///
    /// let mut dec = UnaryDecoder::new(ue.encoded());
    /// assert_eq!(dec.decode(), Some(2));
    /// assert_eq!(dec.decode(), Some(12));
    /// assert_eq!(dec.decode(), None);
    ///
    /// // use the iterator if you don't want to use a mutable
    /// // decoder
    /// let dec = UnaryDecoder::new(ue.encoded());
    /// let mut iter = dec.iter();
    ///
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), Some(12));
    /// assert_eq!(iter.next(), None);
    ///
    /// // Or use the decoder as an iterator
    /// let mut dec = UnaryDecoder::new(ue.encoded());
    /// for val in dec {
    ///     println!("Value: {}", val);
    /// }
    /// ```
    UnaryDecoder,
    decode,
    UnaryDecodingIterator
);

decoding_iter!(UnaryDecodingIterator, unary::decode);

pub(super) fn encode(bitvec: &mut BitVector, val: u128) {
    // The unary encoder can only encode upto a usize:: MAX value
    if val > usize::MAX as u128 {
        panic!("Cannot unary encode val {} that exceeds usize::MAX", val);
    }
    bitvec.fill(true, val as usize);
    //push the terminating continuation bit
    bitvec.fill(false, 1);
}

pub(super) fn decode(bitvec: &BitVector, index: usize) -> Option<(u128, usize)> {
    if index >= bitvec.len() {
        return None;
    }

    let count = bitvec.leading_ones(index);
    return Some((count as u128, count + 1));
}

#[cfg(test)]
mod tests {
    use super::*;

    // encoded = 1010_1010_1010_1010
    #[test]
    fn test_encode_1() {
        //encode 1, 8 times
        let mut ue = UnaryEncoder::new();
        for i in 0..8 {
            ue.encode(1);
            assert_eq!(ue.elements(), i + 1);
        }

        let enc = ue.encoded();
        assert_eq!(enc.len(), 16);
        assert_eq!(enc.read_u16(0), (0b1010_1010_1010_1010, 16));
        assert_eq!(ue.elements(), 8);
        //now create a decoder and start the decoding
        let mut dec = UnaryDecoder::new(&ue.encoded());
        assert_eq!(dec.cursor, 0);
        for i in 0..8 {
            let val = dec.decode();
            assert_eq!(val, Some(1));
            assert_eq!(
                dec.cursor,
                (i + 1) * 2,
                "At i={}, cursor = {}",
                i,
                dec.cursor
            );
        }
    }

    #[test]
    fn test_encode_decode() {
        let mut ue = UnaryEncoder::new();
        ue.encode(1); //10
        let enc = ue.encoded();
        assert_eq!(enc.len(), 2);
        assert_eq!(enc[0..2].as_u8(), (0b10, 2));
        assert_eq!(ue.elements(), 1);

        //now encode a larger number thats not a multiple of 8
        ue.encode(17);
        let enc = ue.encoded();
        assert_eq!(enc.len(), 20);
        assert_eq!(enc[2..].leading_ones(), 17);
        assert_eq!(enc[2..].trailing_zeros(), 1);
        assert_eq!(ue.elements(), 2);

        //now create a decoder
        let mut dec = UnaryDecoder::new(&ue.encoded());
        // call decode to decode the first value
        let val = dec.decode();
        assert_eq!(val, Some(1));
        assert_eq!(dec.cursor, 2);
        //now call decode again to decode the next value (17)
        let val = dec.decode();
        assert_eq!(val, Some(17));
        assert_eq!(dec.cursor, 20);
    }
}
