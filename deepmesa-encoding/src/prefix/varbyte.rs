use deepmesa_collections::bitvec::bitvec::BitVector;

impl_encoder!(
    /// Encodes unsigned values using variable byte encoding.
    ///
    /// Each value is encoded in 8 byte chunks. The MSB of each byte
    /// is used to indicate whether there are more bytes to read for
    /// this element. The MSB is set to 0 if there is are additional
    /// bytes in the element and is set to 1 to indicate that this is
    /// the last byte in the element.
    ///
    /// # Examples:
    /// ```text
    /// decimal 255 = 1111_1111
    /// encoding for decimal 255 = 0000_0001_0111_1111;
    ///
    /// decimal 2 = 0000_0010
    /// encoding for decimal 2 = 1000_0010;
    /// ```
    ///
    /// The variable byte encoder, encodes the data in a
    /// [`BitVector`]. The [`.encode()`](#method.encode) accepts a
    /// [`u128`] value and pushes encoded bits to the [`BitVector`].
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
    /// use deepmesa::encoding::VarByteEncoder;
    ///
    /// let mut vbe = VarByteEncoder::new();
    ///
    /// // encode 255
    /// vbe.encode(255);
    /// assert_eq!(vbe.elements(), 1);
    /// assert_eq!(vbe.encoded_len(), 16);
    /// assert_eq!(vbe.comp_ratio(), 16.0);
    ///
    /// // Get the underlying BitVector.
    /// let encoded = vbe.encoded();
    /// assert_eq!(encoded.read_u16(0), (0b0000_0001_1111_1111, 16));
    ///
    /// // encode 2
    /// vbe.encode(2);
    /// assert_eq!(vbe.elements(), 2);
    /// assert_eq!(vbe.encoded_len(), 24);
    /// assert_eq!(vbe.comp_ratio(), 12.0);
    ///
    /// let encoded = vbe.encoded();
    /// assert_eq!(encoded.read_u8(16), (0b1000_0010, 8));
    /// ```
    ///
    /// Encoded bits can be decoded using the [`VarByteDecoder`].
    VarByteEncoder,
    varbyte_encode
);

impl_decoder!(
    /// Decodes encoded bits using Variable Byte Encoding.
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
    /// use deepmesa::encoding::VarByteEncoder;
    /// use deepmesa::encoding::VarByteDecoder;
    ///
    /// let mut vbe = VarByteEncoder::new();
    /// vbe.encode(255);
    /// vbe.encode(2);
    ///
    /// // Decoder needs to be mutable to use the decode method
    ///
    /// let mut dec = VarByteDecoder::new(vbe.encoded());
    /// assert_eq!(dec.decode(), Some(255));
    /// assert_eq!(dec.decode(), Some(2));
    /// assert_eq!(dec.decode(), None);
    ///
    /// // use the iterator if you don't want to use a mutable
    /// // decoder
    /// let dec = VarByteDecoder::new(vbe.encoded());
    /// let mut iter = dec.iter();
    ///
    /// assert_eq!(iter.next(), Some(255));
    /// assert_eq!(iter.next(), Some(2));
    /// assert_eq!(iter.next(), None);
    ///
    /// // Or use the decoder as an iterator
    /// let mut dec = VarByteDecoder::new(vbe.encoded());
    /// for val in dec {
    ///     println!("Value: {}", val);
    /// }
    /// ```
    VarByteDecoder,
    varbyte_decode,
    VarByteDecodingIterator
);

decoding_iter!(VarByteDecodingIterator, varbyte_decode);
pub(super) fn varbyte_encode(bitvec: &mut BitVector, val: u128) {
    let mut val = val;
    let mut enc_vec: Vec<u8> = Vec::with_capacity(16);
    loop {
        let byte: u8 = (val % 128) as u8;
        enc_vec.push(byte);
        if val < 128 {
            break;
        }
        val = val / 128;
    }

    //add 128 to the first element of the vector. This sets the
    // continuation bit to 1 to indicate that this is the last
    // byte
    enc_vec[0] += 128;
    //now reverse the encoded vector and push it into the bitvector
    for i in (0..enc_vec.len()).rev() {
        bitvec.push_u8(enc_vec[i], Some(8));
    }
}

pub(super) fn varbyte_decode(bitvec: &BitVector, index: usize) -> Option<(u128, usize)> {
    if index >= bitvec.len() {
        return None;
    }
    let mut val: u128 = 0;
    let mut cursor = index;
    loop {
        let (byte, read) = bitvec.read_u8(cursor);
        debug_assert!(read == 8, "Failed to find valid byte at cursor {:?}", index);

        cursor += 8;
        if byte < 128 {
            val = val * 128 + byte as u128;
        } else {
            val = (val * 128) + (byte - 128) as u128;
            break;
        }
    }

    return Some((val, cursor - index));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_824() {
        let mut vbe = VarByteEncoder::new();
        vbe.encode(824);

        let enc = vbe.encoded();
        //decimal 824 = 0000_0011_0011_1000
        //encoding for decimal 824 = 0000_0110_1011_1000
        assert_eq!(enc.len(), 16);
        assert_eq!(vbe.elements(), 1);
        assert_eq!(enc.read_u16(0), (0b0000_0110_1011_1000, 16));
        let comp_ratio = enc.len() as f64 / vbe.elements() as f64;
        assert_eq!(comp_ratio, 16.0);
    }

    #[test]
    fn test_encode_255() {
        let mut vbe = VarByteEncoder::new();
        vbe.encode(255);

        let enc = vbe.encoded();
        //decimal 255 = 1111_1111
        //encoding for decimal 255 = 0000_0001_1111_1111
        assert_eq!(enc.len(), 16);
        assert_eq!(vbe.elements(), 1);
        assert_eq!(enc.read_u16(0), (0b0000_0001_1111_1111, 16));
        let comp_ratio = enc.len() as f64 / vbe.elements() as f64;
        assert_eq!(comp_ratio, 16.0);
    }

    #[test]
    fn test_encode_many() {
        let mut vbe = VarByteEncoder::new();
        for x in 0..10000 {
            vbe.encode(x);
        }
        assert_eq!(vbe.elements(), 10000);
        let comp_ratio = vbe.encoded_len() as f64 / vbe.elements() as f64;
        assert_eq!(comp_ratio, 15.8976);
    }

    #[test]
    fn test_decode_824() {
        let mut vbe = VarByteEncoder::new();
        vbe.encode(824);

        let mut dec = VarByteDecoder::new(&vbe.encoded());
        let val = dec.decode();
        match val {
            None => panic!("Got None! Expected a value"),
            Some(x) => {
                assert_eq!(x, 824);
            }
        }
    }

    #[test]
    fn test_decode_65535() {
        let mut vbe = VarByteEncoder::new();
        vbe.encode(65535);

        let enc = vbe.encoded();

        let mut dec = VarByteDecoder::new(&enc);
        let decoded_val = dec.decode().unwrap();
        assert_eq!(decoded_val, 65535);
    }

    #[test]
    fn test_decode_big() {
        let val = 0b1101_0011_1111_1111;
        let mut vbe = VarByteEncoder::new();
        vbe.encode(val);
        let enc = vbe.encoded();
        assert_eq!(enc.read_u8(0), (0b0000_0011, 8));
        assert_eq!(enc.read_u8(8), (0b0010_0111, 8));
        assert_eq!(enc.read_u8(16), (0b1111_1111, 8));
        let mut dec = VarByteDecoder::new(&vbe.encoded());
        let decoded_val = dec.decode().unwrap();
        assert_eq!(val as u128, decoded_val);
    }

    #[test]
    fn test_encode_u128_max() {
        let val = u128::MAX;
        let mut vbe = VarByteEncoder::new();
        vbe.encode(val);

        let mut dec = VarByteDecoder::new(&vbe.encoded());
        let decoded_val = dec.decode().unwrap();
        assert_eq!(val, decoded_val);
    }
}
