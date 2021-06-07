use crate::prefix::{
    decoder::{PrefixDecoder, VarByteDecoder},
    encoder::{PrefixEncoder, VarByteEncoder},
};

impl<'a> VarByteDecoder for PrefixDecoder<'a> {
    fn decode_varbyte(&mut self) -> Option<u128> {
        if self.cursor >= self.bitvec.len() * 8 {
            return None;
        }
        let mut dec: u128 = 0;
        let mut done = false;
        loop {
            let (byte, read) = self.bitvec.read_u8(self.cursor);
            if read != 8 {
                panic!("Failed to find valid byte at cursor {:?}", self.cursor);
            }

            // let byte: u8 = unwrap!(
            //     self.bitvec.byte_at(self.cursor),
            //     "Failed to find valid byte at cursor {:?}",
            //     self.cursor
            // );
            if byte < 128 {
                dec = dec * 128 + byte as u128;
            } else {
                dec = (dec * 128) + (byte - 128) as u128;
                done = true;
            }
            self.cursor += 8;
            if done {
                break;
            }
        }

        return Some(dec);
    }
}

impl VarByteEncoder for PrefixEncoder {
    /// Encodes the supplied bytes in varByte encoding. The MSB of each
    /// byte is used to indicate whether there are more bytes to read
    /// in this element. The MSB is set to 0 if there is are
    /// additional bytes in the element and is set to 1 to indicate
    /// that this is the last byte in the element.
    ///
    /// #Example:
    ///
    /// decimal 255 = 1111_1111
    /// encoding for decimal 255 = 1000_0001_0111_1111;
    ///
    /// decimal 2 = 0000_0010
    /// encoding for decimal 2 = 0000_0010;
    fn encode_varbyte_u128(&mut self, mut val: u128) {
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
            self.bitvec.push_u8(enc_vec[i], Some(8));
            //self.bitvec.push_byte(enc_vec[i]);
        }
        self.elements += 1;
    }
}

#[cfg(test)]
mod tests {
    use crate::prefix::decoder::Decoder;
    use crate::prefix::decoder::PrefixDecoder;
    use crate::prefix::encoder::Encoder;
    use crate::prefix::encoder::PrefixEncoder;
    use crate::prefix::PrefixEncoding::VarByte;

    #[test]
    fn test_encode_824() {
        let mut vbe = PrefixEncoder::new(VarByte);
        vbe.encode_u128(824);

        let enc = vbe.encoded();
        //decimal 824 = 0000_0011_0011_1000
        //encoding for decimal 824 = 0000_0110_1011_1000
        assert_eq!(enc.len(), 16);
        assert_eq!(vbe.elements(), 1);
        // //assert the high order bits
        assert_eq!(enc.read_u16(0), (0b0000_0110_1011_1000, 16));
        //assert_eq!(enc.byte_at(0).unwrap(), 0b0000_0110);
        // //assert the low order bits
        //        assert_eq!(enc.byte_at(1).unwrap(), 0b1011_1000);
        let comp_ratio = enc.len() as f64 / vbe.elements() as f64;
        assert_eq!(comp_ratio, 16.0);
    }

    #[test]
    fn test_encode_255() {
        let mut vbe = PrefixEncoder::new(VarByte);
        vbe.encode_u128(255);

        let enc = vbe.encoded();
        //decimal 255 = 1111_1111
        //encoding for decimal 255 = 0000_0001_1111_1111
        assert_eq!(enc.len(), 16);
        assert_eq!(vbe.elements(), 1);
        // //assert the high order bits
        assert_eq!(enc.read_u16(0), (0b0000_0001_1111_1111, 16));
        //assert_eq!(enc.byte_at(0).unwrap(), 0b0000_0001);
        // //assert the low order bits
        //assert_eq!(enc.byte_at(1).unwrap(), 0b1111_1111);
        let comp_ratio = enc.len() as f64 / vbe.elements() as f64;
        assert_eq!(comp_ratio, 16.0);
    }

    #[test]
    fn test_encode_many() {
        let mut vbe = PrefixEncoder::new(VarByte);
        for x in 0..10000 {
            vbe.encode_u128(x);
        }
        assert_eq!(vbe.elements(), 10000);
        let comp_ratio = vbe.len_bits() as f64 / vbe.elements() as f64;
        assert_eq!(comp_ratio, 15.8976);
    }

    #[test]
    fn test_decode_824() {
        let mut vbe = PrefixEncoder::new(VarByte);
        vbe.encode_u128(824);
        let enc = vbe.encoded();

        let mut dec = PrefixDecoder::new(&enc, VarByte);
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
        let mut vbe = PrefixEncoder::new(VarByte);
        vbe.encode_u128(65535);

        let enc = vbe.encoded();

        let mut dec = PrefixDecoder::new(&enc, VarByte);
        let decoded_val = dec.decode().unwrap();
        assert_eq!(decoded_val, 65535);
    }

    #[test]
    fn test_decode_big() {
        let val = 0b1101_0011_1111_1111;
        //       1  0101_0011_1111_1111
        //0000_0101 0010_0111 0111_1111
        let mut vbe = PrefixEncoder::new(VarByte);
        vbe.encode_u128(val);
        let enc = vbe.encoded();
        println!("ENC: {:?}", enc);
        assert_eq!(enc.read_u8(0), (0b0000_0011, 8));
        assert_eq!(enc.read_u8(8), (0b0010_0111, 8));
        assert_eq!(enc.read_u8(16), (0b1111_1111, 8));
        // assert_eq!(enc.byte_at(0).unwrap(), 0b0000_0011);
        // assert_eq!(enc.byte_at(1).unwrap(), 0b0010_0111);
        // assert_eq!(enc.byte_at(2).unwrap(), 0b1111_1111);
        let mut dec = PrefixDecoder::new(&enc, VarByte);
        let decoded_val = dec.decode().unwrap();
        assert_eq!(val as u128, decoded_val);
    }

    #[test]
    fn test_encode_u128_max() {
        let val = u128::MAX;
        let mut vbe = PrefixEncoder::new(VarByte);
        vbe.encode_u128(val);

        let mut dec = PrefixDecoder::new(&vbe.encoded(), VarByte);
        let decoded_val = dec.decode().unwrap();
        assert_eq!(val, decoded_val);
    }
}
