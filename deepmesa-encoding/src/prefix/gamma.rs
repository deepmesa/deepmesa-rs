use std::mem;

use crate::prefix::{
    decoder::{GammaDecoder, PrefixDecoder, UnaryDecoder},
    encoder::{GammaEncoder, PrefixEncoder, UnaryEncoder},
};
use deepmesa_collections::bitvec::BitOrder;

impl<'a> GammaDecoder for PrefixDecoder<'a> {
    fn decode_gamma(&mut self) -> Option<u128> {
        //first decode the unary prefix
        let prefix = self.decode_unary();
        if prefix == None {
            return None;
        }

        let offset_len = prefix.unwrap();

        // //now read that many bits from the bitvector starting at cursor:
        let slice = &self.bitvec[self.cursor..self.cursor + offset_len as usize];
        // .bitvec
        // .get_slice(self.cursor, self.cursor + offset_len as usize);

        // let slice = self
        //     .bitvec
        //     .get_slice(self.cursor, self.cursor + offset_len as usize);

        // let offset = &self.bits[self.cursor..self.cursor + offset_len];
        let (val, read_bits) = slice.as_u128();
        if (read_bits as u128) != offset_len {
            panic!(
                "failed to read {} bits. Only read {} bits",
                offset_len, read_bits
            );
        }

        //now increment the cursor with the number of bits read
        self.cursor += read_bits;
        // set the bit after the msb to 1 and return it
        return Some(val | 2u128.pow(offset_len as u32));
    }
}

impl GammaEncoder for PrefixEncoder {
    fn encode_gamma_u128(&mut self, val: u128) {
        //Chop off the MSB 1 bit and count the remaining bits to get the offset len
        let lz: usize = val.leading_zeros() as usize;
        let offset_len = (mem::size_of::<u128>() * 8) - (lz + 1);
        //encode the unary by that amount
        self.encode_unary_u128(offset_len as u128);
        //Append the gamma offset to the bitvec
        self.bitvec.push_bits_u128(val, offset_len, BitOrder::Lsb0);
    }
}

#[cfg(test)]
mod tests {
    use crate::prefix::decoder::Decoder;
    use crate::prefix::decoder::PrefixDecoder;
    use crate::prefix::encoder::Encoder;
    use crate::prefix::encoder::PrefixEncoder;
    use crate::prefix::PrefixEncoding::Gamma;

    #[test]
    fn test_encode_4() {
        let mut ge = PrefixEncoder::new(Gamma);
        ge.encode_u128(4); //110,00
        let enc = ge.encoded();
        assert_eq!(enc.len(), 5);
        assert_eq!(enc[0..5].as_u8(), (0b110_00, 5));
        //        assert_eq!(enc.byte_at(0).unwrap(), 0b1100_0000);

        let mut dec = PrefixDecoder::new(&enc, Gamma);
        // call decode to decode the first value (13)
        let val = dec.decode();
        assert_eq!(val, Some(4));
    }

    #[test]
    fn test_encode_decode() {
        let mut ge = PrefixEncoder::new(Gamma);
        ge.encode_u128(13); // 1110101
        let enc = ge.encoded();
        assert_eq!(enc.len(), 7);
        assert_eq!(enc[0..7].as_u8(), (0b1110_101, 7));
        //            assert_eq!(enc.byte_at(0).unwrap(), 0b1110_1010);
        //assert_eq!(enc.byte_at(1), None);
        ge.encode_u128(24);
        // {
        //     let enc = ge.encoded();
        //     assert_eq!(enc.len_bits(), 16);
        //     assert_eq!(enc.byte_at(0).unwrap(), 0b1110_1011);
        //     assert_eq!(enc.byte_at(1).unwrap(), 0b1110_1000);
        //     assert_eq!(enc.byte_at(2), None);
        // }
        // ge.encode_u128(511);
        // {
        //     let enc = ge.encoded();
        //     assert_eq!(enc.len_bits(), 33);
        //     assert_eq!(enc.byte_at(0).unwrap(), 0b1110_1011);
        //     assert_eq!(enc.byte_at(1).unwrap(), 0b1110_1000);
        //     assert_eq!(enc.byte_at(2).unwrap(), 0b1111_1111);
        //     assert_eq!(enc.byte_at(3).unwrap(), 0b0111_1111);
        //     assert_eq!(enc.byte_at(4).unwrap(), 0b1000_0000);
        //     assert_eq!(enc.byte_at(5), None);
        // }

        // let enc = ge.encoded();
        // //now create a decoder
        // let mut dec = PrefixDecoder::new(&enc).unwrap();
        // // call decode to decode the first value (13)
        // let val = dec.decode();
        // assert_eq!(val, Some(13));
        // assert_eq!(dec.cursor, 7);
        // //now call decode again to decode the next value (24)
        // let val = dec.decode();
        // assert_eq!(val, Some(24));
        // assert_eq!(dec.cursor, 16);

        // //now call decode again to decode the next value (511)
        // let val = dec.decode();
        // assert_eq!(val, Some(511));
        // assert_eq!(dec.cursor, 33);
    }
}
