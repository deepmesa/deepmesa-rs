use std::mem;

use deepmesa_collections::bitvec::BitOrder;

use crate::prefix::{
    decoder::{DeltaDecoder, GammaDecoder, PrefixDecoder},
    encoder::{DeltaEncoder, GammaEncoder, PrefixEncoder},
};

impl<'a> DeltaDecoder for PrefixDecoder<'a> {
    fn decode_delta(&mut self) -> Option<u128> {
        //first decode the gamma prefix
        let prefix = self.decode_gamma();
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

impl DeltaEncoder for PrefixEncoder {
    fn encode_delta_u128(&mut self, val: u128) {
        //Chop off the MSB 1 bit and count the remaining bits to get the offset len
        let lz: usize = val.leading_zeros() as usize;
        let offset_len = (mem::size_of::<u128>() * 8) - (lz + 1);
        //encode the offset in gamma code by that amount
        self.encode_gamma_u128(offset_len as u128);
        //Append the delta offset to the bitvec
        self.bitvec.push_bits_u128(val, offset_len, BitOrder::Lsb0);
    }
}

#[cfg(test)]
mod tests {
    use crate::prefix::decoder::Decoder;
    use crate::prefix::decoder::PrefixDecoder;
    use crate::prefix::encoder::Encoder;
    use crate::prefix::encoder::PrefixEncoder;
    use crate::prefix::PrefixEncoding::Delta;

    #[test]
    fn test_encode_decode() {
        let mut ge = PrefixEncoder::new(Delta);
        ge.encode_u128(13); //Delta code: 10,1,101
        let enc = ge.encoded();
        assert_eq!(enc.len(), 6);
        assert_eq!(enc[0..6].as_u8(), (0b10_1_101, 6));
        // let (byte, read) = enc.read_u8(0);
        // assert_eq!(read, 6);
        // assert_eq!(byte, 0b1011_0100);
        // //assert_eq!(enc.byte_at(1), None);
        ge.encode_u128(24); // Delta Code: 110,00,1000
                            // {
                            //     let enc = ge.encoded();
                            //     assert_eq!(enc.len_bits(), 15);

        //     assert_eq!(enc.byte_at(0).unwrap(), 0b1011_0111);
        //     assert_eq!(enc.byte_at(1).unwrap(), 0b0001_0000);
        //     assert_eq!(enc.byte_at(2), None);
        // }
        // ge.encode_u128(511); // Delta Code: 1110,000,1111_1111
        // {
        //     let enc = ge.encoded();
        //     assert_eq!(enc.len_bits(), 30);
        //     assert_eq!(enc.byte_at(0).unwrap(), 0b1011_0111);
        //     assert_eq!(enc.byte_at(1).unwrap(), 0b0001_0001);
        //     assert_eq!(enc.byte_at(2).unwrap(), 0b1100_0011);
        //     assert_eq!(enc.byte_at(3).unwrap(), 0b1111_1100);
        //     assert_eq!(enc.byte_at(4), None);
        // }

        // let enc = ge.encoded();
        // //now create a decoder
        // let mut dec = PrefixDecoder::new(&enc).unwrap();
        // // call decode to decode the first value (13)
        // let val = dec.decode();
        // assert_eq!(val, Some(13));
        // assert_eq!(dec.cursor, 6);
        // //now call decode again to decode the next value (24)
        // let val = dec.decode();
        // assert_eq!(
        //     val,
        //     Some(24),
        //     "val={:08b}, expected: {:08b}",
        //     val.unwrap(),
        //     24
        // );
        // assert_eq!(dec.cursor, 15);

        // //now call decode again to decode the next value (511)
        // let val = dec.decode();
        // assert_eq!(val, Some(511));
        // assert_eq!(dec.cursor, 30);
    }
}
