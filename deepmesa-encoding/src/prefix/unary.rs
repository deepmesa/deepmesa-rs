use crate::prefix::{
    decoder::{PrefixDecoder, UnaryDecoder},
    encoder::{PrefixEncoder, UnaryEncoder},
};

//TODO: Unary alg needs to be rewritten using new methods in bit vec
// and bit slice: leading_ones().
impl<'a> UnaryDecoder for PrefixDecoder<'a> {
    fn decode_unary(&mut self) -> Option<u128> {
        if self.cursor >= self.bitvec.len() {
            return None;
        }

        //Now get the byte that the cursor is in and bitshift it left
        // by the remainder
        let (mut byte, read) = self.bitvec.read_u8(self.cursor / 8);
        if read == 0 {
            panic!("ERROR!"); //TODO;
        }
        byte = byte << self.cursor % 8;

        //let mut byte = self.bitvec.byte_at(self.cursor / 8).unwrap() << self.cursor % 8;
        // now count the leading ones
        let mut count = byte.leading_ones() as usize;
        if count < (8 - self.cursor % 8) {
            //if the count is less than the byte then we're done
            //increment the cursor by the count and return
            self.cursor += (count + 1) as usize;
            return Some(count as u128);
        }
        //now increment the cursor by the remaining bits in the byte
        // to move it to the byte boundary
        self.cursor += 8 - (self.cursor % 8);

        //implicit else, the byte (starting at the cursor is full of
        // ones. Start looping through the rest of the bytes.
        loop {
            let (byte, read) = self.bitvec.read_u8(self.cursor / 8);
            if read == 0 {
                panic!("ERROR!"); //todo;
            }
            //byte = self.bitvec.byte_at(self.cursor / 8).unwrap();

            let ones = byte.leading_ones() as usize;
            count += ones;
            if ones < 8 {
                self.cursor += (ones + 1) as usize;
                break;
            }
            self.cursor += 8;
        }
        return Some(count as u128);
    }
}

impl UnaryEncoder for PrefixEncoder {
    fn encode_unary_u128(&mut self, val: u128) {
        // The unary encoder can only encode upto a usize:: MAX value
        if val > usize::MAX as u128 {
            panic!("Cannot unary encode val {} that exceeds usize::MAX", val);
        }
        self.bitvec.fill(true, val as usize);
        //push the terminating continuation bit
        self.bitvec.fill(false, 1);
        self.elements += 1;
    }
}

#[cfg(test)]
mod tests {
    use crate::prefix::decoder::Decoder;
    use crate::prefix::decoder::PrefixDecoder;
    use crate::prefix::encoder::Encoder;
    use crate::prefix::encoder::PrefixEncoder;
    use crate::prefix::PrefixEncoding::Unary;
    use std::convert::TryInto;

    // encoded = 1010_1010_1010_1010
    #[test]
    fn test_encode_1() {
        //encode 1, 8 times
        let mut ue = PrefixEncoder::new(Unary);
        let mut expected_byte = 0b0000_0000;
        for i in 0..8 {
            // if i == 4 {
            //     expected_byte = 0b0000_0000;
            // }
            ue.encode_u128(1);
            let enc = ue.encoded();
            assert_eq!(enc.len(), (i + 1) * 2);
            assert_eq!(enc[(i * 2)..(i + 1) * 2].as_u8(), (0b10, 2));

            // {
            //     let enc = ue.encoded();
            //     //                assert_eq!(enc.encoding(), Some(&Unary));
            //     assert_eq!(enc.len(), (i * 2) + 2, "At i={}", i);
            //     if i < 4 {
            //         expected_byte += 2u8.pow((7 - (i * 2)).try_into().unwrap());
            //         assert_eq!(
            //             enc.byte_at(0).unwrap(),
            //             expected_byte,
            //             "At i= {}, EncByte={:08b}, Expected Byte={:08b}",
            //             i,
            //             enc.byte_at(0).unwrap(),
            //             expected_byte,
            //         );
            //         assert_eq!(enc.byte_at(1), None);
            //     } else {
            //         assert_eq!(enc.byte_at(0).unwrap(), 0b1010_1010);
            //         expected_byte += 2u8.pow((7 - ((i - 4) * 2)).try_into().unwrap());
            //         assert_eq!(enc.byte_at(1).unwrap(), expected_byte);
            //     }
            // }
        }

        //now start the decoding
        let enc = ue.encoded();
        assert_eq!(enc.len(), 16);
        assert_eq!(enc.read_u16(0), (0b1010_1010_1010_1010, 16));
        //now create a decoder
        let mut dec = PrefixDecoder::new(&enc, Unary);
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
        let mut ue = PrefixEncoder::new(Unary);
        ue.encode_u128(1); //10
        let enc = ue.encoded();
        //            assert_eq!(enc.encoding(), Some(&Unary));
        assert_eq!(enc.len(), 2);
        assert_eq!(enc[0..2].as_u8(), (0b10, 2));
        //assert_eq!(enc.byte_at(0).unwrap(), 0b1000_0000);
        //            assert_eq!(enc.byte_at(1), None);

        //now encode a larger number thats not a multiple of 8
        ue.encode_u128(17);
        // {
        //     let enc = ue.encoded();
        //     assert_eq!(enc.encoding(), Some(&Unary));
        //     assert_eq!(enc.len_bits(), 20);
        //     assert_eq!(enc.byte_at(0).unwrap(), 0b1011_1111);
        //     assert_eq!(enc.byte_at(1).unwrap(), 0b1111_1111);
        //     assert_eq!(enc.byte_at(2).unwrap(), 0b1110_0000);
        //     assert_eq!(enc.byte_at(3), None);
        // }

        // let enc = ue.encoded();
        // //now create a decoder
        // let mut dec = PrefixDecoder::new(&enc).unwrap();
        // // call decode to decode the first value
        // let val = dec.decode();
        // assert_eq!(val, Some(1));
        // assert_eq!(dec.cursor, 2);
        // //now call decode again to decode the next value (17)
        // let val = dec.decode();
        // assert_eq!(val, Some(17));
        // assert_eq!(dec.cursor, 20);
    }
}
