use deepmesa_collections::bitvec::bitvec::BitVector;

use crate::prefix::{EncodingError, PrefixEncoding};

pub trait VarByteDecoder {
    fn decode_varbyte(&mut self) -> Option<u128>;
}

pub trait UnaryDecoder {
    fn decode_unary(&mut self) -> Option<u128>;
}

pub trait GammaDecoder {
    fn decode_gamma(&mut self) -> Option<u128>;
}

pub trait DeltaDecoder {
    fn decode_delta(&mut self) -> Option<u128>;
}

pub trait Decoder: Iterator + VarByteDecoder + UnaryDecoder + GammaDecoder + DeltaDecoder {
    fn encoding(&self) -> Option<&PrefixEncoding>;

    fn decode(&mut self) -> Option<u128> {
        match self.encoding() {
            Some(PrefixEncoding::VarByte) => self.decode_varbyte(),
            Some(PrefixEncoding::Unary) => self.decode_unary(),
            Some(PrefixEncoding::Gamma) => self.decode_gamma(),
            Some(PrefixEncoding::Delta) => self.decode_delta(),
            None => {
                panic!("Unspecified encoding 'None'");
            }
        }
    }
}

pub struct PrefixDecoder<'a> {
    pub(crate) bitvec: &'a BitVector,
    pub(crate) encoding: Option<PrefixEncoding>,
    pub(crate) cursor: usize,
}

impl<'a> Decoder for PrefixDecoder<'a> {
    fn encoding(&self) -> Option<&PrefixEncoding> {
        self.encoding.as_ref()
    }
}

impl<'a> PrefixDecoder<'a> {
    pub fn new(encoded: &'a BitVector, encoding: PrefixEncoding) -> PrefixDecoder {
        return PrefixDecoder {
            bitvec: encoded,
            encoding: Some(encoding),
            cursor: 0,
        };
    }
}

impl<'a> Iterator for PrefixDecoder<'a> {
    type Item = u128;
    fn next(&mut self) -> Option<Self::Item> {
        self.decode()
    }
}
