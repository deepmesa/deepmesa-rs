use crate::prefix::PrefixEncoding;
use deepmesa_collections::bitvec::bitvec::BitVector;

pub struct PrefixEncoder {
    pub(crate) bitvec: BitVector,
    pub(crate) encoding: Option<PrefixEncoding>,
    pub(crate) elements: usize,
}

pub trait VarByteEncoder {
    fn encode_varbyte_u8(&mut self, val: u8) {
        self.encode_varbyte_u128(val as u128);
    }
    fn encode_varbyte_u16(&mut self, val: u16) {
        self.encode_varbyte_u128(val as u128);
    }
    fn encode_varbyte_u32(&mut self, val: u32) {
        self.encode_varbyte_u128(val as u128);
    }
    fn encode_varbyte_u64(&mut self, val: u64) {
        self.encode_varbyte_u128(val as u128);
    }
    fn encode_varbyte_u128(&mut self, val: u128);
}

pub trait UnaryEncoder {
    fn encode_unary_u8(&mut self, val: u8) {
        self.encode_unary_u128(val as u128);
    }
    fn encode_unary_u16(&mut self, val: u16) {
        self.encode_unary_u128(val as u128);
    }
    fn encode_unary_u32(&mut self, val: u32) {
        self.encode_unary_u128(val as u128);
    }
    fn encode_unary_u64(&mut self, val: u64) {
        self.encode_unary_u128(val as u128);
    }
    fn encode_unary_u128(&mut self, val: u128);
}

pub trait GammaEncoder {
    fn encode_gamma_u8(&mut self, val: u8) {
        self.encode_gamma_u128(val as u128);
    }
    fn encode_gamma_u16(&mut self, val: u16) {
        self.encode_gamma_u128(val as u128);
    }
    fn encode_gamma_u32(&mut self, val: u32) {
        self.encode_gamma_u128(val as u128);
    }
    fn encode_gamma_u64(&mut self, val: u64) {
        self.encode_gamma_u128(val as u128);
    }
    fn encode_gamma_u128(&mut self, val: u128);
}

pub trait DeltaEncoder {
    fn encode_delta_u8(&mut self, val: u8) {
        self.encode_delta_u128(val as u128);
    }
    fn encode_delta_u16(&mut self, val: u16) {
        self.encode_delta_u128(val as u128);
    }
    fn encode_delta_u32(&mut self, val: u32) {
        self.encode_delta_u128(val as u128);
    }
    fn encode_delta_u64(&mut self, val: u64) {
        self.encode_delta_u128(val as u128);
    }
    fn encode_delta_u128(&mut self, val: u128);
}

pub trait Encoder: VarByteEncoder + UnaryEncoder + GammaEncoder + DeltaEncoder {
    fn encode_u8(&mut self, val: u8) {
        self.encode_u128(val as u128);
    }
    fn encode_u16(&mut self, val: u16) {
        self.encode_u128(val as u128);
    }
    fn encode_u32(&mut self, val: u32) {
        self.encode_u128(val as u128);
    }
    fn encode_u64(&mut self, val: u64) {
        self.encode_u128(val as u128);
    }
    fn encode_u128(&mut self, val: u128) {
        match self.encoding() {
            Some(PrefixEncoding::VarByte) => self.encode_varbyte_u128(val),
            Some(PrefixEncoding::Unary) => self.encode_unary_u128(val),
            Some(PrefixEncoding::Gamma) => self.encode_gamma_u128(val),
            Some(PrefixEncoding::Delta) => self.encode_delta_u128(val),
            None => {
                panic!("Unspecified Encoding 'None'");
            }
        }
    }

    fn encoding(&self) -> Option<PrefixEncoding>;
    fn encoded(&self) -> &BitVector;
    fn elements(&self) -> usize;
    fn len_bits(&self) -> usize;
}

impl PrefixEncoder {
    pub fn new(encoding: PrefixEncoding) -> PrefixEncoder {
        PrefixEncoder {
            bitvec: BitVector::with_capacity(1024),
            encoding: Some(encoding),
            elements: 0,
        }
    }

    pub fn with_capacity(encoding: PrefixEncoding, capacity_bits: usize) -> PrefixEncoder {
        PrefixEncoder {
            bitvec: BitVector::with_capacity(capacity_bits),
            encoding: Some(encoding),
            elements: 0,
        }
    }
}

impl Encoder for PrefixEncoder {
    fn encoded(&self) -> &BitVector {
        &self.bitvec
    }

    fn elements(&self) -> usize {
        self.elements
    }

    fn len_bits(&self) -> usize {
        self.bitvec.len()
    }

    fn encoding(&self) -> Option<PrefixEncoding> {
        self.encoding
    }
}
