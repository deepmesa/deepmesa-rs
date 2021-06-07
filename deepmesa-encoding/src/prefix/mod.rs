pub mod decoder;
pub mod delta;
pub mod encoder;
pub mod gamma;
pub mod unary;
pub mod varbyte;

//TODO: Make this error impl Error. i.e. make it idiomatic rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncodingError {
    msg: String,
}

//TODO: Change this enum name. Not everything is a prefix encoding
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrefixEncoding {
    VarByte,
    Unary,
    Gamma,
    Delta,
    // Golomb,
    // Huffman,
}
