#[macro_use]
pub(super) mod macros;

pub mod delta;
pub mod gamma;
pub mod golomb;
pub mod unary;
pub mod varbyte;

const U128_BITS: usize = 128;
