#[macro_use]
pub(in crate::matrix) mod macros;
pub(in crate::matrix) mod dataset;
pub mod iter;
pub mod matmul;
pub mod matrix;
pub(in crate::matrix) mod simd;
#[cfg(test)]
pub(in crate::matrix) mod tests;
pub mod traits;
pub mod vector;
