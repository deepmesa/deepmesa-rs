pub(in crate::matrix::simd::neon) mod addassign;
pub(in crate::matrix::simd::neon) mod addinto;
pub(in crate::matrix::simd) mod kernel;
pub(in crate::matrix::simd::neon) mod mulassign;
pub(in crate::matrix::simd::neon) mod mulinto;
pub(in crate::matrix::simd::neon) mod subassign;
pub(in crate::matrix::simd::neon) mod subinto;
pub(in crate::matrix::simd::neon) mod vaddq;
pub(in crate::matrix::simd::neon) mod vaddqxn;
pub(in crate::matrix::simd::neon) mod vdup;
pub(in crate::matrix::simd::neon) mod vload;
pub(in crate::matrix::simd::neon) mod vmulq;
pub(in crate::matrix::simd::neon) mod vmulqxn;
pub(in crate::matrix::simd::neon) mod vstore;
pub(in crate::matrix::simd::neon) mod vsubq;
pub(in crate::matrix::simd::neon) mod vsubqxn;
use crate::matrix::traits::MatrixElement;
use std::marker::PhantomData;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) const SIMD_NEON_VEC_SIZE_BYTES: usize = 16;
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) const SIMD_NEON_LOAD_SIZE_4: usize = 4;
