use crate::matrix::simd::traits::SimdOperation;
use core::fmt::Debug;
use core::fmt::Display;
use std::num::FpCategory;
use std::ops::Mul;

pub trait FillRow<Rhs> {
    fn fill_row(&mut self, row: usize, val: Rhs);
}

pub trait FillColumn<Rhs> {
    fn fill_column(&mut self, col: usize, val: Rhs);
}

pub trait FillDiagonal<Rhs> {
    fn fill_diagonal(&mut self, val: Rhs);
}

pub trait Set<T> {
    fn set(&mut self, row: usize, col: usize, val: T);
}

pub trait Get<T> {
    fn get(&self, row: usize, col: usize) -> T;
}

pub trait AddInto<Rhs, Output> {
    fn add_into(&self, rhs: Rhs, result: &mut Output);
}

pub(in crate::matrix) trait Dataset<T>
where
    T: MatrixElement,
{
    fn rows(&self) -> usize;
    fn cols(&self) -> usize;
    fn get(&self, row: usize, col: usize) -> T;
}

pub trait MatrixElement:
    Sized + Default + PartialEq + Copy + Clone + Display + Debug + SimdOperation
{
    type Output;
    fn abs(self) -> Self;
    fn zero() -> Self::Output;
    fn one() -> Self::Output;
    fn simd_supported() -> bool;
    fn power(&self, exp: u16) -> Self::Output;
    fn to_f64(&self) -> f64;
    fn to_f32(&self) -> f32;
    fn to_u8(&self) -> u8;
    fn to_u16(&self) -> u16;
    fn to_u32(&self) -> u32;
    fn to_u64(&self) -> u64;
    fn to_u128(&self) -> u128;
    fn to_i8(&self) -> i8;
    fn to_i16(&self) -> i16;
    fn to_i32(&self) -> i32;
    fn to_i64(&self) -> i64;
    fn to_i128(&self) -> i128;
}

pub trait CheckedMul: Sized + Mul<Self, Output = Self> {
    fn checked_mul(self, rhs: Self) -> Option<Self>;
}

macro_rules! impl_checked_mul {
    ($t:ty) => {
        impl CheckedMul for $t {
            fn checked_mul(self, rhs: Self) -> Option<$t> {
                return <$t>::checked_mul(self, rhs);
            }
        }
    };
}

macro_rules! impl_checked_mul_float {
    ($t:ty) => {
        impl CheckedMul for $t {
            fn checked_mul(self, rhs: Self) -> Option<$t> {
                let val = self.mul(rhs);
                match val.classify() {
                    FpCategory::Infinite | FpCategory::Nan | FpCategory::Subnormal => {
                        return None;
                    }
                    _ => {
                        return Some(val);
                    }
                }
            }
        }
    };
}

impl_checked_mul!(u8);
impl_checked_mul!(u16);
impl_checked_mul!(u32);
impl_checked_mul!(u64);
impl_checked_mul!(u128);
impl_checked_mul!(i8);
impl_checked_mul!(i16);
impl_checked_mul!(i32);
impl_checked_mul!(i64);
impl_checked_mul!(i128);
impl_checked_mul_float!(f32);
impl_checked_mul_float!(f64);

macro_rules! fn_abs {
    (signed) => {
        fn abs(self) -> Self {
            self.abs()
        }
    };
    (unsigned) => {
        fn abs(self) -> Self {
            self
        }
    };
}

macro_rules! fn_power {
    (integer) => {
        fn power(&self, exp: u16) -> Self::Output {
            return self.pow(exp as u32);
        }
    };
    (float) => {
        fn power(&self, exp: u16) -> Self::Output {
            return self.powi(exp as i32);
        }
    };
}

macro_rules! impl_element_type {
    ($s:ident, $f:ident, $t:ty, $zero:literal, $one:literal, $simd_supported:ident) => {
        impl MatrixElement for $t {
            type Output = Self;
            fn_abs!($s);
            fn_power!($f);

            fn simd_supported() -> bool {
                #[cfg(target_arch = "aarch64")]
                {
                    use std::arch::is_aarch64_feature_detected;
                    if is_aarch64_feature_detected!("neon") {
                        return $simd_supported;
                    }
                }
                return false;
            }

            fn zero() -> Self::Output {
                $zero
            }

            fn one() -> Self::Output {
                $one
            }

            fn to_f64(&self) -> f64 {
                return *self as f64;
            }

            fn to_f32(&self) -> f32 {
                return *self as f32;
            }

            fn to_u8(&self) -> u8 {
                return *self as u8;
            }

            fn to_u16(&self) -> u16 {
                return *self as u16;
            }

            fn to_u32(&self) -> u32 {
                return *self as u32;
            }

            fn to_u64(&self) -> u64 {
                return *self as u64;
            }

            fn to_u128(&self) -> u128 {
                return *self as u128;
            }

            fn to_i8(&self) -> i8 {
                return *self as i8;
            }

            fn to_i16(&self) -> i16 {
                return *self as i16;
            }

            fn to_i32(&self) -> i32 {
                return *self as i32;
            }

            fn to_i64(&self) -> i64 {
                return *self as i64;
            }

            fn to_i128(&self) -> i128 {
                return *self as i128;
            }
        }
    };
}

impl_element_type!(signed, float, f32, 0.0, 1.0, true);
impl_element_type!(signed, float, f64, 0.0, 1.0, true);
impl_element_type!(signed, integer, i8, 0, 1, true);
impl_element_type!(signed, integer, i16, 0, 1, true);
impl_element_type!(signed, integer, i32, 0, 1, true);
impl_element_type!(signed, integer, i64, 0, 1, false);
impl_element_type!(signed, integer, i128, 0, 1, false);
impl_element_type!(unsigned, integer, u8, 0, 1, true);
impl_element_type!(unsigned, integer, u16, 0, 1, true);
impl_element_type!(unsigned, integer, u32, 0, 1, true);
impl_element_type!(unsigned, integer, u64, 0, 1, false);
impl_element_type!(unsigned, integer, u128, 0, 1, false);
