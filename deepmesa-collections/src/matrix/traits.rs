use core::fmt::Debug;
use core::fmt::Display;
use std::num::FpCategory;
use std::ops::Mul;

use super::simd::SimdOperation;

// pub enum NumericDataType {
//     U8,
//     U16,
//     U32,
//     U64,
//     U128,
//     I8,
//     I16,
//     I32,
//     I64,
//     I128,
//     F32,
//     F64,
// }

pub trait MatrixElement:
    Sized + Default + PartialEq + Copy + Clone + Display + Debug + SimdOperation //+ NumericType
{
    type Output;
    fn abs(self) -> Self;
    fn zero() -> Self::Output;
    fn one() -> Self::Output;
    fn simd_supported() -> bool;
}

// pub trait NumericType {
//     fn numeric_type() -> NumericDataType;
// }

pub trait CheckedMul: Sized + Mul<Self, Output = Self> {
    fn checked_mul(self, rhs: Self) -> Option<Self>;
}

// macro_rules! impl_numeric_type {
//     ($t:ty, $nt:expr) => {
//         impl NumericType for $t {
//             fn numeric_type() -> NumericDataType {
//                 $nt
//             }
//         }
//     };
// }

// impl_numeric_type!(u8, NumericDataType::U8);
// impl_numeric_type!(u16, NumericDataType::U16);
// impl_numeric_type!(u32, NumericDataType::U32);
// impl_numeric_type!(u64, NumericDataType::U64);
// impl_numeric_type!(u128, NumericDataType::U128);
// impl_numeric_type!(i8, NumericDataType::I8);
// impl_numeric_type!(i16, NumericDataType::I16);
// impl_numeric_type!(i32, NumericDataType::I32);
// impl_numeric_type!(i64, NumericDataType::I64);
// impl_numeric_type!(i128, NumericDataType::I128);
// impl_numeric_type!(f32, NumericDataType::F32);
// impl_numeric_type!(f64, NumericDataType::F64);

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

macro_rules! impl_element_type {
    ($s:ident, $t:ty, $zero:literal, $one:literal, $simd_supported:ident) => {
        impl MatrixElement for $t {
            type Output = Self;
            fn_abs!($s);

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
        }
    };
}

impl_element_type!(signed, f32, 0.0, 1.0, true);
impl_element_type!(signed, f64, 0.0, 1.0, true);
impl_element_type!(signed, i8, 0, 1, true);
impl_element_type!(signed, i16, 0, 1, true);
impl_element_type!(signed, i32, 0, 1, true);
impl_element_type!(signed, i64, 0, 1, false);
impl_element_type!(signed, i128, 0, 1, false);
impl_element_type!(unsigned, u8, 0, 1, true);
impl_element_type!(unsigned, u16, 0, 1, true);
impl_element_type!(unsigned, u32, 0, 1, true);
impl_element_type!(unsigned, u64, 0, 1, false);
impl_element_type!(unsigned, u128, 0, 1, false);
