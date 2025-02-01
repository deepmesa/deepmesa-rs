//use crate::matrix::simd::traits::SimdOperation;
use core::fmt::Debug;
use core::fmt::Display;
use std::num::FpCategory;
use std::ops::Mul;

pub(in crate::matrix) trait SimdAddAssign<Rhs = Self> {
    fn simd_add_assign(&mut self, rhs: Rhs);
}

pub(in crate::matrix) trait SimdAdd<Rhs = Self> {
    fn simd_add(&self, rhs: Rhs) -> Self;
}

pub(in crate::matrix) trait SimdAddInto<Rhs = Self> {
    fn simd_add_into(&self, result: &mut Self, rhs: Rhs);
}

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
    fn len(&self) -> usize;
    fn data_ptr(&self) -> *const T;
    fn is_simd_enabled(&self) -> bool;
    fn use_simd(&self) -> bool {
        if !self.is_simd_enabled() {
            return false;
        }

        #[cfg(target_arch = "aarch64")]
        {
            use std::arch::is_aarch64_feature_detected;
            if is_aarch64_feature_detected!("neon") {
                return true;
            }
        }

        return false;
    }
}

pub(in crate::matrix) enum ElementType {
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    F32(f32),
    F64(f64),
}

pub trait MatrixElement: Sized + Default + PartialEq + Copy + Clone + Display + Debug
//+ SimdOperation
{
    type Output;
    fn abs(self) -> Self;
    fn zero() -> Self::Output;
    fn one() -> Self::Output;
    fn simd_supported() -> bool;
    fn power(&self, exp: u16) -> Self::Output;
    fn element_type(&self) -> ElementType;
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
    ($signed:ident, $float:ident, $t:ty, $ty_enum: ident, $zero:literal, $one:literal, $simd_supported:ident) => {
        impl MatrixElement for $t {
            type Output = Self;
            fn_abs!($signed);
            fn_power!($float);

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

            fn element_type(&self) -> ElementType {
                return ElementType::$ty_enum(*self);
            }
        }
    };
}

impl_element_type!(signed, float, f32, F32, 0.0, 1.0, true);
impl_element_type!(signed, float, f64, F64, 0.0, 1.0, true);
impl_element_type!(signed, integer, i8, I8, 0, 1, true);
impl_element_type!(signed, integer, i16, I16, 0, 1, true);
impl_element_type!(signed, integer, i32, I32, 0, 1, true);
impl_element_type!(signed, integer, i64, I64, 0, 1, false);
impl_element_type!(signed, integer, i128, I128, 0, 1, false);
impl_element_type!(unsigned, integer, u8, U8, 0, 1, true);
impl_element_type!(unsigned, integer, u16, U16, 0, 1, true);
impl_element_type!(unsigned, integer, u32, U32, 0, 1, true);
impl_element_type!(unsigned, integer, u64, U64, 0, 1, false);
impl_element_type!(unsigned, integer, u128, U128, 0, 1, false);
