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

pub trait AddInto<Rhs, Output> {
    fn add_into(&self, rhs: Rhs, result: &mut Output);
}

pub trait SubInto<Rhs, Output> {
    fn sub_into(&self, rhs: Rhs, result: &mut Output);
}

pub trait MulInto<Rhs, Output> {
    fn mul_into(&self, rhs: Rhs, result: &mut Output);
}

pub trait MatMul<Rhs, Output> {
    fn mat_mul(&self, rhs: &Rhs, result: &mut Output);
}

pub enum ElementType {
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

pub trait MatrixElementType {
    fn element_type(&self) -> ElementType;
    fn ptr_element_type(ptr: *const Self) -> ElementType;
}

pub trait MatrixElement:
    Sized + Default + PartialEq + Copy + Clone + Display + Debug + MatrixElementType
{
    type Output;
    fn abs(self) -> Self;
    fn zero() -> Self::Output;
    fn one() -> Self::Output;
    fn simd_supported() -> bool;
    fn power(&self, exp: u16) -> Self::Output;
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

macro_rules! impl_matrix_element {
    ($signed:ident, $float:ident, $t:ty, $zero:literal, $one:literal, $simd_supported:ident) => {
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
        }
    };
}

impl_matrix_element!(signed, float, f32, 0.0, 1.0, true);
impl_matrix_element!(signed, float, f64, 0.0, 1.0, true);
impl_matrix_element!(signed, integer, i8, 0, 1, true);
impl_matrix_element!(signed, integer, i16, 0, 1, true);
impl_matrix_element!(signed, integer, i32, 0, 1, true);
impl_matrix_element!(signed, integer, i64, 0, 1, false);
impl_matrix_element!(signed, integer, i128, 0, 1, false);
impl_matrix_element!(unsigned, integer, u8, 0, 1, true);
impl_matrix_element!(unsigned, integer, u16, 0, 1, true);
impl_matrix_element!(unsigned, integer, u32, 0, 1, true);
impl_matrix_element!(unsigned, integer, u64, 0, 1, false);
impl_matrix_element!(unsigned, integer, u128, 0, 1, false);

macro_rules! impl_matrix_element_type {
    (integer, $t:ident, $ty_enum:ident) => {
        impl MatrixElementType for $t {
            fn element_type(&self) -> ElementType {
                return ElementType::$ty_enum(*self);
            }

            fn ptr_element_type(_ptr: *const Self) -> ElementType {
                return ElementType::$ty_enum(0);
            }
        }
    };
    (float, $t:ident, $ty_enum:ident) => {
        impl MatrixElementType for $t {
            fn element_type(&self) -> ElementType {
                return ElementType::$ty_enum(*self);
            }

            fn ptr_element_type(_ptr: *const Self) -> ElementType {
                return ElementType::$ty_enum(0.0);
            }
        }
    };
}

impl_matrix_element_type!(float, f32, F32);
impl_matrix_element_type!(float, f64, F64);
impl_matrix_element_type!(integer, i8, I8);
impl_matrix_element_type!(integer, i16, I16);
impl_matrix_element_type!(integer, i32, I32);
impl_matrix_element_type!(integer, i64, I64);
impl_matrix_element_type!(integer, i128, I128);
impl_matrix_element_type!(integer, u8, U8);
impl_matrix_element_type!(integer, u16, U16);
impl_matrix_element_type!(integer, u32, U32);
impl_matrix_element_type!(integer, u64, U64);
impl_matrix_element_type!(integer, u128, U128);
