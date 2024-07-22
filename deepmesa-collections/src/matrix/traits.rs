use core::fmt::Debug;
use core::fmt::Display;

pub trait MatrixElement: Sized + Default + PartialEq + Copy + Clone + Display + Debug {
    type Output;
    fn abs(self) -> Self;
    fn zero() -> Self::Output;
    fn one() -> Self::Output;
}

macro_rules! impl_element_type {
    ($for:ty, $zero:literal, $one:literal) => {
        impl MatrixElement for $for {
            type Output = Self;
            fn abs(self) -> Self {
                self.abs()
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

macro_rules! impl_element_type_unsigned {
    ($for:ty) => {
        impl MatrixElement for $for {
            type Output = Self;
            fn abs(self) -> Self {
                self
            }
            fn zero() -> Self::Output {
                0
            }
            fn one() -> Self::Output {
                1
            }
        }
    };
}

impl_element_type!(f32, 0.0, 1.0);
impl_element_type!(f64, 0.0, 1.0);
impl_element_type!(i8, 0, 1);
impl_element_type!(i16, 0, 1);
impl_element_type!(i32, 0, 1);
impl_element_type!(i64, 0, 1);
impl_element_type!(i128, 0, 1);
impl_element_type_unsigned!(u8);
impl_element_type_unsigned!(u16);
impl_element_type_unsigned!(u32);
impl_element_type_unsigned!(u64);
impl_element_type_unsigned!(u128);
