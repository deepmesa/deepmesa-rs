use crate::matrix::simd::traits::SimdAddAssign;
use crate::matrix::simd::traits::SimdAddInto;
use crate::matrix::simd::traits::SimdMulAssign;
use crate::matrix::simd::traits::SimdMulInto;
use crate::matrix::simd::traits::SimdSubAssign;
use crate::matrix::simd::traits::SimdSubInto;
use crate::matrix::traits::ElementType;
use crate::matrix::traits::MatrixElement;

pub(in crate::matrix::simd) struct SimdKernelNeon<T>
where
    T: MatrixElement,
{
    _p: std::marker::PhantomData<T>,
}

macro_rules! impl_simd_add_assign {
    ($(($t: ident, $e:ident)),*) => {
        impl<T> SimdAddAssign<T, T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_add_assign(ptr: *mut T, rhs: T, len: usize) {
                match rhs.element_type() {
                    $(
                        ElementType::$e(val) => {
                            $t::simd_add_assign(ptr as *mut $t, val, len);
                        }
                    )*
                        _ => {
                            panic!("Simd Neon Operation not supported for type {}", std::any::type_name::<T>());
                        }
                }
            }
        }

        impl<T> SimdAddAssign<T, *const T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_add_assign(ptr: *mut T, rhs: * const T, len: usize) {
                match T::ptr_element_type(rhs) {
                    $(
                        ElementType::$e(_) => {
                            $t::simd_add_assign(ptr as *mut $t, rhs as *const $t, len);
                        }
                    )*
                        _ => {
                            panic!("SIMD Neon Operation not supported for type {}",std::any::type_name::<T>());
                        }
                }
            }
        }
    };
}

impl_simd_add_assign!(
    (u8, U8),
    (u16, U16),
    (u32, U32),
    (i8, I8),
    (i16, I16),
    (i32, I32),
    (f32, F32),
    (f64, F64)
);

macro_rules! impl_simd_add_into {
    ($(($t: ident, $e:ident)),*) => {
        impl<T> SimdAddInto<T, T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_add_into(ptr: *const T, rhs: T, dst: *mut T, len: usize) {
                match rhs.element_type() {
                    $(
                        ElementType::$e(val) => {
                            $t::simd_add_into(ptr as *const $t, val, dst as * mut $t, len);
                        }
                    )*
                        _ => {
                            panic!("SIMD Neon Operation not supported for type {}", std::any::type_name::<T>());
                        }
                }
            }
        }

        impl<T> SimdAddInto<T, *const T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_add_into(ptr: *const T, rhs: *const T, dst: *mut T, len: usize) {
                match T::ptr_element_type(rhs) {
                    $(
                        ElementType::$e(_) => {
                            $t::simd_add_into(ptr as *const $t, rhs as *const $t, dst as *mut $t, len);
                        }
                    )*
                        _ => {
                            panic!("SIMD Neon Operation not supported for type {}", std::any::type_name::<T>());
                        }
                }
            }
        }
    };
}

impl_simd_add_into!(
    (u8, U8),
    (u16, U16),
    (u32, U32),
    (i8, I8),
    (i16, I16),
    (i32, I32),
    (f32, F32),
    (f64, F64)
);

macro_rules! impl_simd_sub_assign {
    ($(($t: ident, $e:ident)),*) => {
        impl<T> SimdSubAssign<T, T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_sub_assign(ptr: *mut T, rhs: T, len: usize) {
                match rhs.element_type() {
                    $(
                        ElementType::$e(val) => {
                            $t::simd_sub_assign(ptr as *mut $t, val, len);
                        }
                    )*
                        _ => {
                            panic!("Simd Neon Operation not supported for type {}", std::any::type_name::<T>());
                        }
                }
            }
        }

        impl<T> SimdSubAssign<T, *const T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_sub_assign(ptr: *mut T, rhs: * const T, len: usize) {
                match T::ptr_element_type(rhs) {
                    $(
                        ElementType::$e(_) => {
                            $t::simd_sub_assign(ptr as *mut $t, rhs as *const $t, len);
                        }
                    )*
                        _ => {
                            panic!("SIMD Neon Operation not supported for type {}",std::any::type_name::<T>());
                        }
                }
            }
        }
    };
}

impl_simd_sub_assign!(
    (u8, U8),
    (u16, U16),
    (u32, U32),
    (i8, I8),
    (i16, I16),
    (i32, I32),
    (f32, F32),
    (f64, F64)
);

macro_rules! impl_simd_sub_into {
    ($(($t: ident, $e:ident)),*) => {
        impl<T> SimdSubInto<T, T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_sub_into(ptr: *const T, rhs: T, dst: *mut T, len: usize) {
                match rhs.element_type() {
                    $(
                        ElementType::$e(val) => {
                            $t::simd_sub_into(ptr as *const $t, val, dst as * mut $t, len);
                        }
                    )*
                        _ => {
                            panic!("SIMD Neon Operation not supported for type {}", std::any::type_name::<T>());
                        }
                }
            }
        }

        impl<T> SimdSubInto<T, *const T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_sub_into(ptr: *const T, rhs: *const T, dst: *mut T, len: usize) {
                match T::ptr_element_type(rhs) {
                    $(
                        ElementType::$e(_) => {
                            $t::simd_sub_into(ptr as *const $t, rhs as *const $t, dst as *mut $t, len);
                        }
                    )*
                        _ => {
                            panic!("SIMD Neon Operation not supported for type {}", std::any::type_name::<T>());
                        }
                }
            }
        }
    };
}

impl_simd_sub_into!(
    (u8, U8),
    (u16, U16),
    (u32, U32),
    (i8, I8),
    (i16, I16),
    (i32, I32),
    (f32, F32),
    (f64, F64)
);

macro_rules! impl_simd_mul_assign {
    ($(($t: ident, $e:ident)),*) => {
        impl<T> SimdMulAssign<T, T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_mul_assign(ptr: *mut T, rhs: T, len: usize) {
                match rhs.element_type() {
                    $(
                        ElementType::$e(val) => {
                            $t::simd_mul_assign(ptr as *mut $t, val, len);
                        }
                    )*
                        _ => {
                            panic!("Simd Neon Operation not supported for type {}", std::any::type_name::<T>());
                        }
                }
            }
        }

        impl<T> SimdMulAssign<T, *const T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_mul_assign(ptr: *mut T, rhs: * const T, len: usize) {
                match T::ptr_element_type(rhs) {
                    $(
                        ElementType::$e(_) => {
                            $t::simd_mul_assign(ptr as *mut $t, rhs as *const $t, len);
                        }
                    )*
                        _ => {
                            panic!("SIMD Neon Operation not supported for type {}",std::any::type_name::<T>());
                        }
                }
            }
        }
    };
}

impl_simd_mul_assign!(
    (u8, U8),
    (u16, U16),
    (u32, U32),
    (i8, I8),
    (i16, I16),
    (i32, I32),
    (f32, F32),
    (f64, F64)
);

macro_rules! impl_simd_mul_into {
    ($(($t: ident, $e:ident)),*) => {
        impl<T> SimdMulInto<T, T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_mul_into(ptr: *const T, rhs: T, dst: *mut T, len: usize) {
                match rhs.element_type() {
                    $(
                        ElementType::$e(val) => {
                            $t::simd_mul_into(ptr as *const $t, val, dst as * mut $t, len);
                        }
                    )*
                        _ => {
                            panic!("SIMD Neon Operation not supported for type {}", std::any::type_name::<T>());
                        }
                }
            }
        }

        impl<T> SimdMulInto<T, *const T> for SimdKernelNeon<T>
        where
            T: MatrixElement,
        {
            unsafe fn simd_mul_into(ptr: *const T, rhs: *const T, dst: *mut T, len: usize) {
                match T::ptr_element_type(rhs) {
                    $(
                        ElementType::$e(_) => {
                            $t::simd_mul_into(ptr as *const $t, rhs as *const $t, dst as *mut $t, len);
                        }
                    )*
                        _ => {
                            panic!("SIMD Neon Operation not supported for type {}", std::any::type_name::<T>());
                        }
                }
            }
        }
    };
}

impl_simd_mul_into!(
    (u8, U8),
    (u16, U16),
    (u32, U32),
    (i8, I8),
    (i16, I16),
    (i32, I32),
    (f32, F32),
    (f64, F64)
);
