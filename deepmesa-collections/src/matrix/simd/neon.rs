//SIMD for arm64 Neon - simdneon. This doesn't support Arm SVE.

use crate::matrix::matrix::Matrix;
use crate::matrix::matrix::SyncDirection;
use crate::matrix::simd::SimdVecBuffer;
use crate::matrix::simd::{SimdMetaData, SimdOperation};
use crate::matrix::traits::MatrixElement;
use std::arch::aarch64::*;
use std::marker::PhantomData;
use std::ptr;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vec_load {
    (u8, x1, $v:ident, $ptr:ident) => {
        let $v: uint8x16_t = vld1q_u8($ptr);
    };
    (u8, x2, $v:ident, $ptr:ident) => {
        let $v: uint8x16x2_t = vld1q_u8_x2($ptr);
    };
    (u8, x3, $v:ident, $ptr:ident) => {
        let $v: uint8x16x3_t = vld1q_u8_x3($ptr);
    };
    (u8, x4, $v:ident, $ptr:ident) => {
        let $v: uint8x16x4_t = vld1q_u8_x4($ptr);
    };
    (u16, x1, $v:ident, $ptr:ident) => {
        let $v: uint16x8_t = vld1q_u16($ptr);
    };
    (u16, x2, $v:ident, $ptr:ident) => {
        let $v: uint16x8x2_t = vld1q_u16_x2($ptr);
    };
    (u16, x3, $v:ident, $ptr:ident) => {
        let $v: uint16x8x3_t = vld1q_u16_x3($ptr);
    };
    (u16, x4, $v:ident, $ptr:ident) => {
        let $v: uint16x8x4_t = vld1q_u16_x4($ptr);
    };
    (u32, x1, $v:ident, $ptr:ident) => {
        let $v: uint32x4_t = vld1q_u32($ptr);
    };
    (u32, x2, $v:ident, $ptr:ident) => {
        let $v: uint32x4x2_t = vld1q_u32_x2($ptr);
    };
    (u32, x3, $v:ident, $ptr:ident) => {
        let $v: uint32x4x3_t = vld1q_u32_x3($ptr);
    };
    (u32, x4, $v:ident, $ptr:ident) => {
        let $v: uint32x4x4_t = vld1q_u32_x4($ptr);
    };
    (i8, x1, $v:ident, $ptr:ident) => {
        let $v: int8x16_t = vld1q_s8($ptr);
    };
    (i8, x2, $v:ident, $ptr:ident) => {
        let $v: int8x16x2_t = vld1q_s8_x2($ptr);
    };
    (i8, x3, $v:ident, $ptr:ident) => {
        let $v: int8x16x3_t = vld1q_s8_x3($ptr);
    };
    (i8, x4, $v:ident, $ptr:ident) => {
        let $v: int8x16x4_t = vld1q_s8_x4($ptr);
    };
    (i16, x1, $v:ident, $ptr:ident) => {
        let $v: int16x8_t = vld1q_s16($ptr);
    };
    (i16, x2, $v:ident, $ptr:ident) => {
        let $v: int16x8x2_t = vld1q_s16_x2($ptr);
    };
    (i16, x3, $v:ident, $ptr:ident) => {
        let $v: int16x8x3_t = vld1q_s16_x3($ptr);
    };
    (i16, x4, $v:ident, $ptr:ident) => {
        let $v: int16x8x4_t = vld1q_s16_x4($ptr);
    };
    (i32, x1, $v:ident, $ptr:ident) => {
        let $v: int32x4_t = vld1q_s32($ptr);
    };
    (i32, x2, $v:ident, $ptr:ident) => {
        let $v: int32x4x2_t = vld1q_s32_x2($ptr);
    };
    (i32, x3, $v:ident, $ptr:ident) => {
        let $v: int32x4x3_t = vld1q_s32_x3($ptr);
    };
    (i32, x4, $v:ident, $ptr:ident) => {
        let $v: int32x4x4_t = vld1q_s32_x4($ptr);
    };
    (f32, x1, $v:ident, $ptr:ident) => {
        let $v: float32x4_t = vld1q_f32($ptr);
    };
    (f32, x2, $v:ident, $ptr:ident) => {
        let $v: float32x4x2_t = vld1q_f32_x2($ptr);
    };
    (f32, x3, $v:ident, $ptr:ident) => {
        let $v: float32x4x3_t = vld1q_f32_x3($ptr);
    };
    (f32, x4, $v:ident, $ptr:ident) => {
        let $v: float32x4x4_t = vld1q_f32_x4($ptr);
    };
    (f64, x1, $v:ident, $ptr:ident) => {
        let $v: float64x2_t = vld1q_f64($ptr);
    };
    (f64, x2, $v:ident, $ptr:ident) => {
        let $v: float64x2x2_t = vld1q_f64_x2($ptr);
    };
    (f64, x3, $v:ident, $ptr:ident) => {
        let $v: float64x2x3_t = vld1q_f64_x3($ptr);
    };
    (f64, x4, $v:ident, $ptr:ident) => {
        let $v: float64x2x4_t = vld1q_f64_x4($ptr);
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[rustfmt::skip]
macro_rules! vec_mul {
    (u8, x1, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let $v_res: uint8x16_t = vmulq_u8($v_lhs, $v_rhs);
    };
    (u8, x2, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint8x16_t = vmulq_u8($v_lhs.0, $v_rhs);
        let res_1: uint8x16_t = vmulq_u8($v_lhs.1, $v_rhs);
        let $v_res: uint8x16x2_t = uint8x16x2_t {
            0: res_0,
            1: res_1
        };
    };
    (u8, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint8x16_t = vmulq_u8($v_lhs.0, $v_rhs);
        let res_1: uint8x16_t = vmulq_u8($v_lhs.1, $v_rhs);
        let res_2: uint8x16_t = vmulq_u8($v_lhs.2, $v_rhs);
        let $v_res: uint8x16x3_t = uint8x16x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (u8, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint8x16_t = vmulq_u8($v_lhs.0, $v_rhs);
        let res_1: uint8x16_t = vmulq_u8($v_lhs.1, $v_rhs);
        let res_2: uint8x16_t = vmulq_u8($v_lhs.2, $v_rhs);
        let res_3: uint8x16_t = vmulq_u8($v_lhs.3, $v_rhs);

        let $v_res: uint8x16x4_t = uint8x16x4_t {
            0: res_0,
            1: res_1,
            2: res_2,
            3: res_3,
        };
    };
    (i8, x1, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let $v_res: int8x16_t = vmulq_s8($v_lhs, $v_rhs);
    };
    (i8, x2, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int8x16_t = vmulq_s8($v_lhs.0, $v_rhs);
        let res_1: int8x16_t = vmulq_s8($v_lhs.1, $v_rhs);
        let $v_res: int8x16x2_t = int8x16x2_t {
            0: res_0,
            1: res_1
        };
    };
    (i8, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int8x16_t = vmulq_s8($v_lhs.0, $v_rhs);
        let res_1: int8x16_t = vmulq_s8($v_lhs.1, $v_rhs);
        let res_2: int8x16_t = vmulq_s8($v_lhs.2, $v_rhs);
        let $v_res: int8x16x3_t = int8x16x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (i8, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int8x16_t = vmulq_s8($v_lhs.0, $v_rhs);
        let res_1: int8x16_t = vmulq_s8($v_lhs.1, $v_rhs);
        let res_2: int8x16_t = vmulq_s8($v_lhs.2, $v_rhs);
        let res_3: int8x16_t = vmulq_s8($v_lhs.3, $v_rhs);

        let $v_res: int8x16x4_t = int8x16x4_t {
            0: res_0,
            1: res_1,
            2: res_2,
            3: res_3,
        };
    };
    (u16, x1, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let $v_res: uint16x8_t = vmulq_u16($v_lhs, $v_rhs);
    };
    (u16, x2, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint16x8_t = vmulq_u16($v_lhs.0, $v_rhs);
        let res_1: uint16x8_t = vmulq_u16($v_lhs.1, $v_rhs);
        let $v_res: uint16x8x2_t = uint16x8x2_t {
            0: res_0,
            1: res_1
        };
    };
    (u16, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint16x8_t = vmulq_u16($v_lhs.0, $v_rhs);
        let res_1: uint16x8_t = vmulq_u16($v_lhs.1, $v_rhs);
        let res_2: uint16x8_t = vmulq_u16($v_lhs.2, $v_rhs);
        let $v_res: uint16x8x3_t = uint16x8x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (u16, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint16x8_t = vmulq_u16($v_lhs.0, $v_rhs);
        let res_1: uint16x8_t = vmulq_u16($v_lhs.1, $v_rhs);
        let res_2: uint16x8_t = vmulq_u16($v_lhs.2, $v_rhs);
        let res_3: uint16x8_t = vmulq_u16($v_lhs.3, $v_rhs);

        let $v_res: uint16x8x4_t = uint16x8x4_t {
            0: res_0,
            1: res_1,
            2: res_2,
            3: res_3,
        };
    };
    (i16, x1, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let $v_res: int16x8_t = vmulq_s16($v_lhs, $v_rhs);
    };
    (i16, x2, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int16x8_t = vmulq_s16($v_lhs.0, $v_rhs);
        let res_1: int16x8_t = vmulq_s16($v_lhs.1, $v_rhs);
        let $v_res: int16x8x2_t = int16x8x2_t {
            0: res_0,
            1: res_1
        };
    };
    (i16, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int16x8_t = vmulq_s16($v_lhs.0, $v_rhs);
        let res_1: int16x8_t = vmulq_s16($v_lhs.1, $v_rhs);
        let res_2: int16x8_t = vmulq_s16($v_lhs.2, $v_rhs);
        let $v_res: int16x8x3_t = int16x8x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (i16, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int16x8_t = vmulq_s16($v_lhs.0, $v_rhs);
        let res_1: int16x8_t = vmulq_s16($v_lhs.1, $v_rhs);
        let res_2: int16x8_t = vmulq_s16($v_lhs.2, $v_rhs);
        let res_3: int16x8_t = vmulq_s16($v_lhs.3, $v_rhs);

        let $v_res: int16x8x4_t = int16x8x4_t {
            0: res_0,
            1: res_1,
            2: res_2,
            3: res_3,
        };
    };
    (u32, x1, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let $v_res: uint32x4_t = vmulq_u32($v_lhs, $v_rhs);
    };
    (u32, x2, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint32x4_t = vmulq_u32($v_lhs.0, $v_rhs);
        let res_1: uint32x4_t = vmulq_u32($v_lhs.1, $v_rhs);
        let $v_res: uint32x4x2_t = uint32x4x2_t {
            0: res_0,
            1: res_1
        };
    };
    (u32, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint32x4_t = vmulq_u32($v_lhs.0, $v_rhs);
        let res_1: uint32x4_t = vmulq_u32($v_lhs.1, $v_rhs);
        let res_2: uint32x4_t = vmulq_u32($v_lhs.2, $v_rhs);
        let $v_res: uint32x4x3_t = uint32x4x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (u32, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint32x4_t = vmulq_u32($v_lhs.0, $v_rhs);
        let res_1: uint32x4_t = vmulq_u32($v_lhs.1, $v_rhs);
        let res_2: uint32x4_t = vmulq_u32($v_lhs.2, $v_rhs);
        let res_3: uint32x4_t = vmulq_u32($v_lhs.3, $v_rhs);

        let $v_res: uint32x4x4_t = uint32x4x4_t {
            0: res_0,
            1: res_1,
            2: res_2,
            3: res_3,
        };
    };

    (i32, x1, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let $v_res: int32x4_t = vmulq_s32($v_lhs, $v_rhs);
    };
    (i32, x2, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int32x4_t = vmulq_s32($v_lhs.0, $v_rhs);
        let res_1: int32x4_t = vmulq_s32($v_lhs.1, $v_rhs);
        let $v_res: int32x4x2_t = int32x4x2_t {
            0: res_0,
            1: res_1
        };
    };
    (i32, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int32x4_t = vmulq_s32($v_lhs.0, $v_rhs);
        let res_1: int32x4_t = vmulq_s32($v_lhs.1, $v_rhs);
        let res_2: int32x4_t = vmulq_s32($v_lhs.2, $v_rhs);
        let $v_res: int32x4x3_t = int32x4x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (i32, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int32x4_t = vmulq_s32($v_lhs.0, $v_rhs);
        let res_1: int32x4_t = vmulq_s32($v_lhs.1, $v_rhs);
        let res_2: int32x4_t = vmulq_s32($v_lhs.2, $v_rhs);
        let res_3: int32x4_t = vmulq_s32($v_lhs.3, $v_rhs);

        let $v_res: int32x4x4_t = int32x4x4_t {
            0: res_0,
            1: res_1,
            2: res_2,
            3: res_3,
        };
    };

    (f32, x1, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let $v_res: float32x4_t = vmulq_f32($v_lhs, $v_rhs);
    };
    (f32, x2, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: float32x4_t = vmulq_f32($v_lhs.0, $v_rhs);
        let res_1: float32x4_t = vmulq_f32($v_lhs.1, $v_rhs);
        let $v_res: float32x4x2_t = float32x4x2_t {
            0: res_0,
            1: res_1
        };
    };
    (f32, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: float32x4_t = vmulq_f32($v_lhs.0, $v_rhs);
        let res_1: float32x4_t = vmulq_f32($v_lhs.1, $v_rhs);
        let res_2: float32x4_t = vmulq_f32($v_lhs.2, $v_rhs);
        let $v_res: float32x4x3_t = float32x4x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (f32, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: float32x4_t = vmulq_f32($v_lhs.0, $v_rhs);
        let res_1: float32x4_t = vmulq_f32($v_lhs.1, $v_rhs);
        let res_2: float32x4_t = vmulq_f32($v_lhs.2, $v_rhs);
        let res_3: float32x4_t = vmulq_f32($v_lhs.3, $v_rhs);

        let $v_res: float32x4x4_t = float32x4x4_t {
            0: res_0,
            1: res_1,
            2: res_2,
            3: res_3,
        };
    };

    (f64, x1, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let $v_res: float64x2_t = vmulq_f64($v_lhs, $v_rhs);
    };
    (f64, x2, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: float64x2_t = vmulq_f64($v_lhs.0, $v_rhs);
        let res_1: float64x2_t = vmulq_f64($v_lhs.1, $v_rhs);
        let $v_res: float64x2x2_t = float64x2x2_t {
            0: res_0,
            1: res_1
        };
    };
    (f64, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: float64x2_t = vmulq_f64($v_lhs.0, $v_rhs);
        let res_1: float64x2_t = vmulq_f64($v_lhs.1, $v_rhs);
        let res_2: float64x2_t = vmulq_f64($v_lhs.2, $v_rhs);
        let $v_res: float64x2x3_t = float64x2x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (f64, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: float64x2_t = vmulq_f64($v_lhs.0, $v_rhs);
        let res_1: float64x2_t = vmulq_f64($v_lhs.1, $v_rhs);
        let res_2: float64x2_t = vmulq_f64($v_lhs.2, $v_rhs);
        let res_3: float64x2_t = vmulq_f64($v_lhs.3, $v_rhs);

        let $v_res: float64x2x4_t = float64x2x4_t {
            0: res_0,
            1: res_1,
            2: res_2,
            3: res_3,
        };
    };

}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vec_store {
    (u8, x1, $ptr:ident, $v_res:ident) => {
        vst1q_u8($ptr as *mut u8, $v_res);
    };
    (u8, x2, $ptr:ident, $v_res:ident) => {
        vst1q_u8_x2($ptr as *mut u8, $v_res);
    };
    (u8, x3, $ptr:ident, $v_res:ident) => {
        vst1q_u8_x3($ptr as *mut u8, $v_res);
    };
    (u8, x4, $ptr:ident, $v_res:ident) => {
        vst1q_u8_x4($ptr as *mut u8, $v_res);
    };
    (u16, x1, $ptr:ident, $v_res:ident) => {
        vst1q_u16($ptr as *mut u16, $v_res);
    };
    (u16, x2, $ptr:ident, $v_res:ident) => {
        vst1q_u16_x2($ptr as *mut u16, $v_res);
    };
    (u16, x3, $ptr:ident, $v_res:ident) => {
        vst1q_u16_x3($ptr as *mut u16, $v_res);
    };
    (u16, x4, $ptr:ident, $v_res:ident) => {
        vst1q_u16_x4($ptr as *mut u16, $v_res);
    };
    (u32, x1, $ptr:ident, $v_res:ident) => {
        vst1q_u32($ptr as *mut u32, $v_res);
    };
    (u32, x2, $ptr:ident, $v_res:ident) => {
        vst1q_u32_x2($ptr as *mut u32, $v_res);
    };
    (u32, x3, $ptr:ident, $v_res:ident) => {
        vst1q_u32_x3($ptr as *mut u32, $v_res);
    };
    (u32, x4, $ptr:ident, $v_res:ident) => {
        vst1q_u32_x4($ptr as *mut u32, $v_res);
    };
    (i8, x1, $ptr:ident, $v_res:ident) => {
        vst1q_s8($ptr as *mut i8, $v_res);
    };
    (i8, x2, $ptr:ident, $v_res:ident) => {
        vst1q_s8_x2($ptr as *mut i8, $v_res);
    };
    (i8, x3, $ptr:ident, $v_res:ident) => {
        vst1q_s8_x3($ptr as *mut i8, $v_res);
    };
    (i8, x4, $ptr:ident, $v_res:ident) => {
        vst1q_s8_x4($ptr as *mut i8, $v_res);
    };
    (i16, x1, $ptr:ident, $v_res:ident) => {
        vst1q_s16($ptr as *mut i16, $v_res);
    };
    (i16, x2, $ptr:ident, $v_res:ident) => {
        vst1q_s16_x2($ptr as *mut i16, $v_res);
    };
    (i16, x3, $ptr:ident, $v_res:ident) => {
        vst1q_s16_x3($ptr as *mut i16, $v_res);
    };
    (i16, x4, $ptr:ident, $v_res:ident) => {
        vst1q_s16_x4($ptr as *mut i16, $v_res);
    };
    (i32, x1, $ptr:ident, $v_res:ident) => {
        vst1q_s32($ptr as *mut i32, $v_res);
    };
    (i32, x2, $ptr:ident, $v_res:ident) => {
        vst1q_s32_x2($ptr as *mut i32, $v_res);
    };
    (i32, x3, $ptr:ident, $v_res:ident) => {
        vst1q_s32_x3($ptr as *mut i32, $v_res);
    };
    (i32, x4, $ptr:ident, $v_res:ident) => {
        vst1q_s32_x4($ptr as *mut i32, $v_res);
    };
    (f32, x1, $ptr:ident, $v_res:ident) => {
        vst1q_f32($ptr as *mut f32, $v_res);
    };
    (f32, x2, $ptr:ident, $v_res:ident) => {
        vst1q_f32_x2($ptr as *mut f32, $v_res);
    };
    (f32, x3, $ptr:ident, $v_res:ident) => {
        vst1q_f32_x3($ptr as *mut f32, $v_res);
    };
    (f32, x4, $ptr:ident, $v_res:ident) => {
        vst1q_f32_x4($ptr as *mut f32, $v_res);
    };
    (f64, x1, $ptr:ident, $v_res:ident) => {
        vst1q_f64($ptr as *mut f64, $v_res);
    };
    (f64, x2, $ptr:ident, $v_res:ident) => {
        vst1q_f64_x2($ptr as *mut f64, $v_res);
    };
    (f64, x3, $ptr:ident, $v_res:ident) => {
        vst1q_f64_x3($ptr as *mut f64, $v_res);
    };
    (f64, x4, $ptr:ident, $v_res:ident) => {
        vst1q_f64_x4($ptr as *mut f64, $v_res);
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vec_dup {
    (u8, $v_rhs:ident, $val:ident) => {
        let $v_rhs: uint8x16_t = vld1q_dup_u8(ptr::from_ref::<u8>(&$val));
    };
    (u16, $v_rhs:ident, $val:ident) => {
        let $v_rhs: uint16x8_t = vld1q_dup_u16(ptr::from_ref::<u16>(&$val));
    };
    (u32, $v_rhs:ident, $val:ident) => {
        let $v_rhs: uint32x4_t = vld1q_dup_u32(ptr::from_ref::<u32>(&$val));
    };
    (i8, $v_rhs:ident, $val:ident) => {
        let $v_rhs: int8x16_t = vld1q_dup_s8(ptr::from_ref::<i8>(&$val));
    };
    (i16, $v_rhs:ident, $val:ident) => {
        let $v_rhs: int16x8_t = vld1q_dup_s16(ptr::from_ref::<i16>(&$val));
    };
    (i32, $v_rhs:ident, $val:ident) => {
        let $v_rhs: int32x4_t = vld1q_dup_s32(ptr::from_ref::<i32>(&$val));
    };
    (f32, $v_rhs:ident, $val:ident) => {
        let $v_rhs: float32x4_t = vld1q_dup_f32(ptr::from_ref::<f32>(&$val));
    };
    (f64, $v_rhs:ident, $val:ident) => {
        let $v_rhs: float64x2_t = vld1q_dup_f64(ptr::from_ref::<f64>(&$val));
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vec_load_mul_store {
    ($t:ident, $x:ident, $ptr:ident, $v_rhs:ident) => {
        vec_load!($t, $x, v_lhs, $ptr);
        vec_mul!($t, $x, v_lhs, $v_rhs, v_res);
        vec_store!($t, $x, $ptr, v_res);
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! partial_vec_load_mul_store {
    ($t:ident, $ptr:ident, $v_rhs:ident, $pvec_sz:expr) => {
        let mut sv_buf = SimdVecBuffer::<$t>::neon_vec();
        sv_buf.load($ptr, $pvec_sz);
        let buf_ptr = sv_buf.buf;
        vec_load_mul_store!($t, x1, buf_ptr, $v_rhs);
        sv_buf.store($ptr as *mut $t);
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! impl_simd_operation_mul_assign_not_supported {
    ($t:ty) => {
        #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
        impl SimdOperation for $t {
            unsafe fn mul_assign(_ptr: *const $t, _len: usize, _val: $t) {
                panic!("SIMD mul_assign is not supported for $t");
            }
        }
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! impl_simd_operation_mul_assign {
    ($t:ident) => {
        unsafe fn mul_assign(ptr: *const $t, len: usize, val: $t) {
            let s = SimdMetaData::simd_neon::<$t>(len);
            vec_dup!($t, v_rhs, val);
            let mut idx: usize = 0;
            while idx < s.bat_f * s.bat_sz {
                let ptr_idx = ptr.add(idx);
                vec_load_mul_store!($t, x4, ptr_idx, v_rhs);
                idx += s.bat_sz;
            }

            if s.pbat_sz > 0 {
                let ptr_idx = ptr.add(idx);
                match s.pbat_sz {
                    1 => {
                        vec_load_mul_store!($t, x1, ptr_idx, v_rhs);
                        idx += s.vec_sz;
                    }
                    2 => {
                        vec_load_mul_store!($t, x2, ptr_idx, v_rhs);
                        idx += s.vec_sz * 2;
                    }
                    3 => {
                        vec_load_mul_store!($t, x3, ptr_idx, v_rhs);
                        idx += s.vec_sz * 2;
                    }
                    _ => {
                        panic!("invalid value for s.pbat_sz: {}", s.pbat_sz);
                    }
                }
            }
            if s.pvec_sz > 0 {
                let ptr_idx = ptr.add(idx);
                partial_vec_load_mul_store!($t, ptr_idx, v_rhs, s.pvec_sz);
            }
        }
    };
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for u8 {
    impl_simd_operation_mul_assign!(u8);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for u16 {
    impl_simd_operation_mul_assign!(u16);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for u32 {
    impl_simd_operation_mul_assign!(u32);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for i8 {
    impl_simd_operation_mul_assign!(i8);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for i16 {
    impl_simd_operation_mul_assign!(i16);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for i32 {
    impl_simd_operation_mul_assign!(i32);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for f32 {
    impl_simd_operation_mul_assign!(f32);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl SimdOperation for f64 {
    impl_simd_operation_mul_assign!(f64);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_mul_assign_not_supported!(u64);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_mul_assign_not_supported!(u128);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_mul_assign_not_supported!(i64);
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl_simd_operation_mul_assign_not_supported!(i128);

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) struct SimdNeonKernel<T: MatrixElement> {
    _phantom: PhantomData<T>,
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
impl<T> SimdNeonKernel<T>
where
    T: MatrixElement<Output = T> + SimdOperation,
{
    pub(in crate::matrix::simd) fn scale_row(m: &mut Matrix<T>, row: usize, val: T) {
        if m.is_transpose {
            unsafe {
                let ptr = cmd_ptr_t!(m.cmd, row, 0);
                let len = m.cmd.col_stride;
                T::mul_assign(ptr, len, val);
                m.sync_row(row, SyncDirection::CmdToRmd);
            }
        } else {
            unsafe {
                let ptr = rmd_ptr!(m.rmd, row, 0);
                let len = m.rmd.row_stride;
                T::mul_assign(ptr, len, val);
                m.sync_row(row, SyncDirection::RmdToCmd);
            }
        }
    }
}
