#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
#[rustfmt::skip]
macro_rules! vmul_vmulqxn {
    (u8, x1, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let $v_res: uint8x16_t = vmulq_u8($v_lhs, $v_rhs);
    };
    (u8, x2, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint8x16_t = vmulq_u8($v_lhs.0, $v_rhs.0);
        let res_1: uint8x16_t = vmulq_u8($v_lhs.1, $v_rhs.1);
        let $v_res: uint8x16x2_t = uint8x16x2_t {
            0: res_0,
            1: res_1
        };
    };
    (u8, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint8x16_t = vmulq_u8($v_lhs.0, $v_rhs.0);
        let res_1: uint8x16_t = vmulq_u8($v_lhs.1, $v_rhs.1);
        let res_2: uint8x16_t = vmulq_u8($v_lhs.2, $v_rhs.2);
        let $v_res: uint8x16x3_t = uint8x16x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (u8, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint8x16_t = vmulq_u8($v_lhs.0, $v_rhs.0);
        let res_1: uint8x16_t = vmulq_u8($v_lhs.1, $v_rhs.1);
        let res_2: uint8x16_t = vmulq_u8($v_lhs.2, $v_rhs.2);
        let res_3: uint8x16_t = vmulq_u8($v_lhs.3, $v_rhs.3);

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
        let res_0: int8x16_t = vmulq_s8($v_lhs.0, $v_rhs.0);
        let res_1: int8x16_t = vmulq_s8($v_lhs.1, $v_rhs.1);
        let $v_res: int8x16x2_t = int8x16x2_t {
            0: res_0,
            1: res_1
        };
    };
    (i8, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int8x16_t = vmulq_s8($v_lhs.0, $v_rhs.0);
        let res_1: int8x16_t = vmulq_s8($v_lhs.1, $v_rhs.1);
        let res_2: int8x16_t = vmulq_s8($v_lhs.2, $v_rhs.2);
        let $v_res: int8x16x3_t = int8x16x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (i8, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int8x16_t = vmulq_s8($v_lhs.0, $v_rhs.0);
        let res_1: int8x16_t = vmulq_s8($v_lhs.1, $v_rhs.1);
        let res_2: int8x16_t = vmulq_s8($v_lhs.2, $v_rhs.2);
        let res_3: int8x16_t = vmulq_s8($v_lhs.3, $v_rhs.3);

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
        let res_0: uint16x8_t = vmulq_u16($v_lhs.0, $v_rhs.0);
        let res_1: uint16x8_t = vmulq_u16($v_lhs.1, $v_rhs.1);
        let $v_res: uint16x8x2_t = uint16x8x2_t {
            0: res_0,
            1: res_1
        };
    };
    (u16, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint16x8_t = vmulq_u16($v_lhs.0, $v_rhs.0);
        let res_1: uint16x8_t = vmulq_u16($v_lhs.1, $v_rhs.1);
        let res_2: uint16x8_t = vmulq_u16($v_lhs.2, $v_rhs.2);
        let $v_res: uint16x8x3_t = uint16x8x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (u16, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint16x8_t = vmulq_u16($v_lhs.0, $v_rhs.0);
        let res_1: uint16x8_t = vmulq_u16($v_lhs.1, $v_rhs.1);
        let res_2: uint16x8_t = vmulq_u16($v_lhs.2, $v_rhs.2);
        let res_3: uint16x8_t = vmulq_u16($v_lhs.3, $v_rhs.3);

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
        let res_0: int16x8_t = vmulq_s16($v_lhs.0, $v_rhs.0);
        let res_1: int16x8_t = vmulq_s16($v_lhs.1, $v_rhs.1);
        let $v_res: int16x8x2_t = int16x8x2_t {
            0: res_0,
            1: res_1
        };
    };
    (i16, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int16x8_t = vmulq_s16($v_lhs.0, $v_rhs.0);
        let res_1: int16x8_t = vmulq_s16($v_lhs.1, $v_rhs.1);
        let res_2: int16x8_t = vmulq_s16($v_lhs.2, $v_rhs.2);
        let $v_res: int16x8x3_t = int16x8x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (i16, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int16x8_t = vmulq_s16($v_lhs.0, $v_rhs.0);
        let res_1: int16x8_t = vmulq_s16($v_lhs.1, $v_rhs.1);
        let res_2: int16x8_t = vmulq_s16($v_lhs.2, $v_rhs.2);
        let res_3: int16x8_t = vmulq_s16($v_lhs.3, $v_rhs.3);

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
        let res_0: uint32x4_t = vmulq_u32($v_lhs.0, $v_rhs.0);
        let res_1: uint32x4_t = vmulq_u32($v_lhs.1, $v_rhs.1);
        let $v_res: uint32x4x2_t = uint32x4x2_t {
            0: res_0,
            1: res_1
        };
    };
    (u32, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint32x4_t = vmulq_u32($v_lhs.0, $v_rhs.0);
        let res_1: uint32x4_t = vmulq_u32($v_lhs.1, $v_rhs.1);
        let res_2: uint32x4_t = vmulq_u32($v_lhs.2, $v_rhs.2);
        let $v_res: uint32x4x3_t = uint32x4x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (u32, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: uint32x4_t = vmulq_u32($v_lhs.0, $v_rhs.0);
        let res_1: uint32x4_t = vmulq_u32($v_lhs.1, $v_rhs.1);
        let res_2: uint32x4_t = vmulq_u32($v_lhs.2, $v_rhs.2);
        let res_3: uint32x4_t = vmulq_u32($v_lhs.3, $v_rhs.3);

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
        let res_0: int32x4_t = vmulq_s32($v_lhs.0, $v_rhs.0);
        let res_1: int32x4_t = vmulq_s32($v_lhs.1, $v_rhs.1);
        let $v_res: int32x4x2_t = int32x4x2_t {
            0: res_0,
            1: res_1
        };
    };
    (i32, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int32x4_t = vmulq_s32($v_lhs.0, $v_rhs.0);
        let res_1: int32x4_t = vmulq_s32($v_lhs.1, $v_rhs.1);
        let res_2: int32x4_t = vmulq_s32($v_lhs.2, $v_rhs.2);
        let $v_res: int32x4x3_t = int32x4x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (i32, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: int32x4_t = vmulq_s32($v_lhs.0, $v_rhs.0);
        let res_1: int32x4_t = vmulq_s32($v_lhs.1, $v_rhs.1);
        let res_2: int32x4_t = vmulq_s32($v_lhs.2, $v_rhs.2);
        let res_3: int32x4_t = vmulq_s32($v_lhs.3, $v_rhs.3);

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
        let res_0: float32x4_t = vmulq_f32($v_lhs.0, $v_rhs.0);
        let res_1: float32x4_t = vmulq_f32($v_lhs.1, $v_rhs.1);
        let $v_res: float32x4x2_t = float32x4x2_t {
            0: res_0,
            1: res_1
        };
    };
    (f32, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: float32x4_t = vmulq_f32($v_lhs.0, $v_rhs.0);
        let res_1: float32x4_t = vmulq_f32($v_lhs.1, $v_rhs.1);
        let res_2: float32x4_t = vmulq_f32($v_lhs.2, $v_rhs.2);
        let $v_res: float32x4x3_t = float32x4x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (f32, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: float32x4_t = vmulq_f32($v_lhs.0, $v_rhs.0);
        let res_1: float32x4_t = vmulq_f32($v_lhs.1, $v_rhs.1);
        let res_2: float32x4_t = vmulq_f32($v_lhs.2, $v_rhs.2);
        let res_3: float32x4_t = vmulq_f32($v_lhs.3, $v_rhs.3);

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
        let res_0: float64x2_t = vmulq_f64($v_lhs.0, $v_rhs.0);
        let res_1: float64x2_t = vmulq_f64($v_lhs.1, $v_rhs.1);
        let $v_res: float64x2x2_t = float64x2x2_t {
            0: res_0,
            1: res_1
        };
    };
    (f64, x3, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: float64x2_t = vmulq_f64($v_lhs.0, $v_rhs.0);
        let res_1: float64x2_t = vmulq_f64($v_lhs.1, $v_rhs.1);
        let res_2: float64x2_t = vmulq_f64($v_lhs.2, $v_rhs.2);
        let $v_res: float64x2x3_t = float64x2x3_t {
            0: res_0,
            1: res_1,
            2: res_2,
        };
    };
    (f64, x4, $v_lhs:ident, $v_rhs:ident, $v_res:ident) => {
        let res_0: float64x2_t = vmulq_f64($v_lhs.0, $v_rhs.0);
        let res_1: float64x2_t = vmulq_f64($v_lhs.1, $v_rhs.1);
        let res_2: float64x2_t = vmulq_f64($v_lhs.2, $v_rhs.2);
        let res_3: float64x2_t = vmulq_f64($v_lhs.3, $v_rhs.3);

        let $v_res: float64x2x4_t = float64x2x4_t {
            0: res_0,
            1: res_1,
            2: res_2,
            3: res_3,
        };
    };

}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) use vmul_vmulqxn;
