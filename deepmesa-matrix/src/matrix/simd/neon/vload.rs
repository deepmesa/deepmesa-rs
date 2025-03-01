#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vload_vld1q {
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
pub(in crate::matrix::simd) use vload_vld1q;
