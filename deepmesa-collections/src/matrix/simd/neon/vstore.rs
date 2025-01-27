#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vstore_vst1q {
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
pub(in crate::matrix::simd) use vstore_vst1q;
