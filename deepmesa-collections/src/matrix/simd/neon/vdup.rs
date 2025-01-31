#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
macro_rules! vdup_vld1q_dup {
    (u8, $v_rhs:ident, $val:ident) => {
        let $v_rhs: uint8x16_t = vld1q_dup_u8(ptr::from_ref::<u8>(&$val));
        println!("DUP: {:?}", $v_rhs);
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

// #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
// macro_rules! vdup_vld1q_lane {
//     (u8, $v_rhs:ident, $val:ident, $lanes:ident) => {
//         let $v_rhs: uint8x16_t = vld1q_lane_u8(ptr::from_ref::<u8>(&$val));
//     };
//     (u16, $v_rhs:ident, $val:ident) => {
//         let $v_rhs: uint16x8_t = vld1q_dup_u16(ptr::from_ref::<u16>(&$val));
//     };
//     (u32, $v_rhs:ident, $val:ident) => {
//         let $v_rhs: uint32x4_t = vld1q_dup_u32(ptr::from_ref::<u32>(&$val));
//     };
//     (i8, $v_rhs:ident, $val:ident) => {
//         let $v_rhs: int8x16_t = vld1q_dup_s8(ptr::from_ref::<i8>(&$val));
//     };
//     (i16, $v_rhs:ident, $val:ident) => {
//         let $v_rhs: int16x8_t = vld1q_dup_s16(ptr::from_ref::<i16>(&$val));
//     };
//     (i32, $v_rhs:ident, $val:ident) => {
//         let $v_rhs: int32x4_t = vld1q_dup_s32(ptr::from_ref::<i32>(&$val));
//     };
//     (f32, $v_rhs:ident, $val:ident) => {
//         let $v_rhs: float32x4_t = vld1q_dup_f32(ptr::from_ref::<f32>(&$val));
//     };
//     (f64, $v_rhs:ident, $val:ident) => {
//         let $v_rhs: float64x2_t = vld1q_dup_f64(ptr::from_ref::<f64>(&$val));
//     };
// }

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub(in crate::matrix::simd) use vdup_vld1q_dup;
