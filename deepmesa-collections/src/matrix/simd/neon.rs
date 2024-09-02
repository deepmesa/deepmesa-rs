//SIMD for arm64 Neon - simdneon. This doesn't support Arm SVE.
#![allow(unused_variables)]
#![allow(dead_code)]

use crate::matrix::matrix::Matrix;
use crate::matrix::traits::MatrixElement;
use crate::matrix::traits::NumericDataType;
//use std::arch::aarch64::*;
//use std::ptr;
const SIMD_NEON_VEC_SIZE_BYTES: usize = 16;
const SIMD_NEON_LOAD_SIZE_4: usize = 4;

// fn simd_vec_size(numeric_type: NumericDataType) -> usize {
//     match numeric_type {
//         NumericDataType::U8 => SIMD_NEON_VEC_SIZE_16,
//         NumericDataType::U16 => SIMD_NEON_VEC_SIZE_8,
//         NumericDataType::U32 => SIMD_NEON_VEC_SIZE_4,
//         NumericDataType::U64 => SIMD_NEON_VEC_SIZE_2,
//         NumericDataType::U128 => {
//             panic!("u128 data type is not supported on SIMD Neon");
//         }
//         NumericDataType::I8 => SIMD_NEON_VEC_SIZE_16,
//         NumericDataType::I16 => SIMD_NEON_VEC_SIZE_8,
//         NumericDataType::I32 => SIMD_NEON_VEC_SIZE_4,
//         NumericDataType::I64 => SIMD_NEON_VEC_SIZE_2,
//         NumericDataType::I128 => {
//             panic!("i128 data type is not supported on SIMD Neon");
//         }
//         NumericDataType::F32 => SIMD_NEON_VEC_SIZE_4,
//         NumericDataType::F64 => SIMD_NEON_VEC_SIZE_2,
//     }
// }

impl<T> Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    pub unsafe fn scale_row_simd_neon(&mut self, scalar: T, row: usize) {
        match T::numeric_type() {
            NumericDataType::U8 => self.scale_row_u8(scalar, row, self.cols()),
            NumericDataType::U16 => self.scale_row_u16(scalar, row),
            NumericDataType::U32 => self.scale_row_u32(scalar, row),
            NumericDataType::U64 => self.scale_row_u64(scalar, row),
            NumericDataType::U128 => {
                panic!("u128 data type is not supported on SIMD Neon");
            }
            NumericDataType::I8 => self.scale_row_i8(scalar, row),
            NumericDataType::I16 => self.scale_row_i16(scalar, row),
            NumericDataType::I32 => self.scale_row_i32(scalar, row),
            NumericDataType::I64 => self.scale_row_i64(scalar, row),
            NumericDataType::I128 => {
                panic!("i128 data type is not supported on SIMD Neon");
            }
            NumericDataType::F32 => self.scale_row_f32(scalar, row),
            NumericDataType::F64 => self.scale_row_f64(scalar, row),
        }

        // let step = simd_vec_size(T::numeric_type());
        // let iter = MatrixRowStepIterator::new(&self, row, step);
    }

    // pub fn scale_row_simd_neon(&mut self, row: usize, scalar: T) {
    //     println!("In scale_row_simd_neon");
    //     //chunk up the matrix row into 128 byte chunks
    //     // UNSIGNED
    //     // u8  = u8x8 (uint8x8_t) (8 1byte elems per vector - 64 bits) or u8x16 (uint8x16_t) (16 1byte elems per vector - 128 bits)
    //     // u16 = u16x4 (4 2byte elems per vector - 64 bits) or u16x8 (8 2byte elems per vector - 128 bits)
    //     // u32 = u32x2 (2 4byte elems per vector - 64 bits) or u32x4 (4 4byte elems per vector - 128 bits)
    //     // u64 = u64x1 (1 8byte elems per vector - 64 bits) or u64x2 (2 8byte elems per vector - 128 bits) // not useful
    //     // FLOATING POINT
    //     // f32 = f32x2 (2 4byte elems per vector - 64 bits) or u32x4 (4 4byte elems per vector - 128 bits)
    //     // f64 = f64x1 (1 8byte elems per vector - 64 bits) or u64x2 (2 8byte elems per vector - 128 bits) // not useful
    //     // SIGNED
    //     // i8  = u8x8 (8 1byte elems per vector - 64 bits) or u8x16 (16 1byte elems per vector - 128 bits)
    //     // i16 = u16x4 (4 2byte elems per vector - 64 bits) or u16x8 (8 2byte elems per vector - 128 bits)
    //     // i32 = u32x2 (2 4byte elems per vector - 64 bits) or u32x4 (4 4byte elems per vector - 128 bits)
    //     // i64 = u64x1 (1 8byte elems per vector - 64 bits) or u64x2 (2 8byte elems per vector - 128 bits) // not useful

    //     //        let vs = scalar.vec_size();
    //     if self.is_transpose {
    //         panic!("NOT IMPLEMENTED YET!");
    //     } else {
    //         //u8 -> step = 16
    //         //u16 -> step = 8
    //         //u32 -> step = 4
    //         //u64 -> step 2
    //         let iter = MatrixRowStepIterator::new(&self, row, step);
    //     }
    // }

    //TODO: Build a chunking iterator - takes a chunk size (in elements) and then returns slices of that size

    unsafe fn scale_row_u8(&mut self, scalar: T, row: usize, cols: usize) {
        // let start = row * cols;
        // let end = (row + 1) * cols;

        // let reg_s: uint8x16_t;
        // unsafe {
        //     reg_s = vld1q_dup_u8(ptr::from_ref::<T>(&scalar) as *const u8);
        //     //        reg_s = vld1q_dup_u8((&scalar).const_ptr() as *const u8);
        // }

        // //length of the data to get in elements:
        // //elements in a simd vec = (vec size bytes) / elem_size_bytes [16/1] = 16 elements
        // //SIMD_NEON_LOAD_SIZE = 4
        // let step = (SIMD_NEON_VEC_SIZE_BYTES / size_of::<T>()) * SIMD_NEON_LOAD_SIZE_4;

        // for idx in (start..end).step_by(step) {
        //     //            let reg_v: uint8x16x4_t;
        //     let chunk_p: *const T;
        //     let chunk_n: usize;
        //     let reg_v;
        //     (chunk_p, chunk_n) = self.chunk_ptr(idx, step);
        //     if chunk_n < step {
        //         //TODO: handle the case where n is less than step
        //     } else {
        //         reg_v = vld1q_u8_x4(chunk_p as *const u8);
        //     }
        //     //            reg_v = vld1q_u8_x4((&data[idx]).const_ptr() as *const u8);
        //     let st_src: uint8x16x4_t;
        //     let res_0: uint8x16_t = vmulq_u8(reg_v.0, reg_s);
        //     let res_1: uint8x16_t = vmulq_u8(reg_v.1, reg_s);
        //     let res_2: uint8x16_t = vmulq_u8(reg_v.2, reg_s);
        //     let res_3: uint8x16_t = vmulq_u8(reg_v.3, reg_s);

        //     // STORE
        //     st_src = uint8x16x4_t {
        //         0: res_0,
        //         1: res_1,
        //         2: res_2,
        //         3: res_3,
        //     };

        //     //Store
        //     vst1q_u8_x4(chunk_p as *mut u8, st_src);
        //     //            vst1q_u8_x4((&mut data[idx]).mut_ptr() as *mut u8, st_src);
        // }
        //    let p: *const u8 = scalar.as_ptr();
        println!("in scale row_u8");
    }

    unsafe fn scale_row_u16(&mut self, scalar: T, row: usize) {
        println!("in scale row_u16");
    }

    unsafe fn scale_row_u32(&mut self, scalar: T, row: usize) {
        println!("in scale row_u32");
    }

    unsafe fn scale_row_u64(&mut self, scalar: T, row: usize) {
        println!("in scale row_u64");
    }

    unsafe fn scale_row_i8(&mut self, scalar: T, row: usize) {
        println!("in scale row_u8");
    }

    unsafe fn scale_row_i16(&mut self, scalar: T, row: usize) {
        println!("in scale row_u16");
    }

    unsafe fn scale_row_i32(&mut self, scalar: T, row: usize) {
        println!("in scale row_u32");
    }

    unsafe fn scale_row_i64(&mut self, scalar: T, row: usize) {
        println!("in scale row_u64");
    }

    unsafe fn scale_row_f32(&mut self, scalar: T, row: usize) {
        println!("in scale row_u32");
    }

    unsafe fn scale_row_f64(&mut self, scalar: T, row: usize) {
        println!("in scale row_u64");
    }
}
