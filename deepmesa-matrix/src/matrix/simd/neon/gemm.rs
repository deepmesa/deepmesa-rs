//gemm

use crate::matrix::cmd::data::*;
use crate::matrix::cmd::macros::*;
use crate::matrix::rmd::data::*;
use crate::matrix::rmd::macros::*;
use crate::matrix::simd::metadata::SimdMetaData;
use crate::matrix::traits::*;
use core::arch::aarch64::*;

pub fn run_code() {
    unsafe { impl_gemm() }
}

pub unsafe fn impl_gemm() {
    // let rows_ma = 2;
    // let cols_ma = 4;
    // let rows_mb = 4;
    // let cols_mb = 2;

    // let ma = row_major_dataset!([f32, 2, 8, true], 2, 3, 4, 5, 6, 7, 8, 9 ; 10, 11, 12, 13, 14, 15, 16, 17);
    // let mb = row_major_dataset!([f32, 8, 2, true], 3, 4; 5, 6; 7, 8; 9, 10; 11, 12; 13, 14; 15, 16; 17, 18);

    let ma = row_major_dataset!([f32, 2, 4, true], 2, 3, 4, 5; 10, 11, 12, 13);
    let mb = row_major_dataset!([f32, 4, 2, true], 3, 4; 5, 6; 7, 8; 9, 10);
    dbg!(&ma);
    dbg!(&mb);

    let mut ptr_a = ma.rm_data;
    let ptr_b = mb.rm_data;

    for i in 0..ma.rows {
        ptr_a = ptr_a.add(i * ma.row_stride);
        let s = SimdMetaData::simd_neon::<f32>(ma.cols);
        dbg!(&s);
        let mut idx: usize = 0;
        while idx < s.bat_f * s.bat_sz * s.vec_sz {
            dbg!(idx);
            idx += s.vec_sz * s.bat_sz;
        }

        if s.pbat_sz > 0 {
            match s.pbat_sz {
                1 => {
                    debug_assert!(mb.row_stride == s.vec_sz); // assert that the col stride of mb = vec size
                    let a1 = vld1q_f32(ptr_a.add(idx));
                    let mut c1: float32x4_t = vmovq_n_f32(0.);
                    let mut b1 = vld1q_f32(ptr_b.add(idx));
                    c1 = vfmaq_laneq_f32(c1, b1, a1, 0);

                    b1 = vld1q_f32(ptr_b.add(idx + s.vec_sz)); //increment ptr_b 0+(1*4)
                    c1 = vfmaq_laneq_f32(c1, b1, a1, 1); //increment the lane 1, 1+4, 1+8, etc

                    b1 = vld1q_f32(ptr_b.add(idx + (2 * s.vec_sz))); //increment ptr_b 0+(2*4)
                    c1 = vfmaq_laneq_f32(c1, b1, a1, 2); //increment the lane 2, 2+4, 2+8, etc

                    b1 = vld1q_f32(ptr_b.add(idx + (3 * s.vec_sz))); //increment ptr_b 0+(3*4)
                    c1 = vfmaq_laneq_f32(c1, b1, a1, 3); //increment the lane 3, 3+4, 3+8, etc
                    dbg!(&c1);
                    idx += s.vec_sz;
                }
                2 => {
                    idx += s.vec_sz * 2;
                }
                3 => {
                    idx += s.vec_sz * 3;
                }
                _ => {
                    panic!("invalid value for s.pbat_sz: {}", s.pbat_sz);
                }
            }
        }

        if s.pvec_sz > 0 {}
    }
}

unsafe fn do_gemm_lane() {
    let ma = row_major_dataset!([f32, 4, 4, false], 2, 3, 4, 5; 6, 7, 8, 9; 10, 11, 12, 13; 14, 15, 16, 17);
    let a: *const f32 = ma.rm_data;
    let a1 = vld1q_f32(a);
    //    println!("a1 = {:?}", a1);

    let mb =
        row_major_dataset!([f32, 4, 4, false], 20,24,28,32;21,25,29,33;22,26,30,34;23,27,31,35);
    let b: *const f32 = mb.rm_data;

    let a1 = vld1q_f32(a);
    let mut b1 = vld1q_f32(b); //increment ptr_b 0+(0*4)
    let mut c1: float32x4_t = vmovq_n_f32(0.);
    c1 = vfmaq_laneq_f32(c1, b1, a1, 0); //increment the lane 0, 0+(1*4), 0+(2*4), etc
    println!("a1 = {:?}", a1);
    println!("b1 = {:?}", b1);
    println!("c1 = {:?}\n", c1);

    b1 = vld1q_f32(b.add(4)); //increment ptr_b 0+(1*4)
    c1 = vfmaq_laneq_f32(c1, b1, a1, 1); //increment the lane 1, 1+4, 1+8, etc
    println!("a1 = {:?}", a1);
    println!("b1 = {:?}", b1);
    println!("c1 = {:?}\n", c1);

    b1 = vld1q_f32(b.add(8)); //increment ptr_b 0+(2*4)
    c1 = vfmaq_laneq_f32(c1, b1, a1, 2); //increment the lane 2, 2+4, 2+8, etc
    println!("a1 = {:?}", a1);
    println!("b1 = {:?}", b1);
    println!("c1 = {:?}\n", c1);

    b1 = vld1q_f32(b.add(12)); //increment ptr_b 0+(3*4)
    c1 = vfmaq_laneq_f32(c1, b1, a1, 3); //increment the lane 3, 3+4, 3+8, etc
    println!("a1 = {:?}", a1);
    println!("b1 = {:?}", b1);
    println!("c1 = {:?}\n", c1);
}

unsafe fn do_gemm() {
    let m = 4;
    let n = 4;
    let k = 4;

    // a = m x k matrix
    // b = k x n matrix
    let ma = row_major_dataset!([f32, 4, 4, false], 2, 3, 4, 5; 6, 7, 8, 9; 10, 11, 12, 13; 14, 15, 16, 17);
    let a: *const f32 = ma.rm_data;
    let a1 = vld1q_f32(a);
    //    println!("a1 = {:?}", a1);

    let mb =
        row_major_dataset!([f32, 4, 4, false], 20,24,28,32;21,25,29,33;22,26,30,34;23,27,31,35);
    let b: *const f32 = mb.rm_data;

    let mut c1: float32x4_t = vmovq_n_f32(0.);

    let a00 = vmovq_n_f32(2.0);
    let mut b1 = vld1q_f32(b);
    c1 = vfmaq_f32(c1, a00, b1);
    println!("a00 = {:?}", a00);
    println!("b1 = {:?}", b1);
    println!("c1 = {:?}\n", c1);

    let a01 = vmovq_n_f32(3.0);
    b1 = vld1q_f32(b.add(4));
    c1 = vfmaq_f32(c1, a01, b1);
    println!("a01 = {:?}", a01);
    println!("b1 = {:?}", b1);
    println!("c1 = {:?}\n", c1);

    let a02 = vmovq_n_f32(4.0);
    b1 = vld1q_f32(b.add(8));
    c1 = vfmaq_f32(c1, a02, b1);
    println!("a02 = {:?}", a02);
    println!("b1 = {:?}", b1);
    println!("c1 = {:?}\n", c1);

    let a03 = vmovq_n_f32(5.0);
    b1 = vld1q_f32(b.add(12));
    c1 = vfmaq_f32(c1, a03, b1);
    println!("a03 = {:?}", a03);
    println!("b1 = {:?}", b1);
    println!("c1 = {:?}\n", c1);

    // let mut ab11 = [vmovq_n_f32(0.); 4];
    // ab11[0] = vfmaq_laneq_f32(ab11[0], b1, a1, 0);
    // ab11[1] = vfmaq_laneq_f32(ab11[1], b1, a1, 1);
    // ab11[2] = vfmaq_laneq_f32(ab11[2], b1, a1, 2);
    // ab11[3] = vfmaq_laneq_f32(ab11[3], b1, a1, 3);
    // println!("ab11: {:?}", ab11);

    //    let b1 = vld1q_f32(b);

    //    println!("ab11: {:?}", ab11);
}

#[cfg(test)]
mod tests {

    use super::*;
    #[test]
    fn test_gemm() {
        unsafe { do_gemm_lane() }
    }
}

// print!("b: ");
// for i in 0..mb.cm_len {
//     unsafe {
//         let ptr: *const f32 = b.add(i);
//         print!("{:?},", *ptr);
//     }
// }
// println!();
