//gemm

use crate::matrix::cmd::data::*;
use crate::matrix::cmd::macros::*;
use crate::matrix::rmd::data::*;
use crate::matrix::rmd::macros::*;
use crate::matrix::simd::metadata::SimdMetaData;
use crate::matrix::traits::*;
use core::arch::aarch64::*;

//Given a ptr_a and a ptr_b and tile dimensions load up the tiles and
// do the math using SIMD intrinsics
use crate::matrix::simd::neon::SIMD_NEON_LOAD_SIZE_4;
use crate::matrix::simd::neon::SIMD_NEON_VEC_SIZE_BYTES;
use crate::matrix::traits::FillRow;
use std::marker::PhantomData;

use std::fmt;
use std::fmt::Debug;
use std::fmt::Formatter;

pub struct Tile<T: MatrixElement> {
    pub vec_sz: usize,
    pub batch_sz: usize,
    pub ptr_a: *const T,
    pub ptr_b: *const T,
    pub rows_a: usize,
    pub cols_a: usize,

    //Reconcile between actual columns with data vs simd optimized
    // blank columns
    pub rows_b: usize,
    pub cols_b: usize,
    //Width of a and height of b
    //Cols in A == Rows of b
    pub tile_rows: usize,
    pub tile_cols: usize,
    pub tile_width: usize,
}

// Maybe what we need is a tile struct that takes in an RMD and
// produces tiles.

impl<T: MatrixElement> Tile<T> {
    fn new(
        ptr_a: *const T,
        rows_a: usize,
        cols_a: usize,
        ptr_b: *const T,
        rows_b: usize,
        cols_b: usize,
        tile_rows: usize,
        tile_cols: usize,
        tile_width: usize,
    ) -> Tile<T> {
        let vec_sz = SIMD_NEON_VEC_SIZE_BYTES / size_of::<T>();
        if tile_width % vec_sz != 0 {
            panic!(
                "Width ({:?}) must be a multiple of vec_sz = {:?}",
                tile_width, vec_sz
            );
        }

        if tile_width > vec_sz * SIMD_NEON_LOAD_SIZE_4 {
            panic!(
                "Width ({:?}) cannot be greater than {:?}",
                tile_width,
                vec_sz * 4
            );
        }
        if tile_cols % vec_sz != 0 {
            panic!(
                "tile_cols ({:?}) must be a multiple of vec_sz = {:?}",
                tile_cols, vec_sz
            );
        }

        if tile_cols > vec_sz * SIMD_NEON_LOAD_SIZE_4 {
            panic!(
                "tile_cols ({:?}) cannot be greater than {:?}",
                tile_cols, vec_sz
            );
        }

        debug_assert!(tile_rows <= rows_a);
        debug_assert!(tile_cols <= cols_b);

        return Tile {
            vec_sz: vec_sz,
            batch_sz: SIMD_NEON_LOAD_SIZE_4,
            ptr_a: ptr_a,
            ptr_b: ptr_b,
            rows_a: rows_a,
            cols_a: cols_a,
            rows_b: rows_b,
            cols_b: cols_b,
            tile_rows: tile_rows,
            tile_cols: tile_cols,
            tile_width: tile_width,
        };
    }

    pub unsafe fn print(&self) {
        let w_min = std::cmp::min(self.vec_sz, self.cols_a);
        let t_c_min = std::cmp::min(self.vec_sz, self.cols_b);

        let w_max = std::cmp::min(self.vec_sz * self.batch_sz, self.cols_a);
        let t_c_max = std::cmp::min(self.vec_sz * self.batch_sz, self.cols_b);

        println!(
            "self.vec_sz={:?}, cols_a={:?}, cols_b={:?}, w_min={:?}, t_c_min={:?}, w_max={:?}, t_c_max={:?}",
            self.vec_sz, self.cols_a, self.cols_b, w_min, t_c_min, w_max, t_c_max,
        );

        println!("Tile A:");
        for i in 0..self.tile_rows {
            for j in 0..self.tile_width {
                print!("{:?}, ", *self.ptr_a.add(i * self.cols_a + j));
            }
            println!();
        }

        println!("Tile B:");
        for i in 0..self.tile_rows {
            for j in 0..self.tile_cols {
                print!("{:?}, ", *self.ptr_b.add(i * self.cols_b + j));
            }
            println!();
        }
    }

    pub unsafe fn run(&self) {
        for i in 0..self.rows_a {
            let vec_a = vld1q_f64(self.ptr_a.add(i * self.tile_width) as *const f64);
            println!("a[{:?}]->: {:?}", i, vec_a);
        }
    }
}

pub fn make_rmd(rows: usize, cols: usize) -> RowMajorDataset<f64> {
    let mut rmd = RowMajorDataset::<f64>::new(rows, cols, true, true);
    let mut val: f64 = 2.0;
    for i in 0..rows {
        rmd.fill_row(i, val);
        val += 1.0;
    }
    return rmd;
}

pub fn run_code() {
    let ma = row_major_dataset!([f64, 4, 4, true], 2,4,6,8;10,12,14,16;18,20,22,24;26,28,30,32);
    let mb = row_major_dataset!([f64, 4, 4, true], 1,3,5,7;9,11,13,15;17,19,21,23;25,27,29,31);
    //    let mb = row_major_dataset!([f32, 8, 16, true], 4;5;6;7;8;9;10;11);

    dbg!(&ma);
    dbg!(&mb);
    println!();

    unsafe {
        let t = Tile::new(
            ma.rm_data.add(2),
            ma.rows,
            ma.cols,
            mb.rm_data.add(8),
            mb.rows,
            mb.cols,
            2,
            2,
            2,
        );

        t.print();
    }
    //    unsafe { impl_gemm() }
}

pub unsafe fn impl_gemm() {
    // let rows_ma = 2;
    // let cols_ma = 4;
    // let rows_mb = 4;
    // let cols_mb = 2;

    // let ma = row_major_dataset!([f32, 2, 8, true], 2, 3, 4, 5, 6, 7, 8, 9 ; 10, 11, 12, 13, 14, 15, 16, 17);
    // let mb = row_major_dataset!([f32, 8, 2, true], 3, 4; 5, 6; 7, 8; 9, 10; 11, 12; 13, 14; 15, 16; 17, 18);

    //Phase 2:
    //Lets multiply a=2x32 and b=32x8; Result = c=2x8 -

    //Phase 1:
    //Lets mutiply a=2x4 and b = 4x8; result = c=2x8

    let ma = row_major_dataset!([f32, 2, 4, true], 2, 3, 4, 5; 10, 11, 12, 13);
    let mb = row_major_dataset!([f32, 4, 8, true], 1, 2, 3, 4, 5, 6, 7, 8; 9, 10, 11, 12, 13, 14, 15, 16; 1, 2, 3, 4, 5, 6, 7, 8; 9, 10, 11, 12, 13, 14, 15, 16);
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
                    println!(
                        "Cols of B = {:?}, loops = {:?}",
                        mb.cols,
                        mb.cols / s.vec_sz
                    );
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
                    println!("Populating row={:?}", i);
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
