use crate::matrix::{
    rmd::data::RowMajorDataset, simd::traits::SimdAddAssign, traits::MatrixElement,
};

impl<T> SimdAddAssign<T> for RowMajorDataset<T>
where
    T: MatrixElement,
{
    fn simd_add_assign(&mut self, val: T) {
        // Approach 1: Add row * len to ptr
        // let len = self.row_stride;
        // unsafe {
        //     let ptr = self.rm_data;
        //     for row in 0..self.rows {
        //         T::add_assign(ptr.add(row * len), len, val);
        //         println!("RMD IN SIMD_ADD_ASSIGN: {:?}", self);
        //     }
        // }

        // Approach 2: Alternative code keeps increasing adding len
        // let len = self.row_stride;
        // unsafe {
        //     let mut ptr = self.rm_data;
        //     for _ in 0..self.rows {
        //         T::add_assign(ptr, len, val);
        //         println!("RMD IN SIMD_ADD_ASSIGN: {:?}", self);
        //         ptr = ptr.add(len);
        //     }
        // }

        //Approach 3: Pass in the ptr and the full lengh
        unsafe {
            let ptr = self.rm_data;
            let len = self.rm_len;
            T::add_assign(ptr, len, val);
            println!("RMD IN SIMD_ADD_ASSIGN: {:?}", self);
        }

        //Final assessment: The alg accepts a ptr and a length and
        // uses SIMD to iterate over that len starting at that ptr and
        // mutates the slice
    }
}
