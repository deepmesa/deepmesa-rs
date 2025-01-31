use crate::matrix::matrix::Matrix;
use crate::matrix::simd::traits::SimdAddAssign;
use crate::matrix::traits::MatrixElement;

impl<T> SimdAddAssign<T> for Matrix<T>
where
    T: MatrixElement<Output = T>,
{
    fn simd_add_assign(&mut self, val: T) {
        // match self.m_type {
        //     MatrixType::ColMajor(ds) => {
        //         //                ds.simd_add_assign(rhs);
        //     }
        //     MatrixType::RowMajor => {
        //         println!("Running simd_add_assign!");
        //         self.rmd.simd_add_assign(val);
        //     }
        //     MatrixType::DualIndex => {
        //         //                self.did.simd_add_assign(rhs);
        //     }
        //        }
    }
}

#[cfg(test)]
mod tests {
    use std::ops::AddAssign;

    use crate::matrix::matrix::Matrix;
    use crate::matrix::matrix::MatrixType;
    use crate::matrix::traits::*;

    #[test]
    fn test_foo() {
        let mut m = Matrix::<u8>::new(2, 3, MatrixType::RowMajor, true);
        m.fill_row(0, &[1, 2, 3][..]);
        m.fill_row(1, &[4, 5, 6][..]);
        println!("M={:?}", &m);
        println!("SIMD Enabled: {:?}", m.is_simd_enabled());
        m.add_assign(3);
        println!("M={:?}", &m);
        println!("rmd = {:?}", &m.rmd);
    }
}
