use crate::regression::traits::OrdinaryLeastSquares;
use deepmesa_collections::matrix::traits::MatrixElement;
use deepmesa_collections::matrix::vector::Vector;
use deepmesa_collections::matrix::vector::VectorType;

pub struct SimpleLinearModel<'a, T>
where
    T: MatrixElement<Output = T>,
{
    y: &'a Vector<T>,
    x: &'a Vector<T>,
    n: usize,
}

impl<'a, T> SimpleLinearModel<'a, T>
where
    T: MatrixElement<Output = T>,
{
    pub fn new(y: &'a Vector<T>, x: &'a Vector<T>) -> SimpleLinearModel<'a, T> {
        if y.len() != x.len() {
            //TODO return a better error message
            panic!("Invalid linear model. Dimensions of x&y are incorrect");
        }
        let n = y.len();
        return SimpleLinearModel { y, x, n };
    }
}

impl<'a, T> OrdinaryLeastSquares for SimpleLinearModel<'a, T>
where
    T: MatrixElement<Output = T> + std::ops::Mul<Output = T> + std::ops::AddAssign,
{
    fn ols(&self) -> Vector<f64> {
        let sig_xy = self.y.dot(&self.x).to_f64();
        let sig_x = self.x.sum().to_f64();
        let sig_y = self.y.sum().to_f64();
        let vec_xsq = self.x.power(2);
        let sig_vec_xsq = vec_xsq.sum().to_f64();
        let sig_xsq = sig_x.power(2).to_f64();

        let slope = (self.n as f64 * sig_xy.to_f64() - (sig_x * sig_y))
            / ((self.n as f64 * sig_vec_xsq) - sig_xsq);
        let intercept = (sig_y - (slope * sig_x)) / self.n as f64;

        let mut result = Vector::<f64>::new(2, VectorType::ColVector, false);
        result.set(0, intercept);
        result.set(1, slope);
        return result;
    }
}

#[cfg(test)]
mod tests {
    use super::{OrdinaryLeastSquares, SimpleLinearModel, Vector};

    #[test]
    fn test_simple_ols() {
        let x: Vector<u32> = Vector::<u32>::col_vector(&vec![2, 3, 5, 7, 9], false);
        let y: Vector<u32> = Vector::<u32>::col_vector(&vec![4, 5, 7, 10, 15], false);

        let slm = SimpleLinearModel::new(&y, &x);
        let b: Vector<f64> = slm.ols();
        println!("Vector: {:?}", b);
        println!("Slope: {}, Intercept: {}", b.get(0), b.get(1));
    }
}
