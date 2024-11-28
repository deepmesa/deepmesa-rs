use deepmesa_collections::matrix::vector::Vector;

pub trait OrdinaryLeastSquares {
    fn ols(&self) -> Vector<f64>;
}

pub trait GradientDescent {}
