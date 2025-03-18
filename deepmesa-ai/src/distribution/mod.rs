pub mod binomial;

pub trait Base {
    fn mean(&self) -> f64;
    fn median(&self) -> Option<f64>;
    fn mode(&self) -> Option<f64>;
}

pub trait Discrete: Base {
    fn pmf(&self) -> f64;
}

pub trait Continuous: Base {
    fn pdf(&self) -> f64;
}
