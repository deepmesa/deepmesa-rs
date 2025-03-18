use crate::distribution::Base;
use crate::distribution::Discrete;
use deepmesa_common::errors::DeepMesaError;
use deepmesa_common::errors::INVALID_VALUE_ERROR;

#[derive(Debug, Clone)]
pub struct Binomial {
    //Number of successes in a set of trial
    k: u8,
    //Number of trials
    n: u8,
    //Probability of a success of a single trial
    p: f32,
}

const MAX_K: u8 = 170;
const MAX_N: u8 = 170;

impl Binomial {
    pub fn new(k: u8, n: u8, p: f32) -> Result<Binomial, DeepMesaError> {
        if k > MAX_K {
            return Err(DeepMesaError::new(
                INVALID_VALUE_ERROR,
                format!("The value for k cannot exceed {}", MAX_K),
            ));
        }
        if n > MAX_N {
            return Err(DeepMesaError::new(
                INVALID_VALUE_ERROR,
                format!("The value for n cannot exceed {}", MAX_N),
            ));
        }

        if p > 1.0 {
            return Err(DeepMesaError::new(
                INVALID_VALUE_ERROR,
                "The value for p cannot exceed 1.0".to_string(),
            ));
        }

        if p < 0.0 {
            return Err(DeepMesaError::new(
                INVALID_VALUE_ERROR,
                "The value for p cannot be less than 0.0".to_string(),
            ));
        }
        if p == -0.0 {
            return Ok(Binomial { k, n, p: 0.0 });
        }
        return Ok(Binomial { k, n, p });
    }

    fn factorial(n: u8) -> f64 {
        let mut fact: f64 = 1.0;
        for i in 1..=n {
            fact = fact * (i as f64);
        }

        fact
    }
}

impl Base for Binomial {
    fn mean(&self) -> f64 {
        return (self.p * self.n as f32) as f64;
    }

    fn median(&self) -> Option<f64> {
        None
    }

    fn mode(&self) -> Option<f64> {
        None
    }
}

impl Discrete for Binomial {
    fn pmf(&self) -> f64 {
        let n_fact = Binomial::factorial(self.n);
        let k_fact = Binomial::factorial(self.k);
        let nk_diff = self.n - self.k;
        let nkd_fact = Binomial::factorial(nk_diff);
        let p_pow_k = self.p.powi(self.k as i32);

        return (n_fact / (k_fact * nkd_fact))
            * (p_pow_k as f64)
            * (1.0 - self.p).powi(nk_diff as i32) as f64;
    }
}

#[cfg(test)]
mod tests {
    use crate::distribution::Discrete;

    use super::Binomial;

    #[test]
    fn test_neg_prob() {
        let b = Binomial::new(1, 1, -0.0);
        match b {
            Err(e) => panic!("Error: {}", e),
            Ok(b) => assert_eq!(b.p, 0.0),
        }
    }

    #[test]
    fn test_invalid_n() {
        let b = Binomial::new(1, 200, 0.2);
        match b {
            Err(e) => println!("Error: {}", e),
            Ok(_) => panic!("Shouldn't have succeeded"),
        }
    }

    #[test]
    fn test_invalid_k() {
        let b = Binomial::new(182, 29, 0.2);
        match b {
            Err(e) => println!("Error: {}", e),
            Ok(_) => panic!("Shouldn't have succeeded"),
        }
    }

    #[test]
    fn test_basic() {
        let b = Binomial::new(4, 6, 0.3).unwrap();
        let pmf = b.pmf();
        assert_eq!((pmf * 1000000.0).round() / 1000000.0, 0.059535);
    }
}
