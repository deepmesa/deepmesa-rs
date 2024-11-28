use core::fmt;

#[derive(Debug, Clone)]
pub struct DeepMesaError {
    code: String,
    msg: String,
}

pub static INVALID_VALUE_ERROR: &str = "InvalidValue";

impl DeepMesaError {
    pub fn new(code: &str, msg: String) -> DeepMesaError {
        DeepMesaError {
            code: code.to_string(),
            msg,
        }
    }
}

impl fmt::Display for DeepMesaError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{}]: {}", self.code, self.msg)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error() {
        let e = DeepMesaError {
            code: "A123".to_string(),
            msg: "This is a Test error Message".to_string(),
        };

        println!("Common Error: {}", e);
    }
}
