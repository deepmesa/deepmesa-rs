use crate::matrix::rm::MatrixRowMajor;
use crate::matrix::rm::*;
use crate::matrix::traits::MatrixElement;
use std::ops::MulAssign;

macro_rules! iterate_mnk {
    ($a:ident, $b:ident, $c:ident, $m:ident, $n:ident, $k:ident, $val:ident, $e:expr, $s:expr) => {
        for $m in 0..$a.rows {
            for $n in 0..$b.cols {
                let mut $val: T = T::zero();
                for $k in 0..$a.cols {
                    $val += $e;
                }
                $s;
            }
        }
    };
}

// impl<T> MatrixRowMajor<T>
// where
//     T: MatrixElement,
// {
//     fn foo(&mut self, val: T) {
//         self.add_assign(val);
//     }
// }

impl<T> MatrixRowMajor<T>
where
    T: MatrixElement<Output = T>
        + std::ops::Mul<Output = T>
        + std::ops::AddAssign
        + std::ops::MulAssign,
{
    // a = mxk matrix
    // b = kxn matrix
    // c = mxn matrix
    pub fn gemm(&mut self, alpha: T, beta: T, a: &MatrixRowMajor<T>, b: &MatrixRowMajor<T>) {
        if a.cols != b.rows {
            panic!("a cols not equal b rows");
        }
        if a.rows != self.rows {
            panic!("a rows not equal c rows");
        }
        if b.cols != self.cols {
            panic!("b cols not equal c cols");
        }

        if beta != T::zero() {
            self.mul_assign(beta);
            if alpha == T::zero() {
                return;
            }
            //now do add assign
            if a.is_transpose {
                if b.is_transpose {
                    if self.is_transpose {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get_t!(a, m, k) * rm_get_t!(b, k, n) },
                                     unsafe { rm_add_assign_t!(self, m, n, val*alpha);});
                    } else {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get_t!(a, m, k) * rm_get_t!(b, k, n) },
                                     unsafe { rm_add_assign!(self, m, n, val*alpha);});
                    }
                } else {
                    if self.is_transpose {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get_t!(a, m, k) * rm_get!(b, k, n) },
                                     unsafe { rm_add_assign_t!(self, m, n, val*alpha);});
                    } else {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get_t!(a, m, k) * rm_get!(b, k, n) },
                                     unsafe { rm_add_assign!(self, m, n, val*alpha);});
                    }
                }
            } else {
                if b.is_transpose {
                    if self.is_transpose {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get!(a, m, k) * rm_get_t!(b, k, n) },
                                     unsafe { rm_add_assign_t!(self, m, n, val*alpha);});
                    } else {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get!(a, m, k) * rm_get_t!(b, k, n) },
                                     unsafe { rm_add_assign!(self, m, n, val*alpha);});
                    }
                } else {
                    if self.is_transpose {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get!(a, m, k) * rm_get!(b, k, n) },
                                     unsafe { rm_add_assign_t!(self, m, n, val*alpha);});
                    } else {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get!(a, m, k) * rm_get!(b, k, n) },
                                     unsafe { rm_add_assign!(self, m, n, val*alpha);});
                    }
                }
            }
        } else {
            if alpha == T::zero() {
                //TODO: Fill self with zeros
                return;
            }

            //now do add assign
            if a.is_transpose {
                if b.is_transpose {
                    if self.is_transpose {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get_t!(a, m, k) * rm_get_t!(b, k, n) },
                                     unsafe { rm_assign_t!(self, m, n, val*alpha);});
                    } else {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get_t!(a, m, k) * rm_get_t!(b, k, n) },
                                     unsafe { rm_assign!(self, m, n, val*alpha);});
                    }
                } else {
                    if self.is_transpose {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get_t!(a, m, k) * rm_get!(b, k, n) },
                                     unsafe { rm_assign_t!(self, m, n, val*alpha);});
                    } else {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get_t!(a, m, k) * rm_get!(b, k, n) },
                                     unsafe { rm_assign!(self, m, n, val*alpha);});
                    }
                }
            } else {
                if b.is_transpose {
                    if self.is_transpose {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get!(a, m, k) * rm_get_t!(b, k, n) },
                                     unsafe { rm_assign_t!(self, m, n, val*alpha);});
                    } else {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get!(a, m, k) * rm_get_t!(b, k, n) },
                                     unsafe { rm_assign!(self, m, n, val*alpha);});
                    }
                } else {
                    if self.is_transpose {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get!(a, m, k) * rm_get!(b, k, n) },
                                     unsafe { rm_assign_t!(self, m, n, val*alpha);});
                    } else {
                        #[rustfmt::skip]
                        iterate_mnk!(a,b,self,m,n,k,val,
                                     unsafe { rm_get!(a, m, k) * rm_get!(b, k, n) },
                                     unsafe { rm_assign!(self, m, n, val*alpha);});
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::matrix::rm::macros::*;
    use crate::matrix::rm::*;
    use crate::matrix::traits::*;

    #[test]
    fn test_gemm() {
        let a = matrix_rm!([f32, 2, 3, false], 1,2,3;4,5,6);
        let b = matrix_rm!([f32, 3, 2, false], 1,2;3,4;5,6);
        let mut c = matrix_rm!([f32, 2, 2, false], 5,6;7,8);

        let alpha: f32 = 2.0;
        let beta: f32 = 3.0;
        c.gemm(alpha, beta, &a, &b);
        println!("c={:?}", c);
    }

    // #[test]
    // fn test_beta_c() {
    //     let a = matrix_rm!([f32, 2, 3, false], 1,2,3;4,5,6);
    //     let b = matrix_rm!([f32, 3, 2, false], 1,2;3,4;5,6);
    //     let mut c = matrix_rm!([f32, 2, 2, false], 5,6;7,8);

    //     let alpha: f32 = 1.0;
    //     let beta: f32 = 0.0;
    //     c.gemm(alpha, beta, &a, &b);
    //     println!("c={:?}", c);
    // }
}
