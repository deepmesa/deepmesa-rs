mod bitops;
pub mod bitslice;
pub mod bitvec;
pub mod iter;

type BitCount = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitOrder {
    Lsb0,
    Msb0,
}

pub trait BitOrderConvert {
    fn msb0_to_lsb0(&self, n: BitCount) -> Self;
    fn lsb0_to_msb0(&self, n: BitCount) -> Self;
}

macro_rules! impl_bit_order_convert {
    ($t:ty, $sz:literal) => {
        impl BitOrderConvert for $t {
            fn msb0_to_lsb0(&self, n: BitCount) -> Self {
                const TYPE_LEN: usize = $sz;
                if n == 0 {
                    return *self;
                }

                if n > TYPE_LEN {
                    panic!(
                        "Cannot convert BitOrder for BitCount ({}) > {}",
                        n, TYPE_LEN
                    );
                }
                if n == TYPE_LEN {
                    return *self;
                }
                return *self >> (TYPE_LEN - n);
            }

            fn lsb0_to_msb0(&self, n: BitCount) -> Self {
                const TYPE_LEN: usize = $sz;
                if n == 0 {
                    return *self;
                }
                if n > TYPE_LEN {
                    panic!(
                        "Cannot convert BitOrder for BitCount ({}) > {}",
                        n, TYPE_LEN
                    );
                }
                if n == TYPE_LEN {
                    return *self;
                }
                return *self << (TYPE_LEN - n);
            }
        }
    };
}

impl_bit_order_convert!(u8, 8);
impl_bit_order_convert!(u16, 16);
impl_bit_order_convert!(u32, 32);
impl_bit_order_convert!(u64, 64);
impl_bit_order_convert!(u128, 128);

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem;
    use rand::Rng;

    macro_rules! gen_test {
        ($ty:ident, $test_name:ident) => {
            #[test]
            pub fn $test_name() {
                let bitlen = mem::size_of::<$ty>() * 8;
                let pow2: $ty = 2;

                let mut rng = rand::thread_rng();
                let rand: $ty = rng.gen::<$ty>();

                //test msb0_to_lsb0 $t
                assert_eq!(rand.msb0_to_lsb0(bitlen), rand);
                let converted = rand.msb0_to_lsb0(5);

                assert_eq!(converted, rand / pow2.pow(bitlen as u32 - 5) as $ty);

                //test lsb0_to_msb0
                let rand: $ty = converted;

                assert_eq!(rand.lsb0_to_msb0(bitlen), rand);
                assert_eq!(
                    rand.lsb0_to_msb0(5),
                    rand * pow2.pow(bitlen as u32 - 5) as $ty
                );
            }
        };
    }

    gen_test! {u8,test_bit_order_convert_u8}
    gen_test! {u16,test_bit_order_convert_u16}
    gen_test! {u32,test_bit_order_convert_u32}
    gen_test! {u64,test_bit_order_convert_u64}
    gen_test! {u128,test_bit_order_convert_u128}

    #[test]
    pub fn test_convert_zero() {
        let val: u8 = 0b0000_0000;
        assert_eq!(0, val.msb0_to_lsb0(0));
        assert_eq!(0, val.lsb0_to_msb0(0));
    }
}
