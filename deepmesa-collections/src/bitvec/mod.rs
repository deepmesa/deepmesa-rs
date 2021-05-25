mod bitops;

#[macro_use]
mod macros;

pub mod bitslice;
pub mod bitvec;
pub mod iter;
pub mod traits;

type BitCount = usize;

/// This enum indicates the order in which bits are traversed
/// and counted.
///
/// [`Msb0`](#variant.Msb0) indicates that the MSB (Most Significant
/// Bit) should be considered as position `0` and consequently bits
/// should be counted from the MSB to the LSB.
///
/// [`Lsb0`](#variant.Lsb0) indicates tht the LSB (Least Significant
/// Bit) should be considered as position `0` and the bits should
/// therefore be counter from the LSB to the MSB.
///
/// Here is an illustrative example:
///
/// # Examples
/// ```text
/// let val: u8 = 0b1011_1100;
/// ```
/// Counting 4 bits from the `Msb0` would yield `1011` while counting 4
/// bits from the `Lsb0` would result in `1100`
///
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitOrder {
    /// Counts bits from the LSB (Least Significant Bit) to the MSB
    /// (Most Significant Bit).
    Lsb0,
    /// Counts bits from the MSB (Most Significant Bit) to the LSB
    /// (Least Significant Bit).
    Msb0,
}

/// A macro to construct a new [BitVector](BitVector) from a bit pattern.
///
/// This macro accepts a sequence of 1s and 0s separated by commas,
/// (an array of bits effectively) and creates a new BitVector from
/// that pattern. Any token other than a `0` or a `1` will result in a
/// panic.
///
/// # Examples
/// ```
/// use deepmesa::collections::BitVector;
/// use deepmesa::collections::bitvector;
///
/// let bv = bitvector![1,0,1,1,0,1,0,1];
/// assert_eq!(bv.len(), 8);
/// assert_eq!(bv.read_u8(0), (0b1011_0101, 8));
/// ```
///
/// The macro can also accept a single bit (1 or 0) and a length and
/// construct a BitVector of that length with the repeating bit.
///
/// # Examples
/// ```
/// use deepmesa::collections::BitVector;
/// use deepmesa::collections::bitvector;
///
/// let bv = bitvector![1;100];
/// assert_eq!(bv.len(), 100);
/// ```
///
/// Finally this macro can also be used to construct an empty
/// BitVector.
///
/// # Examples
/// ```
/// use deepmesa::collections::BitVector;
/// use deepmesa::collections::bitvector;
///
/// let bv = bitvector!();
/// assert_eq!(bv.len(), 0);
/// ```
#[macro_export]
macro_rules! bitvector {
    () => {
        BitVector::new();
    };
    ($($arg:tt)*) => {{
        let slice = [$($arg)*];
        let mut bv = BitVector::new();
        for item in &slice {
            match item {
                0 => bv.push(false),
                1 => bv.push(true),
                _ => panic!("{} is not a binary digit", item),
            }
        }
        bv
    };};
    ($item: expr, $len: expr) => {
        {
            match $item {
                0=> BitVector::repeat(false, $len),
                1=> BitVector::repeat(true, $len),
                _ => panic!("{} is not a binary digit", item),
            }
        }
    };
}
