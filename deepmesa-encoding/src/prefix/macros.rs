macro_rules! decoding_iter {
    ($iter:ident, $decode_fn: expr) => {
        pub struct $iter<'a> {
            bitvec: &'a BitVector,
            cursor: usize,
        }

        impl<'a> $iter<'a> {
            pub(super) fn new(bitvec: &'a BitVector) -> $iter<'a> {
                $iter { bitvec, cursor: 0 }
            }
        }

        impl<'a> Iterator for $iter<'a> {
            type Item = u128;
            fn next(&mut self) -> Option<Self::Item> {
                match $decode_fn(self.bitvec, self.cursor) {
                    None => None,
                    Some((val, bits_read)) => {
                        self.cursor += bits_read;
                        Some(val)
                    }
                }
            }
        }
    };
}

macro_rules! impl_encoder {
    (
        $(#[$outer:meta])*
        $encoder:ident,
        $encode_fn: expr
    ) => {
        impl_encoder!(
            $(#[$outer])*
            $encoder,
            stringify!($encoder),
            $encode_fn,
            stringify!($encode_fn)
        );
    };

    (
        $(#[$outer:meta])*
        $encoder:ident,
        $sencoder: expr,
        $encode_fn: expr,
        $sencode_fn: expr
    ) => {
        $(#[$outer])*
        pub struct $encoder {
            pub(super) bitvec: BitVector,
            pub(super) elements: usize,
        }

        impl $encoder {
            /// Creates a new [`
            #[doc = $sencoder]
            /// `] with the underlying [`BitVector`] initialized with
            /// a capacity of 1024 bits. .
            pub fn new() -> $encoder {
                $encoder {
                    bitvec: BitVector::with_capacity(1024),
                    elements: 0,
                }
            }

            /// Creates a new [`
            #[doc = $sencoder]
            /// `] with the underlying [`BitVector`] initialized with
            /// the specified `capacity_bits`;
            pub fn with_capacity(capacity_bits: usize) -> $encoder {
                $encoder {
                    bitvec: BitVector::with_capacity(capacity_bits),
                    elements: 0,
                }
            }

            /// Encodes the specified [`u128`] `val`
            pub fn encode(&mut self, val: u128) {
                $encode_fn(&mut self.bitvec, val);
                self.elements += 1;
            }

            /// Returns an immutable reference to the underlying
            /// [`BitVector`] containing the encoded bits.
            pub fn encoded(&self) -> &BitVector {
                &self.bitvec
            }

            /// Returns the length in bits of the underlying
            /// [`BitVector`] containing the encoded bits.
            pub fn encoded_len(&self) -> usize {
                self.bitvec.len()
            }

            /// Returns the number of elements encoded in the
            /// underlying [`BitVector`].
            pub fn elements(&self) -> usize {
                self.elements
            }

            /// Returns the compression ratio of the encoded
            /// elements. This is simply the
            /// [`.encoded_len()`](#method.encoded_len()) divided by
            /// the number of [`.elements()`](#method.elements());
            pub fn comp_ratio(&self) -> f64 {
                self.bitvec.len() as f64 / self.elements as f64
            }
        }
    };
}

macro_rules! impl_decoder {
    (
        $(#[$outer:meta])*
        $decoder:ident,
        $decode_fn:expr,
        $decoding_iter:ident
    ) => {
        impl_decoder!(
            $(#[$outer])*
            $decoder,
            stringify!($decoder),
            $decode_fn,
            stringify!($decode_fn),
            $decoding_iter,
            stringify!($decoding_iter)
        );
    };

    (
        $(#[$outer:meta])*
        $decoder:ident,
        $sdecoder:expr,
        $decode_fn:expr,
        $sdecode_fn: expr,
        $decoding_iter:ident,
        $sdecoding_iter:expr
    ) => {
        $(#[$outer])*
        pub struct $decoder<'a> {
            pub(super) bitvec: &'a BitVector,
            pub(super) cursor: usize,
        }

        impl<'a> $decoder<'a> {
            /// Creates a new [`
            #[doc = $sdecoder]
            /// `] with the specified [`BitVector`] containing the
            /// encoded bits.
            pub fn new(bitvec: &'a BitVector) -> $decoder<'a> {
                $decoder {
                    bitvec: bitvec,
                    cursor: 0,
                }
            }

            /// Decodes the next available encoded element using an
            /// internal cursor. Returns the decoded value or None if
            /// there are no more elements to decode.
            pub fn decode(&mut self) -> Option<u128> {
                match $decode_fn(self.bitvec, self.cursor) {
                    None => None,
                    Some((val, bits_read)) => {
                        self.cursor += bits_read;
                        Some(val)
                    }
                }
            }

            /// Decodes upto `max_elements` from the encoded
            /// bits. Returns a vector containing the decoded
            /// elements. If there are no elements to decode then this
            /// method will return an empty [`Vec`].
            pub fn decode_many(&self, max_elements: usize) -> Vec<u128> {
                let mut vec = Vec::<u128>::with_capacity(max_elements);
                let mut ct = 0;

                let mut iter = self.iter();
                loop {
                    match iter.next() {
                        None => return vec,
                        Some(val) => {
                            vec.push(val);
                            ct += 1;
                            if ct >= max_elements {
                                return vec;
                            }
                        }
                    }
                }
            }

            /// Returns an iterator that iterates over the encoded
            /// elements and decodes them on every invocation.
            pub fn iter(&self) -> $decoding_iter {
                $decoding_iter::<'a>::new(self.bitvec)
            }
        }

        impl<'a> Iterator for $decoder<'a> {
            type Item = u128;
            fn next(&mut self) -> Option<Self::Item> {
                self.decode()
            }
        }
    };
}
