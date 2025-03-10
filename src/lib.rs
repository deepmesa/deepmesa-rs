//! A collection of data structures and algorithms designed for performance.

/// Data structures that implement various collections that are
/// designed for performance
#[cfg(feature = "collections")]
pub mod collections {
    pub use deepmesa_collections::linkedlist::list::LinkedList;
    /// This module contains structs specific to the [`LinkedList`]
    pub mod linkedlist {
        pub use deepmesa_collections::linkedlist::iter::Iter;
        pub use deepmesa_collections::linkedlist::iter::IterMut;
        pub use deepmesa_collections::linkedlist::node::NodeHandle;
    }

    pub use deepmesa_collections::map::lhmap::LinkedHashMap;

    /// This module contains structs specific to the [`LinkedHashMap`]
    pub mod map {
        pub use deepmesa_collections::map::entry::Entry;
        pub use deepmesa_collections::map::entry::Order;
    }

    /// This module contains traits and structs specific to the [`BitVector`]
    pub mod bitvec {
        pub use deepmesa_collections::bitvec::bitslice::BitSlice;
        pub use deepmesa_collections::bitvec::iter::Iter;
        pub use deepmesa_collections::bitvec::iter::IterMut;
        pub use deepmesa_collections::bitvec::iter::IterOnes;
        pub use deepmesa_collections::bitvec::iter::IterU128;
        pub use deepmesa_collections::bitvec::iter::IterU16;
        pub use deepmesa_collections::bitvec::iter::IterU32;
        pub use deepmesa_collections::bitvec::iter::IterU64;
        pub use deepmesa_collections::bitvec::iter::IterU8;
        pub use deepmesa_collections::bitvec::iter::IterZeros;
        pub use deepmesa_collections::bitvec::traits::AsLsb0;
        pub use deepmesa_collections::bitvec::traits::AsMsb0;
        pub use deepmesa_collections::bitvec::traits::BitwiseClear;
        pub use deepmesa_collections::bitvec::traits::BitwiseClearAssign;
        pub use deepmesa_collections::bitvec::traits::BitwiseLsb;
        pub use deepmesa_collections::bitvec::traits::BitwiseLsbAssign;
        pub use deepmesa_collections::bitvec::traits::BitwiseMsb;
        pub use deepmesa_collections::bitvec::traits::BitwiseMsbAssign;
        pub use deepmesa_collections::bitvec::traits::BitwisePartial;
        pub use deepmesa_collections::bitvec::traits::BitwisePartialAssign;
        pub use deepmesa_collections::bitvec::traits::NotLsb;
        pub use deepmesa_collections::bitvec::traits::NotLsbAssign;
        pub use deepmesa_collections::bitvec::traits::NotMsb;
        pub use deepmesa_collections::bitvec::traits::NotMsbAssign;
        pub use deepmesa_collections::bitvec::traits::NotPartial;
        pub use deepmesa_collections::bitvec::traits::NotPartialAssign;
        pub use deepmesa_collections::bitvec::BitOrder;
    }

    pub use deepmesa_collections::bitvec::bitvec::BitVector;
    pub use deepmesa_collections::bitvector;
}

/// A collection of encoding and decoding algorithms
#[cfg(feature = "encoding")]
pub mod encoding {
    pub use deepmesa_encoding::prefix::unary::UnaryDecoder;
    pub use deepmesa_encoding::prefix::unary::UnaryEncoder;

    pub use deepmesa_encoding::prefix::gamma::GammaDecoder;
    pub use deepmesa_encoding::prefix::gamma::GammaEncoder;

    pub use deepmesa_encoding::prefix::delta::DeltaDecoder;
    pub use deepmesa_encoding::prefix::delta::DeltaEncoder;

    pub use deepmesa_encoding::prefix::golomb::GolombDecoder;
    pub use deepmesa_encoding::prefix::golomb::GolombEncoder;

    pub use deepmesa_encoding::prefix::varbyte::VarByteDecoder;
    pub use deepmesa_encoding::prefix::varbyte::VarByteEncoder;
}
