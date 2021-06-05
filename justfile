
all: build test doc

build:
    cargo build --all

# To run a single test: cargo test --package package-name module_path::test_name -- --nocapture
# Example: cargo test --package deepmesa-collections bitvec::bitvec::test_read_u16 -- --nocapture
# To run all tests: cargo test --all -- --nocapture
#    cargo test --package deepmesa-collections bitvec::bitslice::tests::test_read_bits_u8 -- --nocapture
#    cargo test --package deepmesa-collections bitvec::bitvec::tests::test_read_u16 -- --nocapture
#    cargo test --package deepmesa-collections bitvec::tests::test_convert_u128 -- --nocapture
#    cargo test --package deepmesa-collections bitvec::bitvec::tests::test_push_bits  -- --nocapture --exact
#    cargo test --package deepmesa-collections bitvec::bitslice::tests::test_bit_not -- --nocapture
#    cargo test --package deepmesa-collections bitvec::bitops::tests::test_not_msb_inplace -- --nocapture --exact
#    RUST_BACKTRACE=1 cargo test --package deepmesa-collections bitvec::byteslice::tests::test_count_ones -- --nocapture
test:
     cargo test --package deepmesa-collections -- --nocapture

doc:
    cargo doc --no-deps --all

clean:
    cargo clean

release-minor:
    cargo release minor --workspace

release-patch:
    cargo release patch --workspace
