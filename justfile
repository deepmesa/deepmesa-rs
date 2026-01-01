
all: build test doc

build:
    cargo build --all

# To run a single test: cargo test --package package-name module_path::test_name -- --nocapture
# add -- --nocapture along with the RUST_BACKTRACE=1 env variable to show backtraces in failed tests
# Example: cargo test --package deepmesa-collections bitvec::bitvec::test_read_u16 -- --nocapture
# To run all tests: cargo test --all -- --nocapture
#    cargo test --package deepmesa-collections bitvec::bitslice::tests::test_read_bits_u8 -- --nocapture
#    cargo test --package deepmesa-collections bitvec::bitvec::tests::test_read_u16 -- --nocapture
#    cargo test --package deepmesa-collections bitvec::tests::test_convert_u128 -- --nocapture
#    cargo test --package deepmesa-collections bitvec::bitvec::tests::test_push_bits  -- --nocapture --exact
#    cargo test --package deepmesa-collections bitvec::bitslice::tests::test_bit_not -- --nocapture
#    cargo test --package deepmesa-collections bitvec::bitops::tests::test_not_msb_inplace -- --nocapture --exact
#    RUST_BACKTRACE=1 cargo test --package deepmesa-collections bitvec::byteslice::tests::tfest_count_ones -- --nocapture
# To run doc tests
#    cargo test --doc --package deepmesa-collections map::lhmap::LinkedHashMap
#
test $RUST_BACKTRACE="1":
     cargo test --package deepmesa-collections cdeque::cdeque::tests

doc:
    cargo doc --no-deps --all

clean:
    cargo clean

# Needs the cargo-release package (https://github.com/crate-ci/cargo-release)
# cargo install cargo-release

release-minor:
    cargo release minor --workspace

release-patch:
    cargo release patch --workspace
