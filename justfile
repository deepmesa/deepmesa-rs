
all: build test doc

run: build
    @./target/debug/deepmesa

build:
    @cargo build --all

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
#     cargo test --all
#     cargo test --package deepmesa-collections matrix::matrix::tests::test_overflow_f64 -- --nocapture
#     cargo test --package deepmesa-common -- --nocapture
#     cargo test --package deepmesa-stats -- --nocapture
#     cargo test --package deepmesa-collections matrix::tests::cmm_new_tests -- --nocapture
#     cargo test --package deepmesa-collections matrix::tests::rmm_new_tests -- --nocapture
#     cargo test --package deepmesa-collections matrix::tests::di_new_tests -- --nocapture
#     cargo test --package deepmesa-collections matrix::vector::tests::test_dot_product -- --nocapture
#     @cargo test --package deepmesa-collections matrix -- --nocapture
test $RUST_BACKTRACE="1":
     @cargo test --package deepmesa-ai matrix::rm::gemm -- --nocapture

doc:
    @cargo doc --no-deps --all

clean:
    @cargo clean

# Needs the cargo-release package (https://github.com/crate-ci/cargo-release)
# cargo install cargo-release

release-minor:
    cargo release minor --workspace

release-patch:
    cargo release patch --workspace
