
all: build test doc

build:
    cargo build --all

test:
    cargo test --all -- --nocapture

doc:
    cargo doc --no-deps --all

clean:
    cargo clean

release-minor:
    cargo release minor --workspace

release-patch:
    cargo release patch --workspace
