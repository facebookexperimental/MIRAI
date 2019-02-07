#!/bin/bash
# Exit immediately if a command exits with a non-zero status.
set -e
# start clean
cargo clean -p mirai
# Run format checks
cargo fmt --all
# Run lint checks
cargo clippy -- -D warnings
# Build
time cargo build
# Run mirai on itself
cargo uninstall mirai || true
cargo install --debug --path .
cargo clean -p mirai
time RUSTC_WRAPPER=mirai RUST_BACKTRACE=1 cargo build
