#!/bin/bash
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# Exit immediately if a command exits with a non-zero status.
set -e
# start clean
cargo clean -p mirai
rm -rf target/debug/.summary_store.sled
# Run format checks
cargo fmt --all
# Run lint checks
cargo audit
cargo clippy -- -D warnings
# Build
cd checker; cargo rustc --lib -- -D rust-2018-idioms
cd ..; cargo build
# Run mirai on itself
cargo uninstall mirai || true
cargo install --debug --path ./checker
cargo clean -p mirai
time RUSTC_WRAPPER=mirai RUST_BACKTRACE=1 MIRAI_LOG=warn cargo build --lib -p mirai
