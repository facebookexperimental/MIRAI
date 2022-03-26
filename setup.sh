#!/usr/bin/env bash
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# cd into the directory with this source file
cd "$( dirname "${BASH_SOURCE[0]}" )"

# `rust-toolchain.toml` is used to manage the toolchain version,
# so the toolchain version we want is applied automatically, but
# no overrides should be used
rustup override unset

# components rustc-dev llvm-tools are required to build, but installed
# automatically through `rust-toolchain.toml`.
# components rustfmt and clippy are installed by default.

# install audit
cargo install cargo-audit
