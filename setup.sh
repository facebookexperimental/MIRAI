#!/bin/bash
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# Directory for this source file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

TOOLCHAIN=$(cat "$DIR/rust-toolchain")

# install formatter
rustup "+$TOOLCHAIN" component add rustfmt-preview
# install linter
rustup "+$TOOLCHAIN" component add clippy-preview
# install rustc-dev
rustup "+$TOOLCHAIN" component add rustc-dev
# install llvm-tools
rustup "+$TOOLCHAIN" component add llvm-tools-preview
# install audit
cargo "+$TOOLCHAIN" install cargo-audit
