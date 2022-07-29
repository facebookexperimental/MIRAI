#!/usr/bin/env bash
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# Directory for this source file
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

TOOLCHAIN=$(cat "$DIR/rust-toolchain.toml")

# override tool chain
rustup override set $TOOLCHAIN

# install audit
cargo install cargo-audit
