#!/bin/bash
#Copyright (c) Facebook, Inc. and its affiliates.

# This source code is licensed under the MIT license found in the
# LICENSE file in the root directory of this source tree.

# install formatter
rustup component add rustfmt-preview
# install linter
rustup component add clippy-preview
# install audit
cargo install --force cargo-audit || true
