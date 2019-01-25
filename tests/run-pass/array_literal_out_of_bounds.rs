// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls visit_aggregate

pub fn main() {
    let x = [1, 2];
    let _y = x[2]; //~ Control might reach this expression with operand values that cause a panic.
}
