// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that generates a ConstValue::Unevaluated reference to a constant array
// and that checks that MIRAI finds the constant in the summary cache via the def_id

use mirai_annotations::*;

const FOO: [u8; 3] = [1, 2, 3];
const BAR: u8 = FOO[0]; // The reference to FOO is unevaluated in the MIR body that computes BAR

pub fn main() {
    verify!(BAR == 1);
}
