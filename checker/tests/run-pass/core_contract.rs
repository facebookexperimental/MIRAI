// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a contract defined for a core function.

pub fn main() {
    let x: Option<i64> = Some(1);
    let _y = x.unwrap();
    let z: Option<i64> = None;
    let _ = z.unwrap(); //~ unsatisfied precondition: self may not be None, defined in standard_contracts/src/foreign_contracts.rs:414:17: 414:71
}
