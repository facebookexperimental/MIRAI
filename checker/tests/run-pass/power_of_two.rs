// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that calls is_power_of_two.

use mirai_annotations::*;

pub fn main() {
    verify!(4u8.is_power_of_two());
    verify!(!5u8.is_power_of_two());

    verify!(4096u16.is_power_of_two());
    verify!(!4097u16.is_power_of_two());

    verify!(1048576u32.is_power_of_two());
    verify!(!1048577u32.is_power_of_two());

    verify!(1099511627776u64.is_power_of_two());
    verify!(!1099511627777u64.is_power_of_two());

    verify!(1180591620717411303424u128.is_power_of_two());
    verify!(!1180591620717411303425u128.is_power_of_two());

    verify!(1048576usize.is_power_of_two());
    verify!(!1048577usize.is_power_of_two());
}
