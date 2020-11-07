// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests for std::slice::memcmp

use core::cmp::Ordering;
use mirai_annotations::*;

fn compare_strings(str: &str) -> Ordering {
    str.cmp("foo")
}

pub fn test1() {
    verify!(compare_strings("fo") == Ordering::Less);
    verify!(compare_strings("fon") == Ordering::Less);
    verify!(compare_strings("foo") == Ordering::Equal);
    verify!(compare_strings("fool") == Ordering::Greater);
    verify!(compare_strings("fop") == Ordering::Greater);
}

fn compare_byte_arrays(arr: &[u8]) -> Ordering {
    arr.cmp(&[1, 2, 3])
}

pub fn test2() {
    verify!(compare_byte_arrays(&[1, 2]) == Ordering::Less);
    verify!(compare_byte_arrays(&[1, 2, 2]) == Ordering::Less);
    verify!(compare_byte_arrays(&[1, 2, 3]) == Ordering::Equal);
    verify!(compare_byte_arrays(&[1, 2, 3, 4]) == Ordering::Greater);
    verify!(compare_byte_arrays(&[1, 2, 4]) == Ordering::Greater);
}

pub fn main() {}
