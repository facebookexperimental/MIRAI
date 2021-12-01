// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

fn slice_start_index_len_fail(index: usize, len: usize) {
    panic!(
        "range start index {} out of range for slice of length {}",
        index, len
    ); //~ related location
}

pub fn t1(index: usize, len: usize) {
    slice_start_index_len_fail(index, len); //~ range start index {} out of range for slice of length {}
}

fn slice_start_index_len_fail2(index: usize, len: usize) {
    panic!(
        "range start index {} out of range for slice of length {}, ouch",
        index, len
    ); //~ related location
}

pub fn t2(index: usize, len: usize) {
    slice_start_index_len_fail2(index, len); //~ range start index {} out of range for slice of length {}, ouch
}

pub fn main() {}
