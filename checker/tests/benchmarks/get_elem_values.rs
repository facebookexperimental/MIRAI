// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use std::convert::TryFrom;

struct Foo<'a> {
    constant_value_cache: &'a mut Bar,
}

struct Bar {}

impl Bar {
    fn get_i128_for(&self, _v: i128) -> i32 {
        0
    }
    fn get_u128_for(&self, _v: u128) -> i32 {
        0
    }
}

impl<'a> Foo<'a> {
    fn get_element_values(
        &mut self,
        bytes: &[u8],
        is_signed_type: bool,
        bytes_per_elem: usize,
        len: Option<u128>,
    ) -> Vec<i32> {
        assert!(
            bytes_per_elem == 1
                || bytes_per_elem == 2
                || bytes_per_elem == 4
                || bytes_per_elem == 8
                || bytes_per_elem == 16
        );
        if let Some(len) = len {
            if (len * (bytes_per_elem as u128)) != u128::try_from(bytes.len()).unwrap() {
                unimplemented!()
            }
        }
        let mut result = vec![];
        for i in 0..bytes.len() / bytes_per_elem {
            let j = i * bytes_per_elem;
            if is_signed_type {
                result.push(
                    self.constant_value_cache
                        .get_i128_for(match bytes_per_elem {
                            1 => i128::from(i8::from_le_bytes([bytes[j]])),
                            2 => i128::from(i16::from_le_bytes([bytes[j], bytes[j + 1]])),
                            4 => i128::from(i32::from_le_bytes([
                                bytes[j],
                                bytes[j + 1],
                                bytes[j + 2],
                                bytes[j + 3],
                            ])),
                            8 => i128::from(i64::from_le_bytes([
                                bytes[j],
                                bytes[j + 1],
                                bytes[j + 2],
                                bytes[j + 3],
                                bytes[j + 4],
                                bytes[j + 5],
                                bytes[j + 6],
                                bytes[j + 7],
                            ])),
                            16 => i128::from_le_bytes([
                                bytes[j],
                                bytes[j + 1],
                                bytes[j + 2],
                                bytes[j + 3],
                                bytes[j + 4],
                                bytes[j + 5],
                                bytes[j + 6],
                                bytes[j + 7],
                                bytes[j + 8],
                                bytes[j + 9],
                                bytes[j + 10],
                                bytes[j + 11],
                                bytes[j + 12],
                                bytes[j + 13],
                                bytes[j + 14],
                                bytes[j + 15],
                            ]),
                            _ => unreachable!(),
                        })
                        .clone()
                        .into(),
                );
            } else {
                result.push(
                    self.constant_value_cache
                        .get_u128_for(match bytes_per_elem {
                            1 => u128::from(u8::from_le_bytes([bytes[j]])),
                            2 => u128::from(u16::from_le_bytes([bytes[j], bytes[j + 1]])),
                            4 => u128::from(u32::from_le_bytes([
                                bytes[j],
                                bytes[j + 1],
                                bytes[j + 2],
                                bytes[j + 3],
                            ])),
                            8 => u128::from(u64::from_le_bytes([
                                bytes[j],
                                bytes[j + 1],
                                bytes[j + 2],
                                bytes[j + 3],
                                bytes[j + 4],
                                bytes[j + 5],
                                bytes[j + 6],
                                bytes[j + 7],
                            ])),
                            16 => u128::from_le_bytes([
                                bytes[j],
                                bytes[j + 1],
                                bytes[j + 2],
                                bytes[j + 3],
                                bytes[j + 4],
                                bytes[j + 5],
                                bytes[j + 6],
                                bytes[j + 7],
                                bytes[j + 8],
                                bytes[j + 9],
                                bytes[j + 10],
                                bytes[j + 11],
                                bytes[j + 12],
                                bytes[j + 13],
                                bytes[j + 14],
                                bytes[j + 15],
                            ]),
                            _ => unreachable!(),
                        })
                        .clone()
                        .into(),
                );
            }
        }
        result
    }
}

pub fn main() {}
