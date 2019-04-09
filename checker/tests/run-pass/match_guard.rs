// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that uses a match guard to check that an index is within bounds

pub enum Path {
    LocalVariable { ordinal: usize },
}

pub struct AbstractValue {}

impl Path {
    pub fn refine_parameters(&self, arguments: &[(i32, AbstractValue)]) -> i32 {
        match self {
            Path::LocalVariable { ordinal } if 0 < *ordinal && *ordinal <= arguments.len() => {
                arguments[*ordinal - 1].0
            }
            _ => 0,
        }
    }
}

pub fn main() {}
