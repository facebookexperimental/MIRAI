// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that use enum discriminants

use mirai_annotations::*;

pub enum Path {
    QualifiedPath { length: usize, qualifier: Box<Path> },
    Root,
}

impl Path {
    pub fn path_length(&self) -> usize {
        match self {
            Path::QualifiedPath { length, .. } => *length,
            _ => 1,
        }
    }

    pub fn replace_root(&self, new_root: Path) -> Path {
        match self {
            Path::QualifiedPath { qualifier, .. } => {
                checked_assume!(qualifier.path_length() <= 10);
                Path::QualifiedPath {
                    length: qualifier.path_length() + 1,
                    qualifier: Box::new(Path::Root),
                }
            }
            _ => new_root,
        }
    }
}

pub fn main() {}
