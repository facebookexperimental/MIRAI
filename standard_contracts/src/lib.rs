// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

#![allow(internal_features)]
#![feature(allocator_api)]
#![feature(core_intrinsics)]
#![feature(discriminant_kind)]
#![feature(exclusive_range_pattern)]
#![feature(hashmap_internals)]
#![feature(pattern)]
#![feature(ptr_internals)]
#![feature(ptr_metadata)]
#![feature(control_flow_enum)]

#[macro_use]
extern crate mirai_annotations;

#[macro_use]
mod macros;

pub mod foreign_contracts;
