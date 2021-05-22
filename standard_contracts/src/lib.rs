// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

#![feature(allocator_api)]
#![feature(backtrace)]
#![feature(core_intrinsics)]
#![feature(discriminant_kind)]
#![feature(exclusive_range_pattern)]
#![feature(hashmap_internals)]
#![feature(pattern)]
#![feature(toowned_clone_into)]
#![feature(ptr_internals)]

#[macro_use]
extern crate mirai_annotations;

#[macro_use]
mod macros;

pub mod foreign_contracts;
