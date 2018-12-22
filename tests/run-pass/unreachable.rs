#![feature(core_intrinsics)]
#![allow(unused)]

use std::intrinsics;

fn foo() {
    unsafe { intrinsics::unreachable(); }
}
