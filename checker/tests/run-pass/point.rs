// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// MIRAI_FLAGS --diag=verify

use mirai_annotations::*;

use std::ops::{Add, AddAssign};

#[derive(PartialEq, Clone, Copy)]
pub struct Point {
    x: u64,
    y: u64,
}

impl Point {
    pub fn new(x: u64, y: u64) -> Point {
        Point { x, y }
    }
    pub fn get_x(self) -> u64 {
        self.x
    }
    pub fn get_y(self) -> u64 {
        self.y
    }
}

impl Add for Point {
    type Output = Point;
    fn add(self, other: Point) -> Point {
        Point::new(self.x + other.x, self.y + other.y)
    }
}

impl AddAssign for Point {
    fn add_assign(&mut self, other: Point) {
        self.x += other.x;
        self.y += other.y;
    }
}

pub fn main() {
    let w = abstract_value!(1u64);
    let x = abstract_value!(2u64);
    let y = abstract_value!(3u64);
    let z = abstract_value!(4u64);

    assume!(w <= std::u64::MAX / 2); // avoid overflow
    assume!(x <= std::u64::MAX / 2); // avoid overflow
    assume!(y <= std::u64::MAX / 2); // avoid overflow
    assume!(z <= std::u64::MAX / 2); // avoid overflow

    let a = Point::new(w, x);
    let b = Point::new(y, z);
    let c = a + b;
    let d = Point::new(w + y, x + z);
    verify!(c.eq(&d));
}
