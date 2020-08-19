// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test that uses ranges mutated via iterators in a loop.

#![feature(range_is_empty)]
#![feature(unchecked_math)]

#[macro_use]
extern crate mirai_annotations;

pub fn test1() {
    let mut it = std::ops::Range {
        start: 0usize,
        end: 10usize,
    };

    while let Some(_) = it.next() {
        verify!(it.start <= 10);
    }
    verify!(it.start >= 10);
}

// pub fn test2() {
//     let mut it = std::ops::RangeInclusive::new(0usize, 10usize);
//     while let Some(_) = it.next() {
//         verify!(*it.start() <= 10);
//     }
//     verify!(it.is_empty());
// }

struct UsizeRangeInclusive {
    start: usize,
    end: usize,
    exhausted: bool,
}

impl UsizeRangeInclusive {
    fn new(start: usize, end: usize) -> UsizeRangeInclusive {
        UsizeRangeInclusive {
            start,
            end,
            exhausted: false,
        }
    }

    fn is_empty(&self) -> bool {
        self.exhausted || !(self.start <= self.end)
    }

    fn next(&mut self) -> Option<usize> {
        if self.is_empty() {
            return None;
        }
        let is_iterating = self.start < self.end;
        Some(if is_iterating {
            let n = unsafe { std::iter::Step::forward_unchecked(self.start.clone(), 1) };
            std::mem::replace(&mut self.start, n)
        } else {
            self.exhausted = true;
            self.start.clone()
        })
    }
}

pub fn test3() {
    let mut it = UsizeRangeInclusive::new(0usize, 10usize);
    while let Some(_) = it.next() {
        verify!(it.start <= 10);
    }
    verify!(it.is_empty());
}

pub fn main() {}
