// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests generic specialization and function constant tracking.

pub trait Iterator {
    type Item;

    fn for_each<F>(self, f: F)
    where
        Self: Sized,
        F: FnMut(Self::Item),
    {
        #[inline]
        fn call<T>(mut f: impl FnMut(T)) -> impl FnMut((), T) {
            move |(), item| f(item)
        }

        self.fold((), call(f));
    }

    fn fold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        while let Some(x) = self.next() {
            accum = f(accum, x);
        }
        accum
    }

    fn next(&mut self) -> Option<Self::Item>;
}

pub struct Foo {
    count: usize,
}

impl Iterator for Foo {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.count == 123 {
            self.count = 0;
            Some(111)
        } else {
            None
        }
    }
}

pub fn main() {
    let foo = Foo { count: 123 };
    foo.for_each(|x| assert!(x == 111));
}
