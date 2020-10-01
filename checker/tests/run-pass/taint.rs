// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use mirai_annotations::*;

pub struct Foo {
    bar: i64,
}

fn source() -> Foo {
    let result = Foo { bar: 1 };
    set_model_field!(&result, tainted, true);
    result
}

pub fn sink(foo: Foo) {
    // If foo has not been explicitly tainted by a source, it is not tainted.
    precondition!(!get_model_field!(&foo, tainted, false)); //~ related location
    let _x = foo.bar;
}

fn sanitize(foo: &Foo) {
    set_model_field!(foo, tainted, false);
}

pub fn test1() {
    let untainted = Foo { bar: 2 };
    sink(untainted);
}

pub fn test2() {
    let tainted = source();
    sanitize(&tainted);
    sink(tainted);
}

pub fn test3() {
    let tainted = source();
    sink(tainted); //~ unsatisfied precondition
}

pub fn main() {}
