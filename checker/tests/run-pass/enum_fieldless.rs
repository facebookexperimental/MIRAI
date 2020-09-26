// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// A test that fieldless enums can have explicitly defined values for discriminants

use mirai_annotations::*;

enum SomeEnumA {
    VariantN33 = -33,
    VariantN11 = -11,
    Variant22 = 22,
    Variant44 = 44,
    Variant45,
}

enum SomeEnumB {
    None,
    Some(char),
    Leaf,
}

enum SomeEnumC {
    Only(char),
}

enum SomeEnumD {
    Only = -123,
}

fn foo(n: u32) -> SomeEnumA {
    match n {
        0 => SomeEnumA::VariantN33,
        1 => SomeEnumA::VariantN11,
        2 => SomeEnumA::Variant22,
        3 => SomeEnumA::Variant44,
        _ => SomeEnumA::Variant45,
    }
}

fn bar(n: u32) -> SomeEnumB {
    match n {
        0 => SomeEnumB::Leaf,
        1 => SomeEnumB::Some('a'),
        2 => SomeEnumB::Some('/'),
        3 => SomeEnumB::Some('A'),
        _ => SomeEnumB::None,
    }
}

fn baz(n: u32) -> SomeEnumC {
    match n {
        0 => SomeEnumC::Only('4'),
        1 => SomeEnumC::Only('$'),
        _ => SomeEnumC::Only('\0'),
    }
}

fn fun() -> SomeEnumD {
    SomeEnumD::Only
}

pub fn main() {
    verify!(matches!(foo(0), SomeEnumA::VariantN33));
    verify!(matches!(foo(1), SomeEnumA::VariantN11));
    verify!(matches!(foo(2), SomeEnumA::Variant22));
    verify!(matches!(foo(3), SomeEnumA::Variant44));
    verify!(matches!(foo(12345), SomeEnumA::Variant45));
    verify!(matches!(foo(54321), SomeEnumA::Variant45));

    verify!(matches!(bar(0), SomeEnumB::Leaf));
    verify!(matches!(bar(1), SomeEnumB::Some('a')));
    verify!(matches!(bar(2), SomeEnumB::Some('/')));
    verify!(matches!(bar(3), SomeEnumB::Some('A')));
    verify!(matches!(bar(12345), SomeEnumB::None));
    verify!(matches!(bar(54321), SomeEnumB::None));

    verify!(matches!(baz(0), SomeEnumC::Only('4')));
    verify!(matches!(baz(1), SomeEnumC::Only('$')));
    verify!(matches!(baz(2), SomeEnumC::Only('\0')));

    verify!(matches!(fun(), SomeEnumD::Only));
}
