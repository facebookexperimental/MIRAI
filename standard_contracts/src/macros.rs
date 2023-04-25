// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

macro_rules! add_with_overflow {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(x: $t, y: $t) -> ($tt, bool) {
            use ::std::num::Wrapping;
            use std::ops::Add;
            let result = Wrapping(x as $tt).add(Wrapping(y as $tt)).0;
            (result % (($m as $tt) + 1), result > ($m as $tt))
        }
    };
}

macro_rules! atomic_int {
    ($n:ident, $t:ty, $op:tt) => {
        pub unsafe fn $n(dst: *mut $t, src: $t) -> $t {
            use ::std::num::Wrapping;
            use std::ops::AddAssign;
            use std::ops::BitAndAssign;
            use std::ops::BitOrAssign;
            use std::ops::BitXorAssign;
            use std::ops::SubAssign;
            let result = *dst;
            Wrapping(*dst).$op(Wrapping(src));
            result
        }
    };
}

macro_rules! atomic_nand {
    ($n:ident, $t:ty) => {
        pub unsafe fn $n(dst: *mut $t, src: $t) -> $t {
            let result = *dst;
            *dst = !(*dst ^ src);
            result
        }
    };
}

macro_rules! atomic_max_min {
    ($n:ident, $t:ty, $op:tt) => {
        pub unsafe fn $n(dst: *mut $t, src: $t) -> $t {
            if *dst $op src {
                src
            } else {
                *dst
            }
        }
    };
}

macro_rules! atomic_cxchg {
    ($n:ident, $t:ty) => {
        pub unsafe fn $n(dst: *mut $t, old: $t, src: $t) -> ($t, bool) {
            if abstract_value!(true) {
                *dst = src;
                (old, true)
            } else {
                (*dst, false)
            }
        }
    };
}

// No preconditions needed and no post conditions provided.
// No side-effects and can be safely used as an uninterpreted function.
macro_rules! default_contract {
    ($n:ident) => {
        pub fn $n<T>() -> T {
            result!()
        }
    };
}

macro_rules! exact_div {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!(y != 0);
            precondition!(x % y == 0);
            x / y
        }
    };
}

macro_rules! exact_signed_div {
    ($t:ty, $n:ident, $m:expr) => {
        pub fn $n(x: $t, y: $t) -> $t {
            precondition!(y != 0);
            precondition!(x != $m || y != -1);
            precondition!(x % y == 0);
            x / y
        }
    };
}

macro_rules! rotate_left {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            let bw = std::intrinsics::size_of::<$t>() as $t;
            (x << (y % bw)) | (x >> ((bw - y) % bw))
        }
    };
}

macro_rules! rotate_right {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            let bw = std::intrinsics::size_of::<$t>() as $t;
            (x << ((bw - y) % bw)) | (x >> (y % bw))
        }
    };
}

macro_rules! saturating_add {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(a: $t, b: $t) -> $t {
            let result = (a as $tt) + (b as $tt);
            if result > ($m as $tt) {
                $m
            } else {
                result as $t
            }
        }
    };
}

macro_rules! saturating_sub {
    ($t:ty, $n:ident) => {
        pub fn $n(a: $t, b: $t) -> $t {
            if a < b {
                0
            } else {
                a - b
            }
        }
    };
}

macro_rules! sub_with_overflow {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(x: $t, y: $t) -> ($t, bool) {
            let result = (x as $tt) + (-(y as $tt));
            (
                (result % (($m as $tt) + 1)) as $t,
                result < 0 || result > ($m as $tt),
            )
        }
    };
}

macro_rules! unchecked_add {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(x: $t, y: $t) -> $t {
            use ::std::num::Wrapping;
            use std::ops::Add;
            // todo: restore this
            // precondition!((x as $tt) + (y as $tt) <= ($m as $tt));
            Wrapping(x).add(Wrapping(y)).0
        }
    };
}

macro_rules! unchecked_div {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            use ::std::num::Wrapping;
            use std::ops::Div;
            precondition!(y != 0);
            Wrapping(x).div(Wrapping(y)).0
        }
    };
}

macro_rules! unchecked_signed_div {
    ($t:ty, $n:ident, $m:expr) => {
        pub fn $n(x: $t, y: $t) -> $t {
            use ::std::num::Wrapping;
            use std::ops::Div;
            precondition!(y != 0);
            precondition!(x != $m || y != -1);
            Wrapping(x).div(Wrapping(y)).0
        }
    };
}

macro_rules! unchecked_mul {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(x: $t, y: $t) -> $t {
            use ::std::num::Wrapping;
            use std::ops::Mul;
            // todo: restore this
            // precondition!((x as $tt) * (y as $tt) <= ($m as $tt));
            Wrapping(x).mul(Wrapping(y)).0
        }
    };
}

macro_rules! unchecked_rem {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: $t) -> $t {
            use ::std::num::Wrapping;
            use std::ops::Rem;
            precondition!(y != 0);
            Wrapping(x).rem(Wrapping(y)).0
        }
    };
}

macro_rules! unchecked_shl {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: usize) -> $t {
            use ::std::num::Wrapping;
            use std::ops::Shl;
            precondition!(y <= std::intrinsics::size_of::<$t>());
            Wrapping(x).shl(y).0
        }
    };
}

macro_rules! unchecked_shr {
    ($t:ty, $n:ident) => {
        pub fn $n(x: $t, y: usize) -> $t {
            use ::std::num::Wrapping;
            use std::ops::Shr;
            precondition!(y <= std::intrinsics::size_of::<$t>());
            Wrapping(x).shr(y).0
        }
    };
}

macro_rules! unchecked_signed_rem {
    ($t:ty, $n:ident, $m:expr) => {
        pub fn $n(x: $t, y: $t) -> $t {
            use ::std::num::Wrapping;
            use std::ops::Rem;
            precondition!(y != 0);
            precondition!(x != $m || y != -1);
            Wrapping(x).rem(Wrapping(y)).0
        }
    };
}

macro_rules! unchecked_sub {
    ($t:ty, $n:ident, $m:expr ) => {
        pub fn $n(x: $t, y: $t) -> $t {
            use ::std::num::Wrapping;
            use std::ops::Sub;
            precondition!(Wrapping(x as i128).sub(Wrapping(y as i128)).0 >= 0);
            precondition!(Wrapping(x as i128).sub(Wrapping(y as i128)).0 <= ($m as i128));
            Wrapping(x).sub(Wrapping(y)).0
        }
    };
}

macro_rules! wrapping_add {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(a: $t, b: $t) -> $tt {
            use ::std::num::Wrapping;
            use std::ops::Add;
            use std::ops::Rem;
            Wrapping(a as $tt)
                .add(Wrapping(b as $tt))
                .rem(Wrapping($m as $tt).add(Wrapping::<$tt>(1)))
                .0
        }
    };
}

macro_rules! wrapping_mul {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(a: $t, b: $t) -> $tt {
            use ::std::num::Wrapping;
            use ::std::ops::Mul;
            use std::ops::Add;
            use std::ops::Rem;
            Wrapping(a as $tt)
                .mul(Wrapping(b as $tt))
                .rem(Wrapping($m as $tt).add(Wrapping::<$tt>(1)))
                .0
        }
    };
}

macro_rules! wrapping_sub {
    ($t:ty, $tt:ty, $n:ident, $m:expr ) => {
        pub fn $n(a: $t, b: $t) -> $t {
            use ::std::num::Wrapping;
            use ::std::ops::Sub;
            use std::ops::Add;
            use std::ops::Rem;
            Wrapping(a as $tt)
                .sub(Wrapping(b as $tt))
                .rem(Wrapping($m as $tt).add(Wrapping::<$tt>(1)))
                .0 as $t
        }
    };
}
