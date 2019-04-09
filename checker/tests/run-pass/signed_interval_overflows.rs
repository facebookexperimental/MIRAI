// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests arithmetic binary operations that overflow

pub fn ti8_add_overflows(cond: bool) -> i8 {
    let a: i8 = if cond { 0x7F } else { 1 };
    a + 1 //~ possible attempt to add with overflow
}

pub fn ti8_add_safe(cond: bool) -> i8 {
    let a: i8 = if cond { 0x7E } else { 1 };
    a + 1
}

pub fn ti8_mul_overflows(cond: bool) -> i8 {
    let a: i8 = if cond { 0x40 } else { 1 };
    a * 2 //~ possible attempt to multiply with overflow
}

pub fn ti8_mul_safe(cond: bool) -> i8 {
    let a: i8 = if cond { 0x3F } else { 1 };
    a * 2
}

pub fn ti8_sub_overflows(cond: bool) -> i8 {
    let a: i8 = if cond { -128i8 } else { 0 };
    a - 1 //~ possible attempt to subtract with overflow
}

pub fn ti8_sub_safe(cond: bool) -> i8 {
    let a: i8 = if cond { -127i8 } else { 0 };
    a - 1
}

pub fn ti8_shl_overflows(cond: bool) -> i8 {
    let a: i8 = if cond { 8 } else { 1 };
    a << a //~ possible attempt to shift left with overflow
}

pub fn ti8_shl_safe(cond: bool) -> i8 {
    let a: i8 = if cond { 7 } else { 1 };
    a << a
}

pub fn ti8_shr_overflows(cond: bool) -> i8 {
    let a: i8 = if cond { 8 } else { 1 };
    a >> a //~ possible attempt to shift right with overflow
}

pub fn ti8_shr_safe(cond: bool) -> i8 {
    let a: i8 = if cond { 7 } else { 1 };
    a >> a
}

pub fn ti16_add_overflows(cond: bool) -> i16 {
    let a: i16 = if cond { 0x7FFF } else { 1 };
    a + 1 //~ possible attempt to add with overflow
}

pub fn ti16_add_safe(cond: bool) -> i16 {
    let a: i16 = if cond { 0x7FFE } else { 1 };
    a + 1
}

pub fn ti16_mul_overflows(cond: bool) -> i16 {
    let a: i16 = if cond { 0x4000 } else { 1 };
    a * 2 //~ possible attempt to multiply with overflow
}

pub fn ti16_mul_safe(cond: bool) -> i16 {
    let a: i16 = if cond { 0x3FFF } else { 1 };
    a * 2
}

pub fn ti16_sub_overflows(cond: bool) -> i16 {
    let a: i16 = if cond { -32768i16 } else { 0 };
    a - 1 //~ possible attempt to subtract with overflow
}

pub fn ti16_sub_safe(cond: bool) -> i16 {
    let a: i16 = if cond { -32767i16 } else { 0 };
    a - 1
}

pub fn ti16_shl_overflows(cond: bool) -> i16 {
    let a: i16 = if cond { 16 } else { 1 };
    a << a //~ possible attempt to shift left with overflow
}

pub fn ti16_shl_safe(cond: bool) -> i16 {
    let a: i16 = if cond { 15 } else { 1 };
    a << a
}

pub fn ti16_shr_overflows(cond: bool) -> i16 {
    let a: i16 = if cond { 16 } else { 1 };
    a >> a //~ possible attempt to shift right with overflow
}

pub fn ti16_shr_safe(cond: bool) -> i16 {
    let a: i16 = if cond { 15 } else { 1 };
    a >> a
}

pub fn ti32_add_overflows(cond: bool) -> i32 {
    let a: i32 = if cond { 0x7FFFFFFF } else { 1 };
    a + 1 //~ possible attempt to add with overflow
}

pub fn ti32_add_safe(cond: bool) -> i32 {
    let a: i32 = if cond { 0x7FFFFFFE } else { 1 };
    a + 1
}

pub fn ti32_mul_overflows(cond: bool) -> i32 {
    let a: i32 = if cond { 0x40000000 } else { 1 };
    a * 2 //~ possible attempt to multiply with overflow
}

pub fn ti32_mul_safe(cond: bool) -> i32 {
    let a: i32 = if cond { 0x3FFFFFFF } else { 1 };
    a * 2
}

pub fn ti32_sub_overflows(cond: bool) -> i32 {
    let a: i32 = if cond { -2147483648i32 } else { 0 };
    a - 1 //~ possible attempt to subtract with overflow
}

pub fn ti32_sub_safe(cond: bool) -> i32 {
    let a: i32 = if cond { -2147483647i32 } else { 1 };
    a - 1
}

pub fn ti32_shl_overflows(cond: bool) -> i32 {
    let a: i32 = if cond { 32 } else { 1 };
    a << a //~ possible attempt to shift left with overflow
}

pub fn ti32_shl_safe(cond: bool) -> i32 {
    let a: i32 = if cond { 31 } else { 1 };
    a << a
}

pub fn ti32_shr_overflows(cond: bool) -> i32 {
    let a: i32 = if cond { 32 } else { 1 };
    a >> a //~ possible attempt to shift right with overflow
}

pub fn ti32_shr_safe(cond: bool) -> i32 {
    let a: i32 = if cond { 31 } else { 1 };
    a >> a
}

pub fn ti64_add_overflows(cond: bool) -> i64 {
    let a: i64 = if cond { 0x7FFFFFFFFFFFFFFF } else { 1 };
    a + 1 //~ possible attempt to add with overflow
}

pub fn ti64_add_safe(cond: bool) -> i64 {
    let a: i64 = if cond { 0x7FFFFFFFFFFFFFFE } else { 1 };
    a + 1
}

pub fn ti64_mul_overflows(cond: bool) -> i64 {
    let a: i64 = if cond { 0x4000000000000000 } else { 1 };
    a * 2 //~ possible attempt to multiply with overflow
}

pub fn ti64_mul_safe(cond: bool) -> i64 {
    let a: i64 = if cond { 0x3FFFFFFFFFFFFFFF } else { 1 };
    a * 2
}

pub fn ti64_sub_overflows(cond: bool) -> i64 {
    let a: i64 = if cond { -9223372036854775808i64 } else { 0 };
    a - 1 //~ possible attempt to subtract with overflow
}

pub fn ti64_sub_safe(cond: bool) -> i64 {
    let a: i64 = if cond { -9223372036854775807i64 } else { 0 };
    a - 1
}

pub fn ti64_shl_overflows(cond: bool) -> i64 {
    let a: i64 = if cond { 64 } else { 1 };
    a << a //~ possible attempt to shift left with overflow
}

pub fn ti64_shl_safe(cond: bool) -> i64 {
    let a: i64 = if cond { 63 } else { 1 };
    a << a
}

pub fn ti64_shr_overflows(cond: bool) -> i64 {
    let a: i64 = if cond { 64 } else { 1 };
    a >> a //~ possible attempt to shift right with overflow
}

pub fn ti64_shr_safe(cond: bool) -> i64 {
    let a: i64 = if cond { 63 } else { 1 };
    a >> a
}

// Interval domains can only represent finite intervals contained in [i128::MIN+1, ..., i128::MAX-1]
// Z3 is more precise, though.

pub fn ti128_add_overflows(cond: bool) -> i128 {
    let a: i128 = if cond {
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    } else {
        1
    };
    a + 1 //~ possible attempt to add with overflow
}

pub fn ti128_add_safe_ze3(cond: bool) -> i128 {
    let a: i128 = if cond {
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    } else {
        1
    };
    a + 1
}

pub fn ti128_add_safe(cond: bool) -> i128 {
    let a: i128 = if cond {
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC
    } else {
        1
    };
    a + 1
}

pub fn ti128_mul_overflows(cond: bool) -> i128 {
    let a: i128 = if cond {
        0x40000000000000000000000000000000
    } else {
        1
    };
    a * 2 //~ possible attempt to multiply with overflow
}

pub fn ti128_mul_safe(cond: bool) -> i128 {
    let a: i128 = if cond {
        0x3FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    } else {
        1
    };
    a * 2
}

pub fn ti128_sub_overflows(cond: bool) -> i128 {
    let a: i128 = if cond {
        -170141183460469231731687303715884105728i128
    } else {
        0
    };
    a - 1 //~ possible attempt to subtract with overflow
}

pub fn ti128_sub_safe(cond: bool) -> i128 {
    let a: i128 = if cond {
        -170141183460469231731687303715884105727i128
    } else {
        0
    };
    a - 1
}

pub fn ti128_shl_overflows(cond: bool) -> i128 {
    let a: i128 = if cond { 128 } else { 1 };
    a << a //~ possible attempt to shift left with overflow
}

pub fn ti128_shl_safe(cond: bool) -> i128 {
    let a: i128 = if cond { 127 } else { 1 };
    a << a
}

pub fn ti128_shr_overflows(cond: bool) -> i128 {
    let a: i128 = if cond { 128 } else { 1 };
    a >> a //~ possible attempt to shift right with overflow
}

pub fn ti128_shr_safe(cond: bool) -> i128 {
    let a: i128 = if cond { 127 } else { 1 };
    a >> a
}
