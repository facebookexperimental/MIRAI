// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Tests arithmetic binary operations that overflow

pub fn tu8_add_overflows(cond: bool) -> u8 {
    let a: u8 = if cond { 0xFF } else { 1 };
    a + 1 //~ possible attempt to add with overflow
}

pub fn tu8_add_safe(cond: bool) -> u8 {
    let a: u8 = if cond { 0xFE } else { 1 };
    a + 1
}

pub fn tu8_mul_overflows(cond: bool) -> u8 {
    let a: u8 = if cond { 0x80 } else { 1 };
    a * 2 //~ possible attempt to multiply with overflow
}

pub fn tu8_mul_safe(cond: bool) -> u8 {
    let a: u8 = if cond { 0x7F } else { 1 };
    a * 2
}

pub fn tu8_sub_overflows(cond: bool) -> u8 {
    let a: u8 = if cond { 1 } else { 0 };
    a - 2 //~ attempt to subtract with overflow
}

pub fn tu8_sub_safe(cond: bool) -> u8 {
    let a: u8 = if cond { 2 } else { 1 };
    a - 1
}

pub fn tu8_shl_overflows(cond: bool) -> u8 {
    let a: u8 = if cond { 8 } else { 1 };
    a << a //~ possible attempt to shift left with overflow
}

pub fn tu8_shl_safe(cond: bool) -> u8 {
    let a: u8 = if cond { 7 } else { 1 };
    a << a
}

pub fn tu8_shr_overflows(cond: bool) -> u8 {
    let a: u8 = if cond { 8 } else { 1 };
    a >> a //~ possible attempt to shift right with overflow
}

pub fn tu8_shr_safe(cond: bool) -> u8 {
    let a: u8 = if cond { 7 } else { 1 };
    a >> a
}

pub fn tu16_add_overflows(cond: bool) -> u16 {
    let a: u16 = if cond { 0xFFFF } else { 1 };
    a + 1 //~ possible attempt to add with overflow
}

pub fn tu16_add_safe(cond: bool) -> u16 {
    let a: u16 = if cond { 0xFFFE } else { 1 };
    a + 1
}

pub fn tu16_mul_overflows(cond: bool) -> u16 {
    let a: u16 = if cond { 0x8000 } else { 1 };
    a * 2 //~ possible attempt to multiply with overflow
}

pub fn tu16_mul_safe(cond: bool) -> u16 {
    let a: u16 = if cond { 0x7FFF } else { 1 };
    a * 2
}

pub fn tu16_sub_overflows(cond: bool) -> u16 {
    let a: u16 = if cond { 1 } else { 0 };
    a - 2 //~ attempt to subtract with overflow
}

pub fn tu16_sub_safe(cond: bool) -> u16 {
    let a: u16 = if cond { 2 } else { 1 };
    a - 1
}

pub fn tu16_shl_overflows(cond: bool) -> u16 {
    let a: u16 = if cond { 16 } else { 1 };
    a << a //~ possible attempt to shift left with overflow
}

pub fn tu16_shl_safe(cond: bool) -> u16 {
    let a: u16 = if cond { 15 } else { 1 };
    a << a
}

pub fn tu16_shr_overflows(cond: bool) -> u16 {
    let a: u16 = if cond { 16 } else { 1 };
    a >> a //~ possible attempt to shift right with overflow
}

pub fn tu16_shr_safe(cond: bool) -> u16 {
    let a: u16 = if cond { 15 } else { 1 };
    a >> a
}

pub fn tu32_add_overflows(cond: bool) -> u32 {
    let a: u32 = if cond { 0xFFFFFFFF } else { 1 };
    a + 1 //~ possible attempt to add with overflow
}

pub fn tu32_add_safe(cond: bool) -> u32 {
    let a: u32 = if cond { 0xFFFFFFFE } else { 1 };
    a + 1
}

pub fn tu32_mul_overflows(cond: bool) -> u32 {
    let a: u32 = if cond { 0x80000000 } else { 1 };
    a * 2 //~ possible attempt to multiply with overflow
}

pub fn tu32_mul_safe(cond: bool) -> u32 {
    let a: u32 = if cond { 0x7FFFFFFF } else { 1 };
    a * 2
}

pub fn tu32_sub_overflows(cond: bool) -> u32 {
    let a: u32 = if cond { 1 } else { 0 };
    a - 2 //~ attempt to subtract with overflow
}

pub fn tu32_sub_safe(cond: bool) -> u32 {
    let a: u32 = if cond { 2 } else { 1 };
    a - 1
}

pub fn tu32_shl_overflows(cond: bool) -> u32 {
    let a: u32 = if cond { 32 } else { 1 };
    a << a //~ possible attempt to shift left with overflow
}

pub fn tu32_shl_safe(cond: bool) -> u32 {
    let a: u32 = if cond { 31 } else { 1 };
    a << a
}

pub fn tu32_shr_overflows(cond: bool) -> u32 {
    let a: u32 = if cond { 32 } else { 1 };
    a >> a //~ possible attempt to shift right with overflow
}

pub fn tu32_shr_safe(cond: bool) -> u32 {
    let a: u32 = if cond { 31 } else { 1 };
    a >> a
}

pub fn tu64_add_overflows(cond: bool) -> u64 {
    let a: u64 = if cond { 0xFFFFFFFFFFFFFFFF } else { 1 };
    a + 1 //~ possible attempt to add with overflow
}

pub fn tu64_add_safe(cond: bool) -> u64 {
    let a: u64 = if cond { 0xFFFFFFFFFFFFFFFE } else { 1 };
    a + 1
}

pub fn tu64_mul_overflows(cond: bool) -> u64 {
    let a: u64 = if cond { 0x8000000000000000 } else { 1 };
    a * 2 //~ possible attempt to multiply with overflow
}

pub fn tu64_mul_safe(cond: bool) -> u64 {
    let a: u64 = if cond { 0x7FFFFFFFFFFFFFFF } else { 1 };
    a * 2
}

pub fn tu64_sub_overflows(cond: bool) -> u64 {
    let a: u64 = if cond { 1 } else { 0 };
    a - 2 //~ attempt to subtract with overflow
}

pub fn tu64_sub_safe(cond: bool) -> u64 {
    let a: u64 = if cond { 2 } else { 1 };
    a - 1
}

pub fn tu64_shl_overflows(cond: bool) -> u64 {
    let a: u64 = if cond { 64 } else { 1 };
    a << a //~ possible attempt to shift left with overflow
}

pub fn tu64_shl_safe(cond: bool) -> u64 {
    let a: u64 = if cond { 63 } else { 1 };
    a << a
}

pub fn tu64_shr_overflows(cond: bool) -> u64 {
    let a: u64 = if cond { 64 } else { 1 };
    a >> a //~ possible attempt to shift right with overflow
}

pub fn tu64_shr_safe(cond: bool) -> u64 {
    let a: u64 = if cond { 63 } else { 1 };
    a >> a
}

// Interval domains can only represent finite intervals contained in [i128::MIN+1, ..., i128::MAX-1]
// Z3 is more precise, though.

pub fn tu128_add_overflows(cond: bool) -> u128 {
    let a: u128 = if cond {
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF
    } else {
        1
    };
    a + 1
}

pub fn tu128_add_safe(cond: bool) -> u128 {
    let a: u128 = if cond {
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC
    } else {
        1
    };
    a + 1
}

pub fn tu128_mul_overflows(cond: bool) -> u128 {
    let a: u128 = if cond {
        0x40000000000000000000000000000000
    } else {
        1
    };
    a * 2
}

pub fn tu128_mul_safe(cond: bool) -> u128 {
    let a: u128 = if cond {
        0x3FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE
    } else {
        1
    };
    a * 2
}

pub fn tu128_sub_overflows(cond: bool) -> u128 {
    let a: u128 = if cond { 1 } else { 0 };
    a - 2 //~ attempt to subtract with overflow
}

pub fn tu128_sub_safe(cond: bool) -> u128 {
    let a: u128 = if cond { 2 } else { 1 };
    a - 1
}

pub fn tu128_shl_overflows(cond: bool) -> u128 {
    let a: u128 = if cond { 128 } else { 1 };
    a << a //~ possible attempt to shift left with overflow
}

pub fn tu128_shl_safe(cond: bool) -> u128 {
    let a: u128 = if cond { 127 } else { 1 };
    a << a
}

pub fn tu128_shr_overflows(cond: bool) -> u128 {
    let a: u128 = if cond { 128 } else { 1 };
    a >> a //~ possible attempt to shift right with overflow
}

pub fn tu128_shr_safe(cond: bool) -> u128 {
    let a: u128 = if cond { 127 } else { 1 };
    a >> a
}

pub fn main() {}
