#[macro_use]
extern crate mirai_annotations;

pub struct Block {
    round: u64,
}

pub fn round(bl: Block) -> u64 {
    assume!(bl.round < std::u64::MAX - 1);
    bl.round
}

pub fn foo(bl: Block) {
    let ret = round(bl);
    verify!(ret < std::u64::MAX - 1);
}

pub fn main() {}
