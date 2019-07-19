#[macro_use]
extern crate mirai_annotations;

pub struct Block {
    round: u64,
}

impl Block {
    pub fn round(&self) -> u64 {
        postcondition!(self.round < std::u64::MAX - 2); //~ possible unsatisfied postcondition
        self.round
    }
}

pub fn voting_rule(proposed_block: Block) -> () {
    let _ret = proposed_block.round();
    verify!(_ret < std::u64::MAX); //~ possible false verification condition
}

pub fn main() {}
