// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use mirai_annotations::*;

pub struct Block {
    round: u64,
}

impl Block {
    fn round(&self) -> u64 {
        postcondition!(self.round < std::u64::MAX - 2); //~ possible unsatisfied postcondition
        self.round
    }

    pub fn voting_rule(proposed_block: Block) -> () {
        let _ret = proposed_block.round();
        verify!(_ret < std::u64::MAX); // verifies because the post condition is assumed here.
    }
}

pub fn main() {}
