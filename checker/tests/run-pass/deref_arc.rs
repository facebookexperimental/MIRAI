// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that dereferences an Arc

use mirai_annotations::*;

use std::sync::Arc;

pub type Round = u64;

pub struct Block {
    round: Round,
}

impl Block {
    pub fn round(&self) -> Round {
        let result = self.round;
        result
    }

    pub fn voting_rule(&mut self, proposed_block: Arc<Block>) {
        if proposed_block.round() <= self.round() {
            return;
        }
        verify!(proposed_block.round() > self.round());
    }
}

pub fn main() {}
