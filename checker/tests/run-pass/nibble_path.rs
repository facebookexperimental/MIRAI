// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that checks that inferred preconditions with disjunctions can be promoted.

// MIRAI_FLAGS --diag=verify

pub struct Nibble(u8);

impl From<u8> for Nibble {
    fn from(nibble: u8) -> Self {
        assert!(nibble < 16, "Nibble out of range: {}", nibble);
        Self(nibble)
    }
}

#[derive(Clone)]
pub struct NibblePath {
    /// Indicates the total number of nibbles in bytes. Either `bytes.len() * 2 - 1` or
    /// `bytes.len() * 2`.
    // Guarantees intended ordering based on the top-to-bottom declaration order of the struct's
    // members.
    num_nibbles: usize,
    /// The underlying bytes that stores the path, 2 nibbles per byte. If the number of nibbles is
    /// odd, the second half of the last byte must be 0.
    bytes: Vec<u8>,
    // invariant num_nibbles <= ROOT_NIBBLE_HEIGHT
}

impl NibblePath {
    pub fn pop(&mut self) -> Option<Nibble> {
        let popped_nibble = if self.num_nibbles % 2 == 0 {
            self.bytes.last_mut().map(|last_byte| {
                let nibble = *last_byte & 0x0f;
                *last_byte &= 0xf0;
                Nibble::from(nibble)
            })
        } else {
            self.bytes.pop().map(|byte| Nibble::from(byte >> 4))
        };
        if popped_nibble.is_some() {
            //todo: fix this
            //self.num_nibbles -= 1;
        }
        popped_nibble
    }
}

pub struct NodeKey {
    // The version at which the node is created.
    //version: Version,
    // The nibble path this node represents in the tree.
    nibble_path: NibblePath,
}

impl NodeKey {
    pub fn gen_parent_node_key(&self) {
        let mut node_nibble_path = self.nibble_path.clone();
        let _x = node_nibble_path.pop();
    }
}

pub fn main() {}
