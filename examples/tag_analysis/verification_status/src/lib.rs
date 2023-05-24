// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

// This is an example of using tag analysis to record verification status of objects.
// The code is extracted from a blockchain codebase.

#![cfg_attr(mirai, allow(incomplete_features), feature(generic_const_exprs))]

#[macro_use]
extern crate mirai_annotations;

#[cfg(mirai)]
use mirai_annotations::{TagPropagation, TagPropagationSet};

#[cfg(mirai)]
struct VerifiedKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const VERIFIED_MASK: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

#[cfg(mirai)]
type Verified = VerifiedKind<VERIFIED_MASK>;
#[cfg(not(mirai))]
type Verified = ();

/// VoteMsg is the structure sent by the voter in response for receiving a proposal.
pub struct VoteMsg {
    vote: i32,
    sync_info: bool,
}

impl VoteMsg {
    pub fn new(vote: i32, sync_info: bool) -> Self {
        VoteMsg { vote, sync_info }
    }

    pub fn verify(&self) -> Option<()> {
        let flag = self.vote % 2 == 0;
        if flag == self.sync_info {
            add_tag!(self, Verified);
            Some(())
        } else {
            None
        }
    }
}

/// Networking support for all consensus messaging.
pub struct NetworkSender {
    author: String,
}

impl NetworkSender {
    pub fn new(author: String) -> Self {
        NetworkSender { author }
    }

    pub fn author(&self) -> &String {
        &self.author
    }

    /// Send the vote to the chosen recipients.
    pub fn send_vote(&self, vote_msg: VoteMsg, _recipients: Vec<String>) {
        self.check_internal(vote_msg);
        //precondition!(has_tag!(&vote_msg, crate::Verified));
    }

    fn check_internal(&self, vote_msg: VoteMsg) {
        precondition!(has_tag!(&vote_msg, crate::Verified));
    }
}

pub mod unverified_objects {
    pub fn test_unverified_msg() {
        let sender = crate::NetworkSender::new("Alice".to_owned());
        let msg = crate::VoteMsg::new(123, true);
        sender.send_vote(msg, vec!["Bob".to_owned()]); //~ unsatisfied precondition
    }
}

pub mod verified_objects {
    pub fn tes_verified_msg() {
        let sender = crate::NetworkSender::new("Alice".to_owned());
        let msg = crate::VoteMsg::new(122, true);
        if let Some(()) = msg.verify() {
            sender.send_vote(msg, vec!["Bob".to_owned()]);
        }
    }
}
