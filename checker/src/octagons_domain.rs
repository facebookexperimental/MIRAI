// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

use crate::expression::ExpressionType::{self, *};

use log_derive::logfn_inputs;
use serde::{Deserialize, Serialize};
use std::cmp;
use std::convert::TryFrom;

#[derive(Serialize, Deserialize, Clone, Eq, PartialOrd, PartialEq, Hash, Ord)]
pub struct OctagonsDomain {
    x: i128,
    y: i128,
    c: i64, // is that correct?
}

impl std::fmt::Debug for OctagonsDomain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("octagons are here"))
    }
}


