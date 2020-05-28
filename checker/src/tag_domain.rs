// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::bool_domain::BoolDomain;

use log_derive::logfn_inputs;
use mirai_annotations::TagPropagationSet;
use rpds::{rbt_map, RedBlackTreeMap};
use rustc_hir::def_id::DefId;

/// A tag is represented as a pair of its tag kind and its control mask.
/// The tag kind is the name of the declared tag type, and the control mask is associated to the
/// tag type as a const generic parameter.
pub type Tag = (DefId, TagPropagationSet);

/// An element of the tag domain is essentially an over-approximation for present and absent tags.
/// The approximation is denoted as a map from tags to lifted Boolean values (`BoolDomain`).
/// If a tag is mapped to `True`, then it must be present.
/// If a tag is mapped to `False', then it must be absent.
/// If a tag is mapped to `Top`, then it may or may not be present.
#[derive(Ord, PartialOrd, Eq, PartialEq, Debug, Clone)]
pub struct TagDomain {
    map: RedBlackTreeMap<Tag, BoolDomain>,
}

/// Constructors
impl TagDomain {
    /// Construct a tag domain element representing an empty set.
    #[logfn_inputs(TRACE)]
    pub fn for_empty_set() -> TagDomain {
        TagDomain { map: rbt_map![] }
    }
}

/// Transfer functions
impl TagDomain {
    /// Return a new tag domain element by adding the `tag` whose presence is indicated by `val`.
    pub fn add_tag(&self, tag: Tag, val: BoolDomain) -> Self {
        TagDomain {
            map: self.map.insert(tag, val),
        }
    }

    /// Return a lifted Boolean that indicates the presence of `tag` in the tag domain element.
    pub fn has_tag(&self, tag: &Tag) -> BoolDomain {
        *self.map.get(tag).unwrap_or(&BoolDomain::False)
    }
}
