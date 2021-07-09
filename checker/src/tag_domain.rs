// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::bool_domain::BoolDomain;

use log_derive::*;
use mirai_annotations::*;
use rpds::{rbt_map, RedBlackTreeMap};
use rustc_hir::def_id::{CrateNum, DefId, DefIndex};
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};

/// A replication of the `DefId` type from rustc. The type is used to implement serialization.
#[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Hash)]
pub struct SerializableDefId {
    pub krate: CrateNum,
    pub index: DefIndex,
}

impl From<DefId> for SerializableDefId {
    fn from(did: DefId) -> SerializableDefId {
        SerializableDefId {
            krate: did.krate,
            index: did.index,
        }
    }
}

impl std::fmt::Debug for SerializableDefId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{:?}",
            DefId {
                krate: self.krate,
                index: self.index
            }
        ))
    }
}

impl Serialize for SerializableDefId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let krate = u64::from(self.krate.as_u32());
        let index = u64::from(self.index.as_u32());
        serializer.serialize_u64((krate << 32) | index)
    }
}

impl<'de> Deserialize<'de> for SerializableDefId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct U64Visitor;

        impl<'de> de::Visitor<'de> for U64Visitor {
            type Value = u64;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("u64")
            }

            fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
            where
                E: de::Error,
            {
                Ok(value)
            }
        }

        let def_id = deserializer.deserialize_u64(U64Visitor)?;
        let krate = CrateNum::from_u32((def_id >> 32) as u32);
        let index = DefIndex::from_u32((def_id & 0xffffffff) as u32);
        Ok(SerializableDefId { krate, index })
    }
}

/// A tag is represented as a pair of its tag kind and its propagation set.
/// The tag kind is the name of the declared tag type, and the propagation set is associated to the
/// tag type as a const generic parameter.
#[derive(Ord, PartialOrd, Eq, PartialEq, Debug, Copy, Clone, Serialize, Deserialize, Hash)]
pub struct Tag {
    pub def_id: SerializableDefId,
    pub prop_set: TagPropagationSet,
}

impl Tag {
    /// Check if a value of enum type `TagPropagation` is included in `self`'s propagation set.
    #[logfn_inputs(TRACE)]
    pub fn is_propagated_by(&self, exp_tag_prop: TagPropagation) -> bool {
        precondition!((exp_tag_prop as u8) < 128);
        self.prop_set & (1 << (exp_tag_prop as u8)) != 0
    }
}

/// The Tag domain implements an abstraction for the Expression domain. A tag is attached to an
/// operand via `TaggedExpression { tag, operand }`, and tags cannot be removed once attached.
///
/// The concrete semantics for tags of an expression `E` is a set of tags collected from `E`'s
/// sub-expressions of the form `TaggedExpression { tag, .. }`, filtered by some propagation rules.
/// The propagation is done in a bottom-up manner: An expression asks its children nodes for their
/// collections of tags, and then this expression filters some tags *out*, depending on both the
/// expression kind and the tag kind. For example, let's construct the set of tags for `E1+E2`,
/// where `E1` has tag `A` and `C`, `E2` has tag `B` and `D`. Suppose that addition propagates
/// `A` and `B`, but blocks `C` and `D`. As a result, `E1+E2` will have tag `A` and `B`.
/// The propagation is controlled by the `prop_set` field of the `Tag` type.
///
/// The Tag domain implements an abstraction for the tag semantics with a compact representation.
/// To start with, we can represent the concrete semantics of tags as a finite map from tag names
/// to Booleans, i.e., we represent sets as Boolean-valued maps. For example, suppose that in total
/// we have 3 tags `A`, `B`, and `C`. Then the set {`A`, `B`} is represented as {`A` -> true, `B`
/// -> true, `C` -> false}. By abstract interpretation, an abstract tag domain element should
/// represent a set of such Boolean-valued maps. We implement a coarser abstraction in MIRAI.
/// Noticing that tags are independent of each other, we define the abstraction as the Cartesian
/// product of abstractions for each tag. In the concrete semantics, for each tag, we record a
/// Boolean value; thus, in the abstract semantics, for each tag, we record a *lifted* Boolean:
/// TOP={true,false} indicates that the tag *may* exist, TRUE={true} indicates that the tag *must*
/// exist, FALSE={false} indicates that the tag *must not* exist, and BOTTOM={} indicates an
/// impossible state. A Tag domain element is then a finite map from tag names to lifted Booleans.
///
/// However, MIRAI constructs abstract domain elements on demand, so MIRAI does not know the whole
/// set of tags during an analysis. Our solution is to *lazily* record tags in a Tag domain element.
/// We implement the finite maps using Map data structures (specifically, persistent tree maps).
/// Intuitively, if a tag is not tracked by a Tag domain element, i.e., it is not in the support of
/// the finite map, we would like to assume the tag is absent. This works perfectly for intra-
/// procedural analysis, because local variables don't have any tags initially. However, if an
/// expression `E` is a path rooted at a function parameter, in the tag abstraction of `E`, we
/// need to map every tag to TOP which means that we don't know yet if the tag exists or not,
/// and the tag check result could be refined later when MIRAI has more information from the caller.
/// Again, because MIRAI works on demand, we don't know the whole set of tags. We add a field
/// `value_for_untracked_tags` in Tag domain elements to record a lifted Boolean for untracked
/// tags. For example, in the tag abstraction of a local variable, this field is FALSE, while
/// in the tag abstraction of a function parameter, this field is TOP.
#[derive(Ord, PartialOrd, Eq, PartialEq, Debug, Clone, Serialize, Deserialize)]
pub struct TagDomain {
    map: RedBlackTreeMap<Tag, BoolDomain>,
    value_for_untracked_tags: BoolDomain,
}

/// Constructors
impl TagDomain {
    /// Construct a tag domain element representing an empty set of tags.
    /// In other words, the tag domain element maps every tag to False.
    #[logfn_inputs(TRACE)]
    pub fn empty_set() -> TagDomain {
        TagDomain {
            map: rbt_map![],
            value_for_untracked_tags: BoolDomain::False,
        }
    }

    /// Construct the most coarse tag domain element where all tags can be either
    /// present or absent. In other words, the tag domain element maps every tag to Top.
    #[logfn_inputs(TRACE)]
    pub fn top() -> TagDomain {
        TagDomain {
            map: rbt_map![],
            value_for_untracked_tags: BoolDomain::Top,
        }
    }
}

/// Transfer functions
impl TagDomain {
    /// Return a new tag domain element by setting `tag` to True in `self`.
    #[logfn_inputs(TRACE)]
    pub fn add_tag(&self, tag: Tag) -> Self {
        TagDomain {
            map: self.map.insert(tag, BoolDomain::True),
            value_for_untracked_tags: self.value_for_untracked_tags,
        }
    }

    /// Return a lifted Boolean that indicates the presence of `tag` in the tag domain element.
    #[logfn_inputs(TRACE)]
    pub fn has_tag(&self, tag: &Tag) -> BoolDomain {
        *self.map.get(tag).unwrap_or(&self.value_for_untracked_tags)
    }

    /// Return the pointwise logical-or of two tag domain elements.
    #[logfn_inputs(TRACE)]
    pub fn or(&self, other: &Self) -> Self {
        let mut new_map = rbt_map![];
        for tag in self.map.keys().chain(other.map.keys()) {
            let self_val = self.map.get(tag).unwrap_or(&self.value_for_untracked_tags);
            let other_val = other
                .map
                .get(tag)
                .unwrap_or(&other.value_for_untracked_tags);
            let new_val = self_val.or(other_val);
            new_map.insert_mut(*tag, new_val);
        }
        TagDomain {
            map: new_map,
            value_for_untracked_tags: self
                .value_for_untracked_tags
                .or(&other.value_for_untracked_tags),
        }
    }

    /// Return the pointwise join of two tag domain elements.
    #[logfn_inputs(TRACE)]
    pub fn join(&self, other: &Self) -> Self {
        let mut new_map = rbt_map![];
        for tag in self.map.keys().chain(other.map.keys()) {
            let self_val = self.map.get(tag).unwrap_or(&self.value_for_untracked_tags);
            let other_val = other
                .map
                .get(tag)
                .unwrap_or(&other.value_for_untracked_tags);
            let new_val = self_val.join(other_val);
            new_map.insert_mut(*tag, new_val);
        }
        TagDomain {
            map: new_map,
            value_for_untracked_tags: self
                .value_for_untracked_tags
                .join(&other.value_for_untracked_tags),
        }
    }

    /// Return a tag domain element that filters out tags which are not propagated by an expression.
    /// The expression kind is identified by `exp_tag_prop`.
    #[logfn_inputs(TRACE)]
    pub fn propagate_through(&self, exp_tag_prop: TagPropagation) -> Self {
        let new_map: RedBlackTreeMap<Tag, BoolDomain> = self
            .map
            .iter()
            .map(|(tag, val)| {
                if tag.is_propagated_by(exp_tag_prop) {
                    (*tag, *val)
                } else {
                    // If this expression blocks the tag, the tag will be mapped to False after
                    // the propagation.
                    (*tag, BoolDomain::False)
                }
            })
            .collect();
        TagDomain {
            map: new_map,
            // For untracked tags, we don't know their propagation sets, so either these tags
            // are filtered out (mapped to False), or they are not influenced (mapped to `value_for_untracked_tags`).
            // For example, if the untracked tags were mapped to False, then after propagation, they are
            // still mapped to False. Otherwise, if they were mapped to True or Top, then after propagation,
            // they need to be mapped to Top.
            value_for_untracked_tags: self.value_for_untracked_tags.join(&BoolDomain::False),
        }
    }
}
