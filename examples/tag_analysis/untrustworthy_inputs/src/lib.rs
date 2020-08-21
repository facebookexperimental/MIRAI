// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree

// This is an example of using tag analysis to track untrustworthy inputs.
// The code is extracted from a crate for public-key cryptography.

#![cfg_attr(mirai, allow(incomplete_features), feature(const_generics))]

#[macro_use]
extern crate mirai_annotations;

use core::convert::TryFrom;
#[cfg(mirai)]
use mirai_annotations::{TagPropagation, TagPropagationSet};

#[cfg(mirai)]
struct TaintedKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const TAINTED_MASK: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

#[cfg(mirai)]
type Tainted = TaintedKind<TAINTED_MASK>;
#[cfg(not(mirai))]
type Tainted = ();

#[cfg(mirai)]
struct SanitizedKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const SANITIZED_MASK: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

#[cfg(mirai)]
type Sanitized = SanitizedKind<SANITIZED_MASK>;
#[cfg(not(mirai))]
type Sanitized = ();

/// A structure for public keys.
pub struct PublicKey(u32);

/// A public key that we already know is valid. This key does not have the Tainted tag.
pub const A_VALID_PUBLIC_KEY: PublicKey = PublicKey(999213123u32);

impl PublicKey {
    /// Deserialize a public key without any validation checks.
    fn from_bytes_unchecked(bytes: &[u8]) -> Result<PublicKey, &'static str> {
        if bytes.len() != 4 {
            Err("wrong length")
        } else {
            let key = PublicKey(
                u32::from(bytes[0])
                    | u32::from(bytes[1]) << 8
                    | u32::from(bytes[2]) << 16
                    | u32::from(bytes[3]) << 24,
            );
            add_tag!(&key, Tainted);
            Ok(key)
        }
    }
}

impl TryFrom<&[u8]> for PublicKey {
    type Error = &'static str;

    /// Deserialize a public key. This method will also check for key validity.
    fn try_from(bytes: &[u8]) -> Result<PublicKey, Self::Error> {
        match PublicKey::from_bytes_unchecked(bytes) {
            Err(msg) => Err(msg),
            Ok(key) => {
                if bytes[0] == 213 || bytes[2] == 166 {
                    return Err("small subgroup");
                }

                add_tag!(&key, Sanitized);
                Ok(key)
            }
        }
    }
}

pub mod untrustworthy_public_keys {
    pub fn test_unchecked_public_key(bytes: &[u8]) {
        if let Ok(key) = crate::PublicKey::from_bytes_unchecked(bytes) {
            verify!(does_not_have_tag!(&key, crate::Tainted) || has_tag!(&key, crate::Sanitized));
            //~ provably false verification condition
        }
    }
}

pub mod verified_public_keys {
    use core::convert::TryFrom;

    pub fn test_checked_public_key(bytes: &[u8]) {
        let key = match crate::PublicKey::try_from(bytes) {
            Err(..) => crate::A_VALID_PUBLIC_KEY,
            Ok(key) => key,
        };
        verify!(does_not_have_tag!(&key, crate::Tainted) || has_tag!(&key, crate::Sanitized));
    }
}
