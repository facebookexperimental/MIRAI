// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use constant_value::ConstantValue;

// See https://github.com/facebookexperimental/MIRAI/blob/master/documentation/AbstractValues.md.

/// A collection of abstract domains associated with a particular abstract value.
/// The expression domain captures the precise expression that resulted in the abstract
/// value. It can be used to derive any other kind of abstract domain on demand.
#[derive(Serialize, Deserialize, Debug, Eq, PartialEq, Hash)]
pub struct AbstractDomains {
    pub expression_domain: ExpressionDomain,
    //todo: use cached getters to get other domains on demand
}

/// The things all abstract domain instances have to be able to do
pub trait AbstractDomain {
    //todo: join, is_top, is_bottom, etc.
}

/// An abstract domain uses a functional (side effect free) expression that precisely tracks
/// a single value.
#[derive(Serialize, Deserialize, Debug, Eq, PartialEq, Hash)]
pub enum ExpressionDomain {
    /// An expression that represents any possible value
    Top,

    /// An expression that represents an impossible value, such as the value returned by function
    /// that always panics.
    Bottom,

    /// An expression that is a compile time constant value, such as a numeric literal or a
    /// function.
    CompileTimeConstant(ConstantValue),
}

// todo: implement the AbstractDomain trait for ExpressionDomain
