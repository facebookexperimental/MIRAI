// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// A test that has two nested functions that both have the same qualified name if not
// disambiguated with a counter.

#![allow(unused)]

fn test() { { fn bar() {} } { fn bar() {} } }