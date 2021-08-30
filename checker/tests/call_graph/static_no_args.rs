// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Test case that ensures that if a static call is made without
// any arguments, an edge *is* added to the call graph.

fn fn1() -> u32 {
    1
}
pub fn main() {
    fn1();
}

/* CONFIG
{
    "reductions": [],
    "included_crates": []
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"static_no_args::main\"" ]
    1 [ label = "\"static_no_args::fn1\"" ]
    0 -> 1 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Edge(0,0,1);
insert EdgeType(0,0);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": ""
}
*/
