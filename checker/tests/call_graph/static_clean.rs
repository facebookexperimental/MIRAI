// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Linear call graph with static calls, single type, no dominance, no loops.
// Orphan function (unconnected to call graph from main) should be removed 
// by the "Clean" reduction.

pub fn orphan(x: u32) -> u32 {
    x
}
fn fn1(x: u32) -> u32 {
    fn2(x)
}
fn fn2(x: u32) -> u32 {
    fn3(x)
}
fn fn3(x: u32) -> u32 {
    x
}
pub fn main() {
    let x = 1;
    fn1(x);
}

/* CONFIG
{
    "reductions": ["Clean"],
    "included_crates": []
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"static_clean::main\"" ]
    1 [ label = "\"static_clean::fn1\"" ]
    2 [ label = "\"static_clean::fn2\"" ]
    3 [ label = "\"static_clean::fn3\"" ]
    0 -> 1 [ ]
    1 -> 2 [ ]
    2 -> 3 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Edge(0,0,1);
insert Edge(1,1,2);
insert Edge(2,2,3);
insert EdgeType(0,0);
insert EdgeType(1,0);
insert EdgeType(2,0);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "u32"
}
*/
