// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Linear call graph with single type, no dominance, no loops.

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
    "reductions": [],
    "included_crates": []
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"static[8787]::main\"" ]
    1 [ label = "\"static[8787]::fn1\"" ]
    2 [ label = "\"static[8787]::fn2\"" ]
    3 [ label = "\"static[8787]::fn3\"" ]
    0 -> 1 [ ]
    1 -> 2 [ ]
    2 -> 3 [ ]
}
*/

/* EXPECTED:DDLOG
start;
Edge(0,0,1);
Edge(1,1,2);
Edge(2,2,3);
EdgeType(0,0);
EdgeType(1,0);
EdgeType(2,0);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "u32"
}
*/
