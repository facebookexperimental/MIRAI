// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Call graph with static calls, single type, dominance, and a loop.

fn fn1(x: u32) -> u32 {
    let y = fn2(x);
    fn3(y)
}
fn fn2(x: u32) -> u32 {
    x
}
fn fn3(x: u32) -> u32 {
    fn4(x)
}
fn fn4(x: u32) -> u32 {
    if x > 1 {
        fn1(x - 1)
    } else {
        x
    }
}
pub fn main() {
    let x = 3;
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
    0 [ label = "\"static_dom_loop[8787]::main\"" ]
    1 [ label = "\"static_dom_loop[8787]::fn1\"" ]
    2 [ label = "\"static_dom_loop[8787]::fn2\"" ]
    3 [ label = "\"static_dom_loop[8787]::fn3\"" ]
    4 [ label = "\"static_dom_loop[8787]::fn4\"" ]
    0 -> 1 [ ]
    1 -> 2 [ ]
    1 -> 3 [ ]
    3 -> 4 [ ]
    4 -> 1 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Dom(2,3);
insert Edge(0,0,1);
insert Edge(1,1,2);
insert Edge(2,1,3);
insert Edge(3,3,4);
insert Edge(4,4,1);
insert EdgeType(0,0);
insert EdgeType(1,0);
insert EdgeType(2,0);
insert EdgeType(3,0);
insert EdgeType(4,0);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "u32"
}
*/
