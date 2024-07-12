// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Linear call graph with function pointer calls, single type, no dominance, no loops.
// Orphan function (unconnected to call graph from main) should be removed
// by the "Clean" reduction.

pub fn orphan(x: u32) -> u32 {
    x
}
fn fn1(x: u32, fn2: &fn(u32) -> u32) -> u32 {
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
    fn1(x, &(fn2 as fn(u32) -> u32));
}

/* CONFIG
{
    "reductions": ["Clean"],
    "included_crates": [],
    "datalog_config": {
        "datalog_backend": "DifferentialDatalog"
    }
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"fnptr_clean::main\"" ]
    1 [ label = "\"fnptr_clean::fn1\"" ]
    2 [ label = "\"fnptr_clean::fn2\"" ]
    3 [ label = "\"fnptr_clean::fn3\"" ]
    0 -> 1 [ ]
    0 -> 1 [ ]
    1 -> 2 [ ]
    2 -> 3 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Edge(0,0,1);
insert Edge(1,0,1);
insert Edge(2,1,2);
insert Edge(3,2,3);
insert EdgeType(0,0);
insert EdgeType(1,1);
insert EdgeType(2,0);
insert EdgeType(3,0);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "u32",
  "1": "&fn(u32) -> u32"
}
*/

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/fnptr_clean.rs"
  ],
  "callables": [
    {
      "name": "/fnptr_clean/fn1(u32,&ReBound(DebruijnIndex(0), BoundRegion { var: 0, kind: BrNamed(DefId(0:8 ~ fnptr_clean[599c]::fn1::'_), '_) }) Binder(fn(u32) -> u32, []))->u32",
      "file_index": 0,
      "first_line": 14,
      "local": true
    },
    {
      "name": "/fnptr_clean/fn2(u32)->u32",
      "file_index": 0,
      "first_line": 17,
      "local": true
    },
    {
      "name": "/fnptr_clean/fn3(u32)->u32",
      "file_index": 0,
      "first_line": 20,
      "local": true
    },
    {
      "name": "/fnptr_clean/main()->()",
      "file_index": 0,
      "first_line": 23,
      "local": true
    }
  ],
  "calls": [
    [
      0,
      15,
      5,
      0,
      1
    ],
    [
      0,
      18,
      5,
      1,
      2
    ],
    [
      0,
      25,
      5,
      3,
      0
    ]
  ]
}*/
