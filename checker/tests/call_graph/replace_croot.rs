// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

// Test case that ensures that a CROOT node is not duplicated if it
// is analyzed by MIRAI after MIRAI analyzed its first call.

pub fn main() {
    fn1();
}

pub fn fn1() -> u32 {
    1
}

/* CONFIG
{
    "reductions": [],
    "included_crates": [],
    "datalog_config": {
        "datalog_backend": "DifferentialDatalog"
    }
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"replace_croot::main\"" ]
    1 [ label = "\"replace_croot::fn1\"" ]
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

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/replace_croot.rs"
  ],
  "callables": [
    {
      "name": "replace_croot.main",
      "file_index": 0,
      "first_line": 10,
      "local": true
    },
    {
      "name": "replace_croot.fn1",
      "file_index": 0,
      "first_line": 14,
      "local": true
    }
  ],
  "calls": [
    [
      0,
      11,
      5,
      0,
      1
    ]
  ]
}*/
