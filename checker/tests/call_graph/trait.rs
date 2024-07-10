// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

pub trait Tr {
    fn bar(&self) -> i32;
}

struct Bar {}

impl Tr for Bar {
    fn bar(&self) -> i32 {
        1
    }
}

struct BarTwo {}

impl Tr for BarTwo {
    fn bar(&self) -> i32 {
        2
    }
}

pub fn main() {
    let bar = Bar {};
    let _ = bar.bar();
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
    0 [ label = "\"trait::{impl#0}::bar\"" ]
    1 [ label = "\"trait::{impl#1}::bar\"" ]
    2 [ label = "\"trait::main\"" ]
    2 -> 0 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Edge(0,2,0);
insert EdgeType(0,0);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "&Bar"
}
*/

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/trait.rs"
  ],
  "callables": [
    {
      "name": "/trait/main()->()",
      "file_index": 0,
      "first_line": 27,
      "local": true
    },
    {
      "name": "/trait/<Bar as Tr>::bar(&ReLateBound(DebruijnIndex(0), BoundRegion { var: 0, kind: BrNamed(DefId(0:13 ~ trait[3dda]::{impl#0}::bar::'_), '_) }) Bar)->i32",
      "file_index": 0,
      "first_line": 14,
      "local": true
    }
  ],
  "calls": [
    [
      0,
      29,
      13,
      0,
      1
    ]
  ]
}*/
