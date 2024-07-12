// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

pub struct Gen<T> {
    pub t: T,
}

impl<T> Gen<T> {
    pub fn foo<U>(_x: U) {}

    pub fn bar(&self, _x: T) {}
}

pub fn main() {
    let g = Gen::<u8> { t: 1u8 };
    g.bar(2u8);
    Gen::<i8>::foo::<&str>("bar");
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
    0 [ label = "\"generic::main\"" ]
    1 [ label = "\"generic::{impl#0}::bar\"" ]
    2 [ label = "\"generic::{impl#0}::foo\"" ]
    0 -> 1 [ ]
    0 -> 1 [ ]
    0 -> 2 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Dom(1,2);
insert Edge(0,0,1);
insert Edge(1,0,1);
insert Edge(2,0,2);
insert EdgeType(0,0);
insert EdgeType(1,1);
insert EdgeType(2,2);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "&Gen<u8>",
  "1": "u8",
  "2": "&str"
}

*/

/* EXPECTED:CALL_SITES{
  "files": [
    "tests/call_graph/generic.rs"
  ],
  "callables": [
    {
      "name": "/generic/main()->()",
      "file_index": 0,
      "first_line": 17,
      "local": true
    },
    {
      "name": "/generic/Gen::<T>::bar(&ReLateBound(DebruijnIndex(0), BoundRegion { var: 0, kind: BrNamed(DefId(0:12 ~ generic[ed75]::{impl#0}::bar::'_), '_) }) Gen<T/#0>,T/#0)->()",
      "file_index": 0,
      "first_line": 14,
      "local": true
    },
    {
      "name": "/generic/Gen::<T>::foo(U/#1)->()",
      "file_index": 0,
      "first_line": 12,
      "local": true
    }
  ],
  "calls": [
    [
      0,
      19,
      5,
      0,
      1
    ],
    [
      0,
      20,
      5,
      0,
      2
    ]
  ]
}*/
