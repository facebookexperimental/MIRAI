// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//
// Testing derivation of type relations with heuristics.

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Foo {
    x: u32
}

fn foo_ref(f: &Foo) {
    println!("{}", f.x);
}

fn foo_mut_ref(f: &mut Foo) {
    f.x = 0;
    println!("{}", f.x);
}

fn foo_slice_iter(fs: &[Foo]) {
    for f in fs.iter() {
        println!("{}", f.x);
    }
}

fn foo_vec_iter(fs: Vec<Foo>) {
    for f in fs.iter() {
        println!("{}", f.x);
    }
}

pub fn main() {
    let mut f1 = Foo { x: 1 };
    foo_ref(&f1);
    foo_mut_ref(&mut f1);

    let f2 = vec![Foo { x: 0 }, Foo { x: 1 }];
    foo_slice_iter(&f2);
    foo_vec_iter(f2);
}

/* CONFIG
{
    "reductions": ["Fold", "Clean"],
    "included_crates": [
        "type_relations"
    ],
    "datalog_config": {
        "datalog_backend": "DifferentialDatalog",
        "type_relations_path": "tests/call_graph/type_relations.json"
    }
}
*/

/* EXPECTED:DOT
digraph {
    0 [ label = "\"type_relations::main\"" ]
    1 [ label = "\"type_relations::foo_ref\"" ]
    2 [ label = "\"type_relations::foo_mut_ref\"" ]
    3 [ label = "\"type_relations::foo_slice_iter\"" ]
    4 [ label = "\"type_relations::foo_vec_iter\"" ]
    0 -> 1 [ ]
    0 -> 2 [ ]
    0 -> 3 [ ]
    0 -> 4 [ ]
}
*/

/* EXPECTED:DDLOG
start;
insert Dom(1,2);
insert Dom(1,3);
insert Dom(1,4);
insert Dom(2,3);
insert Dom(2,4);
insert Dom(3,4);
insert Edge(0,0,1);
insert Edge(1,0,2);
insert Edge(2,0,3);
insert Edge(3,0,4);
insert EdgeType(0,0);
insert EdgeType(1,6);
insert EdgeType(2,8);
insert EdgeType(3,30);
insert EqType(0,33);
insert EqType(0,36);
insert EqType(0,6);
insert EqType(33,36);
insert EqType(34,30);
insert EqType(36,33);
insert EqType(6,33);
insert EqType(6,36);
insert EqType(8,30);
insert EqType(8,34);
insert Member(30,0);
insert Member(30,33);
insert Member(30,36);
insert Member(30,6);
insert Member(31,34);
insert Member(34,0);
insert Member(34,33);
insert Member(34,36);
insert Member(34,6);
insert Member(8,0);
insert Member(8,33);
insert Member(8,36);
insert Member(8,6);
commit;
*/

/* EXPECTED:TYPEMAP
{
  "0": "&Foo",
  "6": "&mut Foo",
  "8": "&[Foo]",
  "30": "std::vec::Vec<Foo>",
  "31": "Bar",
  "33": "test::Foo",
  "34": "[test::Foo]",
  "36": "Foo"
}
*/
