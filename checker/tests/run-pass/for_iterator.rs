#![feature(rustc_private)]
#![feature(box_syntax)]
#![feature(const_vec_new)]
#![feature(vec_remove_item)]

extern crate rustc;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_target;
extern crate syntax;
extern crate syntax_pos;

//use crate::abstract_value::{AbstractValue, Path};
//use crate::environment::Environment;
//use crate::utils;

//use rustc::hir::def_id::DefId;
//use rustc::ty::TyCtxt;
//use sled::Db;
use std::collections::{HashMap, HashSet};
//use std::ops::Deref;

pub struct AbstractValue {
    //pub domain: AbstractDomain,
}

impl AbstractValue {
    pub fn record_heap_addresses(&self, _result: &mut HashSet<usize>) {}
}

#[derive(Eq, PartialEq)]
pub enum Path {
    AbstractHeapAddress { ordinal: usize },
    LocalVariable { ordinal: usize },
}

impl Path {
    pub fn is_rooted_by(&self, _root: &Path) -> bool {
        true
    }
    pub fn record_heap_addresses(&self, _result: &mut HashSet<usize>) {}
}

pub struct Environment {
    pub value_map: HashMap<Path, AbstractValue>,
}

pub fn extract_side_effects(
    env: &Environment,
    argument_count: usize,
) -> Vec<(&Path, &AbstractValue)> {
    let mut heap_roots: HashSet<usize> = HashSet::new();
    let mut result = Vec::new();
    for ordinal in 0..=argument_count {
        // remember that 0 is the result
        let root = Path::LocalVariable { ordinal };
        for (path, value) in env
            .value_map
            .iter()
            .filter(|(p, _)| (**p) == root || p.is_rooted_by(&root))
        {
            path.record_heap_addresses(&mut heap_roots);
            value.record_heap_addresses(&mut heap_roots);
            result.push((path.clone(), value.clone()));
        }
    }
    let mut visited_heap_roots: HashSet<usize> = HashSet::new();
    while heap_roots.len() > visited_heap_roots.len() {
        let mut new_roots: HashSet<usize> = HashSet::new();
        for ordinal in heap_roots.iter() {
            if visited_heap_roots.insert(*ordinal) {
                let root = Path::AbstractHeapAddress { ordinal: *ordinal };
                for (path, value) in env
                    .value_map
                    .iter()
                    .filter(|(p, _)| (**p) == root || p.is_rooted_by(&root))
                {
                    path.record_heap_addresses(&mut new_roots);
                    value.record_heap_addresses(&mut new_roots);
                    result.push((path.clone(), value.clone()));
                }
            }
        }
        heap_roots.extend(new_roots.into_iter());
    }
    result
}

pub fn main() {}
