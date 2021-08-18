// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use core::fmt;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{DefaultIx, NodeIndex};
use petgraph::visit::Bfs;
use petgraph::{Direction, Graph};
use rustc_hir::def_id::DefId;
use serde::ser::{SerializeMap, Serializer};
use serde::{Deserialize, Serialize};
use serde_json;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs;
use std::path::Path;

// An unique identifier for a Rust type string.
type TypeId = u32;

// A unique identifier for a graph node.
type NodeId = NodeIndex<DefaultIx>;

// Convenience types for the graph folding algorithm.
type HalfRawEdge = (NodeId, TypeId);
type RawEdge = (NodeId, NodeId, TypeId);
type MidpointExcludedMap = HashMap<NodeId, (HashSet<HalfRawEdge>, HashSet<HalfRawEdge>)>;

/// Specifies reduction operations that may be performed
/// on a call graph. Supported operations are:
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CallGraphReduction {
    /// Only include nodes reachable from the given node.
    /// See `CallGraph::filter_reachable`.
    Slice(Box<str>),
    /// Remove nodes in the graph that belong to crates other than
    /// `CallGraphConfig.included_crates`. The outgoing edges of these
    /// removed node are connected to the node's parents.
    /// See `CallGraph::fold_excluded`.
    Fold,
    /// Remove duplicated edges (only considers edge endpoints).
    /// See `CallGraph::deduplicate_edges`.
    Deduplicate,
    /// Remove nodes that have no incoming or outgoing edges.
    /// See `CallGraph::filter_no_edges`.
    Clean,
}

/// Configuration options for call graph generation.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallGraphConfig {
    /// Optionally specifies location for graph to be output in dot format
    /// (for Graphviz).
    dot_output_path: Option<Box<str>>,
    /// Optionally specifies location for graph to be output as Datalog input
    /// relations.
    ddlog_output_path: Option<Box<str>>,
    /// Optionally specifies location for mapping from type identifiers to
    /// type strings.
    type_map_output_path: Option<Box<str>>,
    /// Optionally specifies the location for manually defined type relations
    /// to be imported.
    type_relations_path: Option<Box<str>>,
    /// A list of call graph reductions to apply sequentially
    /// to the call graph.
    reductions: Vec<CallGraphReduction>,
    /// A list of crates to include in the call graph.
    /// Nodes belonging to crates not in this list will be removed.
    included_crates: Vec<Box<str>>,
}

impl Default for CallGraphConfig {
    fn default() -> CallGraphConfig {
        CallGraphConfig {
            dot_output_path: None,
            ddlog_output_path: None,
            type_map_output_path: None,
            type_relations_path: None,
            reductions: Vec::<CallGraphReduction>::new(),
            included_crates: Vec::<Box<str>>::new(),
        }
    }
}

impl CallGraphConfig {
    pub fn new(
        dot_output_path: Option<Box<str>>,
        ddlog_output_path: Option<Box<str>>,
        type_map_output_path: Option<Box<str>>,
        type_relations_path: Option<Box<str>>,
        reductions: Vec<CallGraphReduction>,
        included_crates: Vec<Box<str>>,
    ) -> CallGraphConfig {
        CallGraphConfig {
            dot_output_path,
            ddlog_output_path,
            type_map_output_path,
            type_relations_path,
            reductions,
            included_crates,
        }
    }

    pub fn get_dot_path(&self) -> Option<&str> {
        self.dot_output_path.as_deref()
    }

    pub fn get_ddlog_path(&self) -> Option<&str> {
        self.ddlog_output_path.as_deref()
    }

    pub fn get_type_map_path(&self) -> Option<&str> {
        self.type_map_output_path.as_deref()
    }
}

/// The type of a call graph node.
#[derive(Debug, Clone, PartialEq)]
enum NodeType {
    /// Regular root: Any function that is not a crate root
    Root,
    /// Crate root: Starting point for analysis (pub fn)
    CRoot,
}

/// Nodes in the call graph are functions defined by the program
/// that is being analyzed.
#[derive(Debug, Clone)]
struct CallGraphNode {
    /// The DefId of the function
    defid: DefId,
    /// The name of the function (derived from its DefId).
    name: Box<str>,
    /// The type of the node.
    node_type: NodeType,
}

impl CallGraphNode {
    pub fn new_croot(defid: DefId) -> CallGraphNode {
        CallGraphNode {
            defid,
            name: CallGraphNode::format_name(defid),
            node_type: NodeType::CRoot,
        }
    }

    pub fn new_root(defid: DefId) -> CallGraphNode {
        CallGraphNode {
            defid,
            name: CallGraphNode::format_name(defid),
            node_type: NodeType::Root,
        }
    }

    /// Extracts a function name from the DefId of a function.
    fn format_name(defid: DefId) -> Box<str> {
        let tmp1 = format!("{:?}", defid);
        let tmp2: &str = tmp1.split("~ ").collect::<Vec<&str>>()[1];
        let tmp3 = tmp2.replace(")", "");
        let lhs = tmp3.split('[').collect::<Vec<&str>>()[0];
        let rhs = tmp3.split(']').collect::<Vec<&str>>()[1];
        format!("{}{}", lhs, rhs).into_boxed_str()
    }

    /// A node is excluded if its name does not include any
    /// one of the included crates' names.
    pub fn is_excluded(&self, included_crates: &[&str]) -> bool {
        let mut excluded = true;
        for crate_name in included_crates.iter() {
            if self.name.contains(crate_name) {
                excluded = false;
                break;
            }
        }
        excluded
    }

    pub fn is_croot(&self) -> bool {
        self.node_type == NodeType::CRoot
    }
}

/// Denotes ways that two types, t1 and t2, can be related.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
enum TypeRelationKind {
    /// States that t1 is equivalent to t2.
    Eq,
    /// States that t2 is a member of t1.
    Member,
}

/// A type relation relates types `type1` and `type2` by a
/// `TypeRelationKind`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct TypeRelation {
    kind: TypeRelationKind,
    type1: Box<str>,
    type2: Box<str>,
}

impl TypeRelation {
    fn new_eq(t1: Box<str>, t2: Box<str>) -> TypeRelation {
        TypeRelation {
            kind: TypeRelationKind::Eq,
            type1: t1,
            type2: t2,
        }
    }

    fn new_member(t1: Box<str>, t2: Box<str>) -> TypeRelation {
        TypeRelation {
            kind: TypeRelationKind::Member,
            type1: t1,
            type2: t2,
        }
    }
}

/// Types associated with call graph edges
#[derive(Debug, Clone)]
struct EdgeType {
    /// Unique identifier for this time
    id: TypeId,
    // Textual representation of the type
    name: Box<str>,
    /// Derived type relations
    type_relations: HashSet<TypeRelation>,
}

impl EdgeType {
    fn new(id: TypeId, name: Box<str>) -> EdgeType {
        let type_relations = EdgeType::derive_type_relations(&name);
        EdgeType {
            id,
            name,
            type_relations,
        }
    }

    /// Derive equality and membership relationships from the following
    /// heuristics:
    /// - Option<t> == t
    /// - &t == t
    /// - mut t == t
    /// - [t] > t
    fn derive_type_relations(name: &str) -> HashSet<TypeRelation> {
        let mut relations = HashSet::<TypeRelation>::new();
        let mut base_type = name.to_owned();
        if base_type.contains("&std::option::Option<") {
            let base_type_new = base_type
                .replace("&std::option::Option<", "")
                .replace(">", "");
            relations.insert(TypeRelation::new_eq(
                base_type.into_boxed_str(),
                base_type_new.clone().into_boxed_str(),
            ));
            base_type = base_type_new;
        }
        if base_type.contains('[') && base_type.contains(']') {
            let base_type_new = base_type.replace("[", "").replace("]", "");
            relations.insert(TypeRelation::new_member(
                base_type.into_boxed_str(),
                base_type_new.clone().into_boxed_str(),
            ));
            base_type = base_type_new;
        }
        if base_type.contains("mut") {
            let base_type_new = base_type.replace("mut ", "");
            relations.insert(TypeRelation::new_eq(
                base_type.into_boxed_str(),
                base_type_new.clone().into_boxed_str(),
            ));
            base_type = base_type_new;
        }
        if base_type.contains('&') {
            let base_type_new = base_type.replace("&", "");
            relations.insert(TypeRelation::new_eq(
                base_type.into_boxed_str(),
                base_type_new.into_boxed_str(),
            ));
        }
        relations
    }
}

/// An edge in the call graph is directed. It connects two nodes
/// n1 and n2, and represents that n1 is a caller of n2.
#[derive(Debug, Clone)]
struct CallGraphEdge {
    /// Edges have an associated Rust type, denoting a type of data
    /// passed in the call from n1 to n2.
    type_id: TypeId,
}

impl CallGraphEdge {
    pub fn new(type_id: TypeId) -> CallGraphEdge {
        CallGraphEdge { type_id }
    }
}

/// `CallGraph` stores all information related to the call graph
/// and it's associated information.
#[derive(Debug, Clone)]
pub struct CallGraph {
    /// Configuration for the call graph
    config: CallGraphConfig,
    /// The graph structure capturing calls between nodes
    graph: Graph<CallGraphNode, CallGraphEdge>,
    /// A map from DefId to node information
    nodes: HashMap<DefId, NodeId>,
    /// A map from type string to an EdgeType instance
    edge_types: HashMap<Box<str>, EdgeType>,
    /// Dominance information
    dominance: HashMap<DefId, HashSet<DefId>>,
}

impl CallGraph {
    pub fn new(path_to_config: Option<String>) -> CallGraph {
        let config = match path_to_config {
            Some(path) => CallGraph::parse_config(Path::new(&path)),
            None => CallGraphConfig::default(),
        };
        CallGraph {
            config,
            graph: Graph::<CallGraphNode, CallGraphEdge>::new(),
            nodes: HashMap::<DefId, NodeId>::new(),
            edge_types: HashMap::<Box<str>, EdgeType>::new(),
            dominance: HashMap::<DefId, HashSet<DefId>>::new(),
        }
    }

    fn parse_config(path_to_config: &Path) -> CallGraphConfig {
        let config_result = fs::read_to_string(path_to_config)
            .map_err(|e| e.to_string())
            .and_then(|config_str| {
                serde_json::from_str::<CallGraphConfig>(&config_str).map_err(|e| e.to_string())
            });
        match config_result {
            Ok(config) => config,
            Err(e) => panic!("Failed to read call graph config: {:?}", e),
        }
    }

    /// Produce an updated call graph structure that preserves all of the
    /// fields except `graph`, which is replaced.
    fn update(&self, graph: Graph<CallGraphNode, CallGraphEdge>) -> CallGraph {
        CallGraph {
            config: self.config.clone(),
            graph,
            nodes: self.nodes.clone(),
            edge_types: self.edge_types.clone(),
            dominance: self.dominance.clone(),
        }
    }

    /// Add a new crate root node to the call graph.
    pub fn add_croot(&mut self, defid: DefId) {
        let croot = CallGraphNode::new_croot(defid);
        let node_id = self.graph.add_node(croot);
        self.nodes.insert(defid, node_id);
    }

    /// Add a new root node to the call graph.
    pub fn add_root(&mut self, defid: DefId) {
        if let Entry::Vacant(e) = self.nodes.entry(defid) {
            let croot = CallGraphNode::new_root(defid);
            let node_id = self.graph.add_node(croot);
            e.insert(node_id);
        }
    }

    /// Helper function to get a node or insert a new
    /// root node if it does not exist in the map.
    fn get_or_insert_node(&mut self, defid: DefId) -> NodeId {
        match self.nodes.entry(defid) {
            Entry::Occupied(node) => node.get().to_owned(),
            Entry::Vacant(v) => {
                let node_id = self.graph.add_node(CallGraphNode::new_root(defid));
                *v.insert(node_id)
            }
        }
    }

    /// Add a dominance relationship to the call graph.
    /// Denotes that `defid1` is dominated by `defid2`.
    pub fn add_dom(&mut self, defid1: DefId, defid2: DefId) {
        self.dominance
            .entry(defid1)
            .or_insert_with(HashSet::<DefId>::new)
            .insert(defid2);
    }

    /// Add a new EdgeType to the call graph's `edge_types`.
    fn add_edge_type(&mut self, edge_type_str: Box<str>) -> TypeId {
        let new_type_id = self.edge_types.len() as TypeId;
        match self.edge_types.entry(edge_type_str.to_owned()) {
            Entry::Occupied(edge_type) => edge_type.get().id,
            Entry::Vacant(v) => v.insert(EdgeType::new(new_type_id, edge_type_str)).id,
        }
    }

    /// Add a new edge to the call graph.
    /// The edge is a call edge from `caller_id` to `callee_id` with type `edge_type_str`.
    pub fn add_edge(&mut self, caller_id: DefId, callee_id: DefId, edge_type_str: Box<str>) {
        let type_id = self.add_edge_type(edge_type_str);
        let caller_node = self.get_or_insert_node(caller_id);
        let callee_node = self.get_or_insert_node(callee_id);
        let mut existing_types = HashSet::<TypeId>::new();
        for edge in self.graph.edges_connecting(caller_node, callee_node) {
            existing_types.insert(edge.weight().type_id);
        }
        if !existing_types.contains(&type_id) {
            self.graph
                .add_edge(caller_node, callee_node, CallGraphEdge::new(type_id));
        }
    }

    /// Find a node in the call graph given a `name` that may appear as
    /// a substring within the node's name. The first such node is returned, if any.
    fn get_node_by_name(&self, name: &str) -> Option<NodeId> {
        for node_id in self.graph.node_indices() {
            if let Some(node) = self.graph.node_weight(node_id) {
                if node.name.contains(name) {
                    return Some(node_id);
                }
            }
        }
        None
    }

    /// Find a node in the call graph given a DefId.
    /// The first such node is returned, if any.
    fn get_node_by_defid(&self, defid: DefId) -> Option<NodeId> {
        for node_id in self.graph.node_indices() {
            if let Some(node) = self.graph.node_weight(node_id) {
                if node.defid == defid {
                    return Some(node_id);
                }
            }
        }
        None
    }

    /// Deduplicate edges by only including a single edge for for each
    /// (caller, callee) pair that has an edge.
    ///
    /// If there are multiple edges from a caller to a callee with different types,
    /// this has the effect of including only one of those edges.
    fn deduplicate_edges(&self) -> CallGraph {
        let mut edges = HashSet::<(NodeId, NodeId)>::new();
        let graph = self.graph.filter_map(
            |_, node| Some(node.to_owned()),
            |edge_id, edge| {
                self.graph.edge_endpoints(edge_id).and_then(|endpoints| {
                    if edges.insert(endpoints) {
                        Some(edge.to_owned())
                    } else {
                        None
                    }
                })
            },
        );
        self.update(graph)
    }

    /// Returns the set of nodes (Node indexes, which uniquely identify nodes)
    /// That are reachable from the given start node.
    ///
    /// The underlying algorithm used to perform graph traversal is a,
    /// breath-first search however, only one crate root is included
    /// from the traversal.
    fn reachable_from(&self, start_node: NodeId) -> HashSet<NodeId> {
        let mut reachable = HashSet::<NodeId>::new();
        let mut bfs = Bfs::new(&self.graph, start_node);
        let mut croot: Option<NodeId> = None;
        while let Some(node_id) = bfs.next(&self.graph) {
            if let Some(node) = self.graph.node_weight(node_id) {
                if node.is_croot() {
                    if croot.is_none() {
                        croot = Some(node_id);
                        reachable.insert(node_id);
                    }
                } else {
                    reachable.insert(node_id);
                }
            }
        }
        reachable
    }

    /// Filter out all nodes from the graph that are not reachable
    /// via start node identifiable by `name`.
    fn filter_reachable(&self, name: &str) -> CallGraph {
        if let Some(start_node) = self.get_node_by_name(name) {
            let reachable = self.reachable_from(start_node);
            let graph = self.graph.filter_map(
                |node_id, node| {
                    if reachable.contains(&node_id) {
                        Some(node.to_owned())
                    } else {
                        None
                    }
                },
                |_, edge| Some(edge.to_owned()),
            );
            self.update(graph)
        } else {
            panic!(
                "Failed to filter graph; could not find start node: {}",
                name
            );
        }
    }

    /// Helper function for folding excluded nodes.
    ///
    /// Computes the set of reachable nodes reachable
    /// via one or more excluded nodes.
    fn reachable_raw_edges(
        &self,
        excluded: &MidpointExcludedMap,
        initial_set: &HashSet<HalfRawEdge>,
    ) -> HashSet<HalfRawEdge> {
        let mut reachable = initial_set.clone();
        let mut queue = VecDeque::<NodeId>::new();
        for edge in reachable.iter() {
            let start_node_id = edge.0;
            queue.push_back(start_node_id);
        }
        while let Some(node_id) = queue.pop_front() {
            if let Some((_, child_edges)) = excluded.get(&node_id) {
                for edge in child_edges.iter() {
                    if !reachable.contains(edge) {
                        reachable.insert(*edge);
                        let start_node_id = edge.0;
                        if excluded.contains_key(&start_node_id) {
                            queue.push_back(start_node_id);
                        }
                    }
                }
            }
        }
        reachable
    }

    /// Helper function for folding excluded nodes.
    ///
    /// Condenses a set of edges (in the form of a midpoint-excluded map, which tracks in and out
    /// edges for every excluded node) to all edges that do not have an excluded endpoint.
    fn condense_edge_set(&self, excluded: &MidpointExcludedMap) -> HashSet<RawEdge> {
        let mut condensed_edges = HashSet::<RawEdge>::new();
        for (_, (in_nodes, out_nodes)) in excluded.iter() {
            let out_nodes2 = self.reachable_raw_edges(excluded, out_nodes);
            for (in_node_id, in_type) in in_nodes.iter() {
                if !excluded.contains_key(in_node_id) {
                    for (out_node_id, _) in out_nodes2.iter() {
                        if !excluded.contains_key(out_node_id) {
                            condensed_edges.insert((*in_node_id, *out_node_id, *in_type));
                        }
                    }
                }
            }
        }
        condensed_edges
    }

    /// Fold the graph to remove excluded nodes and edges.
    ///
    /// An excluded node satisfies `node.is_excluded()` (it is not one of crates specified
    /// by CallGraphConfig::included_crates).
    /// An excluded edge is an edge with at least one excluded endpoint.
    ///
    /// The outgoing edges of an excluded node are joined to the node's non-excluded parents.
    fn fold_excluded(&self) -> CallGraph {
        let mut excluded = MidpointExcludedMap::new();
        // 1. Find all excluded nodes
        let mut graph = self.graph.filter_map(
            |node_id, node| {
                let included_crates = self
                    .config
                    .included_crates
                    .iter()
                    .map(|v| &**v)
                    .collect::<Vec<&str>>();
                if node.is_excluded(&included_crates) {
                    excluded.insert(
                        node_id,
                        (HashSet::<HalfRawEdge>::new(), HashSet::<HalfRawEdge>::new()),
                    );
                }
                Some(node.to_owned())
            },
            |_, edge| Some(edge.to_owned()),
        );
        // 2. Find all excluded edges
        graph = graph.filter_map(
            |_, node| Some(node.to_owned()),
            |edge_id, edge| {
                self.graph
                    .edge_endpoints(edge_id)
                    .map(|(start_id, end_id)| {
                        excluded
                            .get_mut(&end_id)
                            .map(|entry| entry.0.insert((start_id, edge.type_id)));
                        excluded
                            .get_mut(&start_id)
                            .map(|entry| entry.1.insert((end_id, edge.type_id)));
                        edge.to_owned()
                    })
            },
        );
        // 3. Condense edges and insert
        for (in_id, out_id, type_id) in self.condense_edge_set(&excluded).iter() {
            let edge = CallGraphEdge::new(*type_id);
            graph.add_edge(*in_id, *out_id, edge);
        }
        // 4. Remove excluded nodes and edges
        graph = graph.filter_map(
            |node_id, node| {
                if excluded.contains_key(&node_id) {
                    None
                } else {
                    Some(node.to_owned())
                }
            },
            |_, edge| Some(edge.to_owned()),
        );
        self.update(graph)
    }

    /// Filter out nodes from that graph that have no incoming
    /// or outgoing edges (unconnected from the rest of the graph).
    fn filter_no_edges(&self) -> CallGraph {
        let graph = self.graph.filter_map(
            |node_id, node| {
                let has_in_edges = self
                    .graph
                    .edges_directed(node_id, Direction::Incoming)
                    .next()
                    .is_some();
                let has_out_edges = self
                    .graph
                    .edges_directed(node_id, Direction::Outgoing)
                    .next()
                    .is_some();
                if has_in_edges || has_out_edges {
                    Some(node.to_owned())
                } else {
                    None
                }
            },
            |_, edge| Some(edge.to_owned()),
        );
        self.update(graph)
    }

    /// Produce a representation of the graph that uses
    /// the (shorter) `node.name`, which is derived from the node's DefId,
    /// rather than the full DefId itself.
    fn shortened_node_names(&self) -> Graph<&str, ()> {
        self.graph
            .filter_map(|_, node| Some(&*node.name), |_, _| Some(()))
    }

    /// Perform a specified sequence of reductions on the call graph.
    fn reduce_graph(&self, call_graph: CallGraph, reductions: &[CallGraphReduction]) -> CallGraph {
        reductions
            .iter()
            .fold(call_graph, |graph, reduction| match reduction {
                CallGraphReduction::Slice(crate_name) => graph.filter_reachable(crate_name),
                CallGraphReduction::Fold => graph.fold_excluded(),
                CallGraphReduction::Deduplicate => graph.deduplicate_edges(),
                CallGraphReduction::Clean => graph.filter_no_edges(),
            })
    }

    fn gather_type_relations(
        &self,
        index_to_type: &HashMap<TypeId, &EdgeType>,
        type_relations_path: Option<&Path>,
    ) -> HashSet<TypeRelation> {
        let mut type_relations = HashSet::<TypeRelation>::new();
        // Insert input type relations from file
        if let Some(path) = type_relations_path {
            let input_type_relations_raw: TypeRelationsRaw = match fs::read_to_string(path)
                .map_err(|e| e.to_string())
                .and_then(|input_type_relations_str| {
                    serde_json::from_str(&input_type_relations_str).map_err(|e| e.to_string())
                }) {
                Ok(relations) => relations,
                Err(e) => panic!("Failed to read input type relations: {:?}", e),
            };
            let mut input_type_relations = HashSet::<TypeRelation>::new();
            for relation in input_type_relations_raw.relations.iter() {
                input_type_relations.insert(relation.to_owned());
            }
            type_relations.extend(input_type_relations);
        }
        for (_, edge_type) in index_to_type.iter() {
            type_relations.extend(edge_type.type_relations.to_owned());
        }
        type_relations
    }

    /// Convert the call graph to a Datalog representation.
    ///
    /// Properties of the graph are converted into Datalog input relations.
    /// - `Dom(n1, n2)`: `n1` dominates `n2`.
    /// - `Edge(id, n1, n2)`: There is a call edge from `n1` to `n2`.
    /// - `EdgeType(id, type_id)`: The edge has the type associated with `type_id`.
    /// - `EqType(type_id1, type_id2)`: The type `type_id1` is equivalent to `type_id2`.
    /// - `Member(type_id1, type_id2)`: The type `type_id2` is a member of `type_id1`.
    fn to_datalog(
        &self,
        ddlog_path: &Path,
        type_map_path: &Path,
        type_relations_path: Option<&Path>,
    ) {
        let mut ctr: u32 = 0;
        let mut used_types = HashSet::<TypeId>::new();
        let mut output = DatalogOutput::new();
        // Output dominance relations
        self.graph.map(
            |node_id1, node| {
                if let Some(nodes) = self.dominance.get(&node.defid) {
                    for defid2 in nodes.iter() {
                        if let Some(node_id2) = self.get_node_by_defid(*defid2) {
                            output.add_relation(DatalogRelation::new_dom(
                                node_id1.index() as u32,
                                node_id2.index() as u32,
                            ))
                        }
                    }
                }
            },
            |_, _| (),
        );
        // Output edge and edge type relations
        self.graph.map(
            |_, _| (),
            |edge_id, edge| {
                if let Some((start_id, end_id)) = self.graph.edge_endpoints(edge_id) {
                    output.add_relation(DatalogRelation::new_edge(
                        ctr,
                        start_id.index() as u32,
                        end_id.index() as u32,
                    ));
                    output.add_relation(DatalogRelation::new_edge_type(ctr, edge.type_id));
                    used_types.insert(edge.type_id);
                    ctr += 1;
                }
            },
        );
        // Output type relations
        let mut index_to_type = HashMap::<TypeId, &EdgeType>::new();
        for (_, edge_type) in self.edge_types.iter() {
            if used_types.contains(&edge_type.id) {
                index_to_type.insert(edge_type.id, edge_type);
            }
        }
        let used_type_strs: HashMap<Box<str>, EdgeType> = self
            .edge_types
            .clone()
            .into_iter()
            .filter(|(_, v)| used_types.contains(&v.id))
            .collect();
        for type_relation in self
            .gather_type_relations(&index_to_type, type_relations_path)
            .iter()
        {
            if let Some(type1) = used_type_strs.get(&type_relation.type1) {
                if let Some(type2) = used_type_strs.get(&type_relation.type2) {
                    match type_relation.kind {
                        TypeRelationKind::Eq => {
                            output.add_relation(DatalogRelation::new_eq_type(type1.id, type2.id))
                        }
                        TypeRelationKind::Member => {
                            output.add_relation(DatalogRelation::new_member(type1.id, type2.id))
                        }
                    }
                }
            }
        }
        match fs::write(ddlog_path, format!("{}", output)) {
            Ok(_) => (),
            Err(e) => panic!("Failed to write ddlog output: {:?}", e),
        }
        // Output the type map
        match serde_json::to_string_pretty(&TypeMapOutput { map: index_to_type })
            .map_err(|e| e.to_string())
            .and_then(|type_map_output| {
                fs::write(type_map_path, type_map_output).map_err(|e| e.to_string())
            }) {
            Ok(_) => (),
            Err(e) => panic!("Failed to write type map output: {:?}", e),
        };
    }

    /// Produce a dot file representation of the call graph
    /// for displaying with Graphviz.
    fn to_dot(&self, dot_path: &Path) {
        let output = format!(
            "{:?}",
            Dot::with_config(&self.shortened_node_names(), &[Config::EdgeNoLabel])
        );
        match fs::write(dot_path, output) {
            Ok(_) => (),
            Err(e) => panic!("Failed to write dot file output: {:?}", e),
        };
    }

    /// Top-level output function.
    ///
    /// First applies a set of reductions to the call graph.
    /// Then produces Datalog and / or dot file output of the call graph.
    pub fn output(&self) {
        let call_graph = self.reduce_graph(self.clone(), &self.config.reductions);
        if let Some(ddlog_path) = &self.config.ddlog_output_path {
            if let Some(type_map_path) = &self.config.type_map_output_path {
                let ddlog_path_str: &str = &*ddlog_path;
                let type_map_path_str: &str = &*type_map_path;
                call_graph.to_datalog(
                    Path::new(ddlog_path_str),
                    Path::new(type_map_path_str),
                    self.config.type_relations_path.as_ref().map(|v| {
                        let path_str: &str = &*v;
                        Path::new(path_str)
                    }),
                );
            }
        }
        if let Some(dot_path) = &self.config.dot_output_path {
            let dot_path_str: &str = &*dot_path;
            call_graph.to_dot(Path::new(dot_path_str));
        }
    }
}

/// Temporary data structure for storing deserialized
/// manually-added type relations.
#[derive(Serialize, Deserialize)]
struct TypeRelationsRaw {
    relations: Vec<TypeRelation>,
}

/// Temporary data structure for storing the type
/// map for serialization.
struct TypeMapOutput<'a> {
    map: HashMap<TypeId, &'a EdgeType>,
}

impl<'a> Serialize for TypeMapOutput<'a> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.map.len()))?;
        let mut map_entries: Vec<_> = self.map.iter().collect();
        map_entries.sort_by_key(|k| k.0);
        for (k, v) in map_entries.iter() {
            map.serialize_entry(&k.to_string(), &v.name)?;
        }
        map.end()
    }
}

/// Represents an atomic Datalog relation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct DatalogRelation {
    /// A relation has a name.
    name: &'static str,
    /// As well as one or more operands.
    operands: Vec<u32>,
}

impl fmt::Display for DatalogRelation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.name,
            self.operands
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(",")
        )
    }
}

impl DatalogRelation {
    pub fn new_dom(n1: u32, n2: u32) -> DatalogRelation {
        DatalogRelation {
            name: "Dom",
            operands: vec![n1, n2],
        }
    }

    pub fn new_edge(id: u32, n1: u32, n2: u32) -> DatalogRelation {
        DatalogRelation {
            name: "Edge",
            operands: vec![id, n1, n2],
        }
    }

    pub fn new_edge_type(id: u32, t: u32) -> DatalogRelation {
        DatalogRelation {
            name: "EdgeType",
            operands: vec![id, t],
        }
    }

    pub fn new_eq_type(t1: u32, t2: u32) -> DatalogRelation {
        DatalogRelation {
            name: "EqType",
            operands: vec![t1, t2],
        }
    }

    pub fn new_member(t1: u32, t2: u32) -> DatalogRelation {
        DatalogRelation {
            name: "Member",
            operands: vec![t1, t2],
        }
    }
}

/// Structure for storing Datalog relations
/// to later be output as a Datalog file that can
/// be input into a Datalog database.
struct DatalogOutput {
    relations: HashSet<DatalogRelation>,
}

impl fmt::Display for DatalogOutput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "start;")?;
        let mut relation_strings = Vec::<String>::new();
        for relation in self.relations.iter() {
            relation_strings.push(format!("insert {};", relation));
        }
        relation_strings.sort();
        let output = relation_strings.join("\n");
        writeln!(f, "{}", output)?;
        writeln!(f, "commit;")
    }
}

impl DatalogOutput {
    pub fn new() -> DatalogOutput {
        DatalogOutput {
            relations: HashSet::<DatalogRelation>::new(),
        }
    }

    pub fn add_relation(&mut self, relation: DatalogRelation) {
        self.relations.insert(relation);
    }
}
