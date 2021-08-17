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
type RTypeIdx = u32;

// A unique identifier for a graph node.
type NodeIdx = NodeIndex<DefaultIx>;

// Convenience types for the graph folding algorithm.
type HalfRawEdge = (NodeIdx, RTypeIdx);
type RawEdge = (NodeIdx, NodeIdx, RTypeIdx);
type MidpointExcludedMap = HashMap<NodeIdx, (HashSet<HalfRawEdge>, HashSet<HalfRawEdge>)>;

/// Specifies reduction operations that may be perfomed
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
    /// (for graphviz).
    dot_output_path: Option<Box<str>>,
    /// Optionally specifies location for graph to be output as datalog input
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
    /// The name of the function (derived from its DefId).
    name: Box<str>,
    /// The type of the node.
    ntype: NodeType,
}

impl CallGraphNode {
    pub fn new_croot(defid: DefId) -> CallGraphNode {
        CallGraphNode {
            name: CallGraphNode::format_name(defid),
            ntype: NodeType::CRoot,
        }
    }

    pub fn new_root(defid: DefId) -> CallGraphNode {
        CallGraphNode {
            name: CallGraphNode::format_name(defid),
            ntype: NodeType::Root,
        }
    }

    /// Extracts a function name from the DefId of a function.
    fn format_name(defid: DefId) -> Box<str> {
        let tmp1 = format!("{:?}", defid);
        let tmp2: &str = tmp1.split("~ ").collect::<Vec<&str>>()[1];
        tmp2.replace(")", "").into_boxed_str()
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
        self.ntype == NodeType::CRoot
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

/// A type relation relates types `rtype1` and `rtype2` by a
/// `TypeRelationKind`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct TypeRelation {
    kind: TypeRelationKind,
    rtype1: Box<str>,
    rtype2: Box<str>,
}

impl TypeRelation {
    fn new_eq(t1: Box<str>, t2: Box<str>) -> TypeRelation {
        TypeRelation {
            kind: TypeRelationKind::Eq,
            rtype1: t1,
            rtype2: t2,
        }
    }

    fn new_member(t1: Box<str>, t2: Box<str>) -> TypeRelation {
        TypeRelation {
            kind: TypeRelationKind::Member,
            rtype1: t1,
            rtype2: t2,
        }
    }
}

/// Types in the call graph as encoded as `RType` structs.
/// An `RType` has:
/// - `id`: A unique identifier.
/// - `name`: A textual representation.
/// - `type_relations`: A set of derived type relations.
#[derive(Debug, Clone)]
struct RType {
    id: RTypeIdx,
    name: Box<str>,
    type_relations: HashSet<TypeRelation>,
}

impl RType {
    fn new(id: RTypeIdx, name: Box<str>) -> RType {
        let type_relations = RType::derive_type_relations(&name);
        RType {
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
    rtype_id: RTypeIdx,
}

impl CallGraphEdge {
    pub fn new(rtype_id: RTypeIdx) -> CallGraphEdge {
        CallGraphEdge { rtype_id }
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
    nodes: HashMap<DefId, NodeIdx>,
    /// A map from type string to type identifier
    rtypes: HashMap<Box<str>, RType>,
    /// Dominance information
    dominance: HashMap<NodeIdx, HashSet<NodeIdx>>,
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
            nodes: HashMap::<DefId, NodeIdx>::new(),
            rtypes: HashMap::<Box<str>, RType>::new(),
            dominance: HashMap::<NodeIdx, HashSet<NodeIdx>>::new(),
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
            rtypes: self.rtypes.clone(),
            dominance: self.dominance.clone(),
        }
    }

    /// Add a new crate root node to the call graph.
    pub fn add_croot(&mut self, defid: DefId) {
        let croot = CallGraphNode::new_croot(defid);
        let node_idx = self.graph.add_node(croot);
        self.nodes.insert(defid, node_idx);
    }

    /// Add a new root node to the calll graph.
    pub fn add_root(&mut self, defid: DefId) {
        if let Entry::Vacant(e) = self.nodes.entry(defid) {
            let croot = CallGraphNode::new_root(defid);
            let node_idx = self.graph.add_node(croot);
            e.insert(node_idx);
        }
    }

    /// Helper function to get a node or insert a new
    /// root node if it does not exist in the map.
    fn get_or_insert_node(&mut self, defid: DefId) -> NodeIdx {
        match self.nodes.entry(defid) {
            Entry::Occupied(node) => node.get().to_owned(),
            Entry::Vacant(v) => {
                let node_idx = self.graph.add_node(CallGraphNode::new_root(defid));
                *v.insert(node_idx)
            }
        }
    }

    /// Add a dominance relationship to the call graph.
    /// Denotes that `defid1` is dominated by `defid2`.
    pub fn add_dom(&mut self, defid1: DefId, defid2: DefId) {
        let node_idx1 = self.get_or_insert_node(defid1);
        let node_idx2 = self.get_or_insert_node(defid2);
        self.dominance
            .entry(node_idx1)
            .or_insert_with(HashSet::<NodeIdx>::new)
            .insert(node_idx2);
    }

    /// Add a new RType to the call graph's `rtypes`.
    fn add_rtype(&mut self, rtype_str: Box<str>) -> RTypeIdx {
        let new_rtype_id = self.rtypes.len() as RTypeIdx;
        match self.rtypes.entry(rtype_str.to_owned()) {
            Entry::Occupied(rtype) => rtype.get().id,
            Entry::Vacant(v) => v.insert(RType::new(new_rtype_id, rtype_str)).id,
        }
    }

    /// Add a new edge to the call graph.
    /// The edge is a call edge from `caller_id` to `callee_id` with type `rtype_str`.
    pub fn add_edge(&mut self, caller_id: DefId, callee_id: DefId, rtype_str: Box<str>) {
        let rtype_id = self.add_rtype(rtype_str);
        let caller_node = self.get_or_insert_node(caller_id);
        let callee_node = self.get_or_insert_node(callee_id);
        let mut existing_rtypes = HashSet::<RTypeIdx>::new();
        for edge in self.graph.edges_connecting(caller_node, callee_node) {
            existing_rtypes.insert(edge.weight().rtype_id);
        }
        if !existing_rtypes.contains(&rtype_id) {
            self.graph
                .add_edge(caller_node, callee_node, CallGraphEdge::new(rtype_id));
        }
    }

    /// Find a node in the call graph given a `name` that may appear as
    /// a substring within the node's name. The first such node is returned, if any.
    fn get_node_by_name(&self, name: &str) -> Option<NodeIdx> {
        for node_idx in self.graph.node_indices() {
            if let Some(node) = self.graph.node_weight(node_idx) {
                if node.name.contains(name) {
                    return Some(node_idx);
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
        let mut edges = HashSet::<(NodeIdx, NodeIdx)>::new();
        let graph = self.graph.filter_map(
            |_, node| Some(node.to_owned()),
            |edge_idx, edge| {
                self.graph.edge_endpoints(edge_idx).and_then(|endpoints| {
                    if edges.contains(&endpoints) {
                        None
                    } else {
                        edges.insert(endpoints);
                        Some(edge.to_owned())
                    }
                })
            },
        );
        self.update(graph)
    }

    /// Returns the set of nodes (Node indexes, which uniquely identify nodes)
    /// That are reachable from the given start node.
    ///
    /// The underlying algorithm used to perform graph traveral is a BFS,
    /// however, only one crate root is included from the traversal.
    fn reachable_from(&self, start_node: NodeIdx) -> HashSet<NodeIdx> {
        let mut reachable = HashSet::<NodeIdx>::new();
        let mut bfs = Bfs::new(&self.graph, start_node);
        let mut croot: Option<NodeIdx> = None;
        while let Some(node_idx) = bfs.next(&self.graph) {
            if let Some(node) = self.graph.node_weight(node_idx) {
                if node.is_croot() {
                    if croot.is_none() {
                        croot = Some(node_idx);
                        reachable.insert(node_idx);
                    }
                } else {
                    reachable.insert(node_idx);
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
                |node_idx, node| {
                    if reachable.contains(&node_idx) {
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
        let mut queue = VecDeque::<NodeIdx>::new();
        for edge in reachable.iter() {
            queue.push_back(edge.0);
        }
        while let Some(node_idx) = queue.pop_front() {
            if let Some(entry) = excluded.get(&node_idx) {
                for node in entry.1.iter() {
                    if !reachable.contains(node) {
                        reachable.insert(*node);
                        if excluded.contains_key(&node.0) {
                            queue.push_back(node.0);
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
            for (in_node_idx, in_rtype) in in_nodes.iter() {
                if !excluded.contains_key(in_node_idx) {
                    for (out_node_idx, _) in out_nodes2.iter() {
                        if !excluded.contains_key(out_node_idx) {
                            condensed_edges.insert((*in_node_idx, *out_node_idx, *in_rtype));
                        }
                    }
                }
            }
        }
        condensed_edges
    }

    /// Fold the graph to remove excluded nodes and edges.
    ///
    /// An excluded node satisfies `node.is_excluded()` (it is not one of crates specfied
    /// by CallGraphConfig::included_crates).
    /// An excluded edge is an edge with at least one excluded endpoint.
    ///
    /// The outgoing edges of an excluded node are joined to the node's non-excluded parents.
    fn fold_excluded(&self) -> CallGraph {
        let mut excluded = MidpointExcludedMap::new();
        // 1. Find all excluded nodes
        let mut graph = self.graph.filter_map(
            |node_idx, node| {
                let included_crates = self
                    .config
                    .included_crates
                    .iter()
                    .map(|v| &**v)
                    .collect::<Vec<&str>>();
                if node.is_excluded(&included_crates) {
                    excluded.insert(
                        node_idx,
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
            |edge_idx, edge| {
                self.graph
                    .edge_endpoints(edge_idx)
                    .map(|(start_idx, end_idx)| {
                        excluded
                            .get_mut(&end_idx)
                            .map(|entry| entry.0.insert((start_idx, edge.rtype_id)));
                        excluded
                            .get_mut(&start_idx)
                            .map(|entry| entry.1.insert((end_idx, edge.rtype_id)));
                        edge.to_owned()
                    })
            },
        );
        // 3. Condense edges and insert
        for (in_idx, out_idx, rtype_id) in self.condense_edge_set(&excluded).iter() {
            let edge = CallGraphEdge::new(*rtype_id);
            graph.add_edge(*in_idx, *out_idx, edge);
        }
        // 4. Remove excluded nodes and edges
        graph = graph.filter_map(
            |node_idx, node| {
                if excluded.contains_key(&node_idx) {
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
            |node_idx, node| {
                let has_in_edges = self
                    .graph
                    .edges_directed(node_idx, Direction::Incoming)
                    .next()
                    .is_some();
                let has_out_edges = self
                    .graph
                    .edges_directed(node_idx, Direction::Outgoing)
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
        index_to_rtype: &HashMap<RTypeIdx, &RType>,
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
        for (_, rtype) in index_to_rtype.iter() {
            type_relations.extend(rtype.type_relations.to_owned());
        }
        type_relations
    }

    /// Convert the call graph to a datalog representation.
    ///
    /// Properties of the graph are converted into datalog input relations.
    /// - `Dom(n1, n2)`: `n1` dominates `n2`.
    /// - `Edge(id, n1, n2)`: There is a call edge from `n1` to `n2`.
    /// - `EdgeType(id, rtype_id)`: The edge has the type `rtype_id`.
    /// - `EqType(rtype_id1, rtype_id2)`: The type `rtype_id1` is equivalent to `rtype_id2`.
    /// - `Member(rtype_id1, rtype_id2)`: The type `rtype_id2` is a member of `rtype_id1`.
    fn to_datalog(
        &self,
        ddlog_path: &Path,
        type_map_path: &Path,
        type_relations_path: Option<&Path>,
    ) {
        let mut ctr: u32 = 0;
        let mut used_rtypes = HashSet::<RTypeIdx>::new();
        let mut output = DatalogOutput::new();
        // Output dominance relations
        self.graph.map(
            |node_idx1, _| {
                if let Some(nodes) = self.dominance.get(&node_idx1) {
                    for node_idx2 in nodes.iter() {
                        output.add_relation(DatalogRelation::new_dom(
                            node_idx1.index() as u32,
                            node_idx2.index() as u32,
                        ))
                    }
                }
            },
            |_, _| (),
        );
        // Output edge and edge type relations
        self.graph.map(
            |_, _| (),
            |edge_idx, edge| {
                if let Some((start_idx, end_idx)) = self.graph.edge_endpoints(edge_idx) {
                    output.add_relation(DatalogRelation::new_edge(
                        ctr,
                        start_idx.index() as u32,
                        end_idx.index() as u32,
                    ));
                    output.add_relation(DatalogRelation::new_edge_type(ctr, edge.rtype_id));
                    used_rtypes.insert(edge.rtype_id);
                    ctr += 1;
                }
            },
        );
        // Output type relations
        let mut index_to_rtype = HashMap::<RTypeIdx, &RType>::new();
        for (_, rtype) in self.rtypes.iter() {
            if used_rtypes.contains(&rtype.id) {
                index_to_rtype.insert(rtype.id, rtype);
            }
        }
        for type_relation in self
            .gather_type_relations(&index_to_rtype, type_relations_path)
            .iter()
        {
            if let Some(rtype1) = self.rtypes.get(&type_relation.rtype1) {
                if let Some(rtype2) = self.rtypes.get(&type_relation.rtype2) {
                    match type_relation.kind {
                        TypeRelationKind::Eq => {
                            output.add_relation(DatalogRelation::new_eq_type(rtype1.id, rtype2.id))
                        }
                        TypeRelationKind::Member => {
                            output.add_relation(DatalogRelation::new_member(rtype1.id, rtype2.id))
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
        match serde_json::to_string_pretty(&TypeMapOutput {
            map: index_to_rtype,
        })
        .map_err(|e| e.to_string())
        .and_then(|type_map_output| {
            fs::write(type_map_path, type_map_output).map_err(|e| e.to_string())
        }) {
            Ok(_) => (),
            Err(e) => panic!("Failed to write type map output: {:?}", e),
        };
    }

    /// Produce a dot file representation of the call graph
    /// for displaying with graphviz.
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
    /// Then produces datalog and / or dot file output of the call graph.
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

/// Temporary data structure for storing deserialzed
/// manually-added type relations.
#[derive(Serialize, Deserialize)]
struct TypeRelationsRaw {
    relations: Vec<TypeRelation>,
}

/// Temporary data structure for storing the type
/// map for serialization.
struct TypeMapOutput<'a> {
    map: HashMap<RTypeIdx, &'a RType>,
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

/// Represents an atomic datalog relation.
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

/// Structure for storing datalog relations
/// to later be output as a datalog file that can
/// be input into a datalog database.
struct DatalogOutput {
    relations: HashSet<DatalogRelation>,
}

impl fmt::Display for DatalogOutput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "start;")?;
        let mut relation_strs = Vec::<String>::new();
        for relation in self.relations.iter() {
            relation_strs.push(format!("insert {};", relation));
        }
        relation_strs.sort();
        let output = relation_strs.join("\n");
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
