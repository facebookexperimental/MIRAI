// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use core::fmt;
use mirai_annotations::*;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{DefaultIx, NodeIndex};
use petgraph::visit::Bfs;
use petgraph::{Direction, Graph};
use regex::Regex;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
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

/// Configuration options for Datalog output
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatalogConfig {
    /// Specifies location for graph to be output as Datalog input relations.
    ddlog_output_path: Box<str>,
    /// Specifies location for mapping from type identifiers to type strings.
    type_map_output_path: Box<str>,
    /// Optionally specifies the location for manually defined type relations
    /// to be imported.
    type_relations_path: Option<Box<str>>,
    /// Datalog output backend to use.
    /// Currently, Differential Datalog and Soufflé are supported.
    datalog_backend: DatalogBackend,
}

impl DatalogConfig {
    pub fn new(
        ddlog_output_path: Box<str>,
        type_map_output_path: Box<str>,
        type_relations_path: Option<Box<str>>,
        datalog_backend: DatalogBackend,
    ) -> DatalogConfig {
        DatalogConfig {
            ddlog_output_path,
            type_map_output_path,
            type_relations_path,
            datalog_backend,
        }
    }

    pub fn get_ddlog_path(&self) -> &str {
        self.ddlog_output_path.as_ref()
    }

    pub fn get_type_map_path(&self) -> &str {
        self.type_map_output_path.as_ref()
    }

    pub fn get_type_relations_path(&self) -> Option<&str> {
        self.type_relations_path.as_deref()
    }

    pub fn get_datalog_backend(&self) -> DatalogBackend {
        self.datalog_backend
    }
}

/// Configuration options for call graph generation.
#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct CallGraphConfig {
    /// Optionally specified location for graph to be output as
    /// (call-site, caller, callee) triples, along with supporting tables.
    call_sites_output_path: Option<Box<str>>,
    /// Optionally specifies location for graph to be output in dot format
    /// (for Graphviz).
    dot_output_path: Option<Box<str>>,
    /// A list of call graph reductions to apply sequentially
    /// to the call graph.
    reductions: Vec<CallGraphReduction>,
    /// A list of crates to include in the call graph.
    /// Nodes belonging to crates not in this list will be removed.
    included_crates: Vec<Box<str>>,
    /// Datalog output configuration
    datalog_config: Option<DatalogConfig>,
}

impl CallGraphConfig {
    pub fn new(
        call_sites_output_path: Option<Box<str>>,
        dot_output_path: Option<Box<str>>,
        reductions: Vec<CallGraphReduction>,
        included_crates: Vec<Box<str>>,
        datalog_config: Option<DatalogConfig>,
    ) -> CallGraphConfig {
        CallGraphConfig {
            call_sites_output_path,
            dot_output_path,
            reductions,
            included_crates,
            datalog_config,
        }
    }

    pub fn get_call_sites_path(&self) -> Option<&str> {
        self.call_sites_output_path.as_deref()
    }

    pub fn get_dot_path(&self) -> Option<&str> {
        self.dot_output_path.as_deref()
    }

    pub fn get_ddlog_path(&self) -> Option<&str> {
        self.datalog_config
            .as_ref()
            .map(|config| config.get_ddlog_path())
    }

    pub fn get_type_map_path(&self) -> Option<&str> {
        self.datalog_config
            .as_ref()
            .map(|config| config.get_type_map_path())
    }

    pub fn get_datalog_backend(&self) -> Option<DatalogBackend> {
        self.datalog_config
            .as_ref()
            .map(|config| config.get_datalog_backend())
    }
}

/// The type of a call graph node.
#[derive(Debug, Clone, Eq, PartialEq)]
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
        let tmp1 = format!("{defid:?}");
        let tmp2: &str = tmp1.split("~ ").collect::<Vec<&str>>()[1];
        let tmp3 = tmp2.replace(')', "");
        let lhs = tmp3.split('[').collect::<Vec<&str>>()[0];
        let rhs = tmp3.split(']').collect::<Vec<&str>>()[1];
        format!("{lhs}{rhs}").into_boxed_str()
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

const COLLECTION_TYPES: &[&str] = &[
    "std::slice::Iter",
    "std::iter::Enumerate",
    "std::iter::Map",
    "std::collections::HashSet",
    "std::collections::HashMap",
    "std::vec::Vec",
];

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum SimpleType {
    Base(Box<str>),
    Collection(Box<str>),
}

/// Types associated with call graph edges
#[derive(Debug, Clone)]
struct EdgeType {
    /// Unique identifier for this time
    id: TypeId,
    // Textual representation of the type
    name: Box<str>,
}

impl EdgeType {
    fn new(id: TypeId, name: Box<str>) -> EdgeType {
        EdgeType { id, name }
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
#[derive(Clone)]
pub struct CallGraph<'tcx> {
    /// Configuration for the call graph
    config: CallGraphConfig,
    /// A context to use for getting the information about DefIds that is needed
    /// to generate fully qualified names for them.
    tcx: TyCtxt<'tcx>,
    /// Functions that are defined in other crates, or that have no bodies.
    /// This does not include functions that are specialized with call site information.
    non_local_defs: HashSet<DefId>,
    /// (call_site, (caller, callee)). One entry per call that is reachable from
    /// an analysis root.
    call_sites: HashMap<rustc_span::Span, (DefId, DefId)>,
    /// The graph structure capturing calls between nodes
    graph: Graph<CallGraphNode, CallGraphEdge>,
    /// A map from DefId to node information
    nodes: HashMap<DefId, NodeId>,
    /// A map from type string to an EdgeType instance
    edge_types: HashMap<Box<str>, EdgeType>,
    /// Dominance information
    dominance: HashMap<DefId, HashSet<DefId>>,
}

impl<'tcx> CallGraph<'tcx> {
    pub fn new(path_to_config: Option<String>, tcx: TyCtxt<'tcx>) -> CallGraph {
        let config = match path_to_config {
            Some(path) => CallGraph::parse_config(Path::new(&path)),
            None => CallGraphConfig::default(),
        };
        CallGraph {
            config,
            tcx,
            non_local_defs: HashSet::new(),
            call_sites: HashMap::new(),
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
            Err(e) => unrecoverable!("Failed to read call graph config: {:?}", e),
        }
    }

    pub fn needs_edges(&self) -> bool {
        self.config.dot_output_path.is_some() || self.config.datalog_config.is_some()
    }

    /// Produce an updated call graph structure that preserves all of the
    /// fields except `graph`, which is replaced.
    fn update(&self, graph: Graph<CallGraphNode, CallGraphEdge>) -> CallGraph<'tcx> {
        CallGraph {
            config: self.config.clone(),
            tcx: self.tcx,
            graph,
            non_local_defs: self.non_local_defs.clone(),
            call_sites: self.call_sites.clone(),
            nodes: self.nodes.clone(),
            edge_types: self.edge_types.clone(),
            dominance: self.dominance.clone(),
        }
    }

    /// Add a new crate root node to the call graph.
    pub fn add_croot(&mut self, defid: DefId) {
        let croot = CallGraphNode::new_croot(defid);
        match self.nodes.entry(defid) {
            Entry::Occupied(node) => {
                // Replace non-croot existing node
                let node_id = node.get().to_owned();
                if let Some(node_weight) = self.graph.node_weight_mut(node_id) {
                    *node_weight = croot;
                }
            }
            Entry::Vacant(v) => {
                let node_id = self.graph.add_node(croot);
                let _ = *v.insert(node_id);
            }
        };
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

    // Record a call site in the call graph. Only do so if call_sites_output_path is specified
    // and omit any calls where the caller is known to be external to the crate being analyzed.
    //todo: to make this a precise as possible a callee should only be marked as external
    // if no Trait type is reachable from a parameter type.
    pub fn add_call_site(
        &mut self,
        loc: rustc_span::Span,
        caller: DefId,
        callee: DefId,
        external_callee: bool,
    ) {
        if self.config.call_sites_output_path.is_some() && !self.non_local_defs.contains(&caller) {
            self.call_sites.insert(loc, (caller, callee));
            if external_callee {
                self.non_local_defs.insert(callee);
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
    fn deduplicate_edges(&self) -> CallGraph<'tcx> {
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
    fn filter_reachable(&self, name: &str) -> CallGraph<'tcx> {
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
            panic!("Failed to filter graph; could not find start node: {name}");
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
    fn fold_excluded(&self) -> CallGraph<'tcx> {
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
    fn filter_no_edges(&self) -> CallGraph<'tcx> {
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
    fn reduce_graph(
        &self,
        call_graph: CallGraph<'tcx>,
        reductions: &[CallGraphReduction],
    ) -> CallGraph<'tcx> {
        reductions
            .iter()
            .fold(call_graph, |graph, reduction| match reduction {
                CallGraphReduction::Slice(crate_name) => graph.filter_reachable(crate_name),
                CallGraphReduction::Fold => graph.fold_excluded(),
                CallGraphReduction::Deduplicate => graph.deduplicate_edges(),
                CallGraphReduction::Clean => graph.filter_no_edges(),
            })
    }

    /// Extract base types from collection types. Ex:
    /// - std::slice::Iter<T> == [T]
    /// - std::iter::Enumerate<std::slice::Iter<T1, T2>> == [T1], [T2]
    fn extract_iterator_type(&self, name: &str) -> Vec<Box<str>> {
        let s1 = name.replace("&mut ", "");
        let s2 = s1.replace('&', "");
        let mut base_types = Vec::<Box<str>>::new();
        let type_regex = Regex::new(r"(?P<type>[^<>,\s]+)").unwrap();
        for caps in type_regex.captures_iter(&s2) {
            let cap_type = &caps["type"];
            if !COLLECTION_TYPES.contains(&cap_type) {
                base_types.push(format!("[{cap_type}]").into_boxed_str());
            }
        }
        base_types
    }

    /// Simplify a type according to these heuristics:
    /// - &t == t
    /// - mut t == t
    /// - [t] > t
    fn simplify_single_type(&self, name: &str) -> SimpleType {
        let mut base_type = name.to_owned();
        base_type = base_type.replace("mut ", "");
        base_type = base_type.replace('&', "");
        if base_type.contains('[') && base_type.contains(']') {
            base_type = base_type.replace(['[', ']'], "");
            SimpleType::Collection(base_type.into_boxed_str())
        } else {
            SimpleType::Base(base_type.into_boxed_str())
        }
    }

    /// Simplify a type that may be a collection
    fn simplify_type(&self, name: &str) -> Vec<SimpleType> {
        let is_collection_type: bool = COLLECTION_TYPES.iter().any(|x| name.contains(x));
        if is_collection_type {
            let base_types = self.extract_iterator_type(name);
            base_types
                .iter()
                .map(|x| self.simplify_single_type(x))
                .collect::<Vec<SimpleType>>()
        } else {
            vec![self.simplify_single_type(name)]
        }
    }

    /// Check whether two types are nominally equivalent or
    /// equivalent according to input type relations
    fn simple_type_eq(&self, t1: &str, t2: &str, eq_map: &HashMap<Box<str>, Box<str>>) -> bool {
        if t1 == t2 {
            return true;
        } else {
            if let Some(map_t1) = eq_map.get(t2) {
                if t1 == map_t1.as_ref() {
                    return true;
                }
            }
            if let Some(map_t2) = eq_map.get(t1) {
                if t2 == map_t2.as_ref() {
                    return true;
                }
            }
        }
        false
    }

    /// Derive all type relations
    fn derive_all_relations(
        &self,
        type_map: &HashMap<TypeId, Box<str>>,
        eq_map: &HashMap<Box<str>, Box<str>>,
        relations: &mut HashSet<TypeRelation>,
    ) {
        let simple_types: Vec<(&str, SimpleType)> =
            type_map
                .iter()
                .fold(Vec::<(&str, SimpleType)>::new(), |mut acc, (_, t)| {
                    acc.extend(
                        self.simplify_type(t.as_ref())
                            .into_iter()
                            .map(|simple_t| (t.as_ref(), simple_t)),
                    );
                    acc
                });
        for (t1, simple_t1) in simple_types.iter() {
            for (t2, simple_t2) in simple_types.iter() {
                if t1 != t2 {
                    match (simple_t1, simple_t2) {
                        // Case 1: [t] > t
                        (SimpleType::Collection(t1_base), SimpleType::Base(t2_base)) => {
                            if self.simple_type_eq(t1_base.as_ref(), t2_base.as_ref(), eq_map) {
                                relations.insert(TypeRelation::new_member(
                                    (*t1).to_owned().into_boxed_str(),
                                    (*t2).to_owned().into_boxed_str(),
                                ));
                            }
                        }
                        // Case 2: t < [t]
                        (SimpleType::Base(t1_base), SimpleType::Collection(t2_base)) => {
                            if self.simple_type_eq(t1_base.as_ref(), t2_base.as_ref(), eq_map) {
                                relations.insert(TypeRelation::new_member(
                                    (*t2).to_owned().into_boxed_str(),
                                    (*t1).to_owned().into_boxed_str(),
                                ));
                            }
                        }
                        // Case 3: [t] = [t] | t = t
                        (SimpleType::Collection(t1_base), SimpleType::Collection(t2_base))
                        | (SimpleType::Base(t1_base), SimpleType::Base(t2_base)) => {
                            if self.simple_type_eq(t1_base.as_ref(), t2_base.as_ref(), eq_map) {
                                // Deterministic lexicographic ordering
                                if t1 < t2 {
                                    relations.insert(TypeRelation::new_eq(
                                        (*t1).to_owned().into_boxed_str(),
                                        (*t2).to_owned().into_boxed_str(),
                                    ));
                                } else {
                                    relations.insert(TypeRelation::new_eq(
                                        (*t2).to_owned().into_boxed_str(),
                                        (*t1).to_owned().into_boxed_str(),
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn get_input_equivalences(
        &self,
        input_relations: &HashSet<TypeRelation>,
    ) -> HashMap<Box<str>, Box<str>> {
        input_relations
            .iter()
            .flat_map(|relation| match relation.kind {
                TypeRelationKind::Eq => vec![
                    (relation.type1.to_owned(), relation.type2.to_owned()),
                    (relation.type2.to_owned(), relation.type1.to_owned()),
                ],
                TypeRelationKind::Member => vec![],
            })
            .collect::<HashMap<Box<str>, Box<str>>>()
    }

    /// Gather together type relations from the input type relations file
    /// as well as type relations derived from program types.
    fn gather_type_relations(
        &self,
        type_map: &mut HashMap<TypeId, Box<str>>,
        type_relations_path: Option<&Path>,
    ) -> HashSet<TypeRelation> {
        let type_to_index: HashMap<Box<str>, TypeId> = type_map
            .iter()
            .map(|(type_id, type_str)| (type_str.to_owned(), *type_id))
            .collect();
        let mut type_relations = HashSet::<TypeRelation>::new();
        // If there is no maximum element then the type map is empty
        // and we default to a starting ID of 0.
        let mut max_id: u32 = *type_map.keys().max().unwrap_or(&0);
        if let Some(path) = type_relations_path {
            let input_type_relations_raw: TypeRelationsRaw = match fs::read_to_string(path)
                .map_err(|e| e.to_string())
                .and_then(|input_type_relations_str| {
                    serde_json::from_str(&input_type_relations_str).map_err(|e| e.to_string())
                }) {
                Ok(relations) => relations,
                Err(e) => panic!("Failed to read input type relations: {e:?}"),
            };
            let input_relations = input_type_relations_raw.relations;
            for relation in input_relations.iter() {
                let relation_to_insert = match relation.kind {
                    TypeRelationKind::Eq => {
                        // Deterministic lexicographic ordering
                        if relation.type1 < relation.type2 {
                            TypeRelation::new_eq(
                                relation.type1.to_owned(),
                                relation.type2.to_owned(),
                            )
                        } else {
                            TypeRelation::new_eq(
                                relation.type2.to_owned(),
                                relation.type1.to_owned(),
                            )
                        }
                    }
                    TypeRelationKind::Member => relation.to_owned(),
                };
                type_relations.insert(relation_to_insert);
                match type_to_index.get(&relation.type1) {
                    Some(_) => {}
                    None => {
                        max_id += 1;
                        type_map.insert(max_id, relation.type1.to_owned());
                    }
                }
                match type_to_index.get(&relation.type2) {
                    Some(_) => {}
                    None => {
                        max_id += 1;
                        type_map.insert(max_id, relation.type2.to_owned());
                    }
                }
            }
        }
        let eq_map = self.get_input_equivalences(&type_relations);
        self.derive_all_relations(type_map, &eq_map, &mut type_relations);
        type_relations
    }

    /// Convert the call graph to a Datalog representation.
    ///
    /// Properties of the graph are converted into input relations.
    fn to_datalog(
        &self,
        backend: DatalogBackend,
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
        let mut index_to_type = HashMap::<TypeId, Box<str>>::new();
        for (_, edge_type) in self.edge_types.iter() {
            if used_types.contains(&edge_type.id) {
                index_to_type.insert(edge_type.id, edge_type.name.to_owned());
            }
        }
        let type_relations = self.gather_type_relations(&mut index_to_type, type_relations_path);
        let mut type_to_index = HashMap::<Box<str>, TypeId>::new();
        for (type_id, type_str) in index_to_type.iter() {
            type_to_index.insert(type_str.to_owned(), *type_id);
        }
        for type_relation in type_relations.iter() {
            if let Some(type_id1) = type_to_index.get(type_relation.type1.as_ref()) {
                if let Some(type_id2) = type_to_index.get(type_relation.type2.as_ref()) {
                    match type_relation.kind {
                        TypeRelationKind::Eq => {
                            output.add_relation(DatalogRelation::new_eq_type(*type_id1, *type_id2))
                        }
                        TypeRelationKind::Member => {
                            output.add_relation(DatalogRelation::new_member(*type_id1, *type_id2))
                        }
                    }
                }
            }
        }
        // Output the Datalog operations in the format of the configured
        // Datalog backend
        let output_result = match backend {
            DatalogBackend::DifferentialDatalog => output.to_differential_datalog(ddlog_path),
            DatalogBackend::Souffle => output.to_souffle(ddlog_path),
        };
        match output_result {
            Ok(_) => (),
            Err(e) => panic!("Failed to write ddlog output: {e:?}"),
        }
        // Output the type map
        match serde_json::to_string_pretty(&TypeMapOutput { map: index_to_type })
            .map_err(|e| e.to_string())
            .and_then(|type_map_output| {
                fs::write(type_map_path, type_map_output).map_err(|e| e.to_string())
            }) {
            Ok(_) => (),
            Err(e) => panic!("Failed to write type map output: {e:?}"),
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
            Err(e) => panic!("Failed to write dot file output: {e:?}"),
        };
    }

    fn to_call_sites(&self, call_site_path: &Path) {
        let call_site_info = CallSiteOutput::new(self);
        match serde_json::to_string_pretty(&call_site_info)
            .map_err(|e| e.to_string())
            .and_then(|call_site_output| {
                fs::write(call_site_path, call_site_output).map_err(|e| e.to_string())
            }) {
            Ok(_) => (),
            Err(e) => panic!("Failed to write call site output: {e}"),
        };
    }

    /// Top-level output function.
    ///
    /// First applies a set of reductions to the call graph.
    /// Then produces Datalog and / or dot file output of the call graph.
    pub fn output(&self) {
        let call_graph = self.reduce_graph(self.clone(), &self.config.reductions);
        if let Some(datalog_config) = &self.config.datalog_config {
            call_graph.to_datalog(
                datalog_config.get_datalog_backend(),
                Path::new(datalog_config.get_ddlog_path()),
                Path::new(datalog_config.get_type_map_path()),
                datalog_config.get_type_relations_path().map(Path::new),
            );
        }
        if let Some(dot_path) = &self.config.dot_output_path {
            call_graph.to_dot(Path::new(dot_path.as_ref()));
        }
        if let Some(call_path) = &self.config.call_sites_output_path {
            call_graph.to_call_sites(Path::new(call_path.as_ref()));
        }
    }
}

/// Supported Datalog output formats
#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum DatalogBackend {
    DifferentialDatalog,
    Souffle,
}

/// Temporary data structure for storing deserialized
/// manually-added type relations.
#[derive(Serialize, Deserialize)]
struct TypeRelationsRaw {
    relations: Vec<TypeRelation>,
}

/// Temporary data structure for storing the type
/// map for serialization.
struct TypeMapOutput {
    map: HashMap<TypeId, Box<str>>,
}

impl Serialize for TypeMapOutput {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut map = serializer.serialize_map(Some(self.map.len()))?;
        let mut map_entries: Vec<_> = self.map.iter().collect();
        map_entries.sort_by_key(|k| k.0);
        for (k, v) in map_entries.iter() {
            map.serialize_entry(&k.to_string(), v.as_ref())?;
        }
        map.end()
    }
}

/// Represents the types of datalog input relations
/// that are generated.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum RelationType {
    /// `Dom(n1, n2)`: `n1` dominates `n2`.
    Dom,
    /// `Edge(id, n1, n2)`: There is a call edge from `n1` to `n2`.
    Edge,
    /// `EdgeType(id, type_id)`: The edge has the type associated with `type_id`.
    EdgeType,
    /// `EqType(type_id1, type_id2)`: The type `type_id1` is equivalent to `type_id2`.
    EqType,
    /// `Member(type_id1, type_id2)`: The type `type_id2` is a member of `type_id1`.
    Member,
}

impl fmt::Display for RelationType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RelationType::Dom => write!(f, "Dom"),
            RelationType::Edge => write!(f, "Edge"),
            RelationType::EdgeType => write!(f, "EdgeType"),
            RelationType::EqType => write!(f, "EqType"),
            RelationType::Member => write!(f, "Member"),
        }
    }
}

/// Represents an atomic Datalog relation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct DatalogRelation {
    /// A relation has a name.
    name: RelationType,
    /// As well as one or more operands.
    operands: Vec<u32>,
}

impl DatalogRelation {
    pub fn new_dom(n1: u32, n2: u32) -> DatalogRelation {
        DatalogRelation {
            name: RelationType::Dom,
            operands: vec![n1, n2],
        }
    }

    pub fn new_edge(id: u32, n1: u32, n2: u32) -> DatalogRelation {
        DatalogRelation {
            name: RelationType::Edge,
            operands: vec![id, n1, n2],
        }
    }

    pub fn new_edge_type(id: u32, t: u32) -> DatalogRelation {
        DatalogRelation {
            name: RelationType::EdgeType,
            operands: vec![id, t],
        }
    }

    pub fn new_eq_type(t1: u32, t2: u32) -> DatalogRelation {
        DatalogRelation {
            name: RelationType::EqType,
            operands: vec![t1, t2],
        }
    }

    pub fn new_member(t1: u32, t2: u32) -> DatalogRelation {
        DatalogRelation {
            name: RelationType::Member,
            operands: vec![t1, t2],
        }
    }

    /// Format the relation for Differential Datalog
    fn to_differential_datalog(&self) -> String {
        format!(
            "{}({})",
            self.name,
            self.operands
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<String>>()
                .join(",")
        )
    }

    /// Format the relation for Soufflé Datalog
    fn to_souffle(&self) -> String {
        self.operands
            .iter()
            .map(|x| x.to_string())
            .collect::<Vec<String>>()
            .join(",")
    }
}

/// Structure for storing Datalog relations
/// to later be output as a Datalog file that can
/// be input into a Datalog database.
struct DatalogOutput {
    relations: HashSet<DatalogRelation>,
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

    /// Output `relations` formatted for the given Datalog backend.
    /// Optionally, `filter` the output to only include relations of a
    /// particular `RelationType`.
    fn output_relation_set(
        &self,
        relations: &HashSet<DatalogRelation>,
        filter: Option<RelationType>,
        backend: DatalogBackend,
    ) -> String {
        let mut relation_strings = Vec::<String>::new();
        for relation in relations.iter() {
            if filter.map_or(true, |x| x == relation.name) {
                match backend {
                    DatalogBackend::DifferentialDatalog => relation_strings
                        .push(format!("insert {};", relation.to_differential_datalog())),
                    DatalogBackend::Souffle => relation_strings.push(relation.to_souffle()),
                };
            }
        }
        relation_strings.sort();
        relation_strings.join("\n")
    }

    /// Output the Datalog relations to a file in the format
    /// expected by Differential Datalog
    pub fn to_differential_datalog(&self, path: &Path) -> std::io::Result<()> {
        fs::write(
            path,
            format!(
                "start;\n{}\ncommit;",
                self.output_relation_set(
                    &self.relations,
                    None,
                    DatalogBackend::DifferentialDatalog
                )
            ),
        )
    }

    /// Output the Datalog relations to a set of files (one file per relation type)
    /// in the format expected by Soufflé Datalog
    pub fn to_souffle(&self, path: &Path) -> std::io::Result<()> {
        fs::write(
            path.join("Dom.facts"),
            self.output_relation_set(
                &self.relations,
                Some(RelationType::Dom),
                DatalogBackend::Souffle,
            ),
        )?;
        fs::write(
            path.join("Edge.facts"),
            self.output_relation_set(
                &self.relations,
                Some(RelationType::Edge),
                DatalogBackend::Souffle,
            ),
        )?;
        fs::write(
            path.join("EdgeType.facts"),
            self.output_relation_set(
                &self.relations,
                Some(RelationType::EdgeType),
                DatalogBackend::Souffle,
            ),
        )?;
        fs::write(
            path.join("EqType.facts"),
            self.output_relation_set(
                &self.relations,
                Some(RelationType::EqType),
                DatalogBackend::Souffle,
            ),
        )?;
        fs::write(
            path.join("Member.facts"),
            self.output_relation_set(
                &self.relations,
                Some(RelationType::Member),
                DatalogBackend::Souffle,
            ),
        )
    }
}

/// Summarizes the call graph of the current crate. Calls to higher order external functions
/// are treated as local calls (i.e. the calls they make are also included here) because
/// their call graphs are imprecise unless specialized with call site information.
#[derive(Serialize)]
struct CallSiteOutput {
    /// Relative paths from the crate root directory for files that are compiled
    /// by this build. Absolute (but "virtual") paths for files from prebuild libraries, such as the
    /// Rust standard library.
    files: Vec<String>,
    /// Metadata for each callable that is mentioned in the calls collection.
    /// The index of the callable in this vector is the caller/callee index
    /// that appears in a calls entry.
    callables: Vec<Callable>,
    /// File index, line, column, caller index, callee index.
    /// Line and column numbers are 1 based.
    calls: Vec<(usize, usize, usize, usize, usize)>,
}

/// Metadata for each callable that is mentioned in the calls collection.
#[derive(Serialize)]
struct Callable {
    /// Fully qualified callable name including name of defining crate.
    name: String,
    /// The index of the CallSiteOutput.files entry that provides the path
    /// of the source file in which this callable is defined.
    file_index: Option<usize>,
    /// The 1-based number of the first source line of the callable.
    first_line: Option<usize>,
    /// If true, this callable is defined in the crate being analyzed, or it is a higher
    /// order/generic function that may need specialized call site information before its
    /// call graph can be precisely determined. If true, calls made inside this function
    /// will show up in CallSiteOutput.calls.
    local: bool,
}

impl CallSiteOutput {
    pub fn new(call_graph: &CallGraph) -> CallSiteOutput {
        let source_map = call_graph.tcx.sess.source_map();
        let mut files = vec![];
        let mut file_map = HashMap::<rustc_span::FileName, usize>::new();
        let mut callables = vec![];
        let mut callable_index = HashMap::<DefId, usize>::new();
        let mut calls = vec![];
        let mut sites: Vec<(&rustc_span::Span, &(DefId, DefId))> =
            call_graph.call_sites.iter().collect();
        sites.sort();
        for (loc, (caller, callee)) in sites.iter() {
            let source_loc = loc.source_callsite();
            if let Ok(line_and_file) = source_map.span_to_lines(source_loc) {
                let file_index =
                    Self::get_file_index(&mut files, &mut file_map, &line_and_file.file.name);
                let line = line_and_file.lines[0];
                let caller_index = Self::get_callable_index(
                    &mut callables,
                    &mut callable_index,
                    *caller,
                    call_graph,
                    &mut files,
                    &mut file_map,
                );
                let callee_index = Self::get_callable_index(
                    &mut callables,
                    &mut callable_index,
                    *callee,
                    call_graph,
                    &mut files,
                    &mut file_map,
                );
                calls.push((
                    file_index,
                    line.line_index + 1,
                    line.start_col.0 + 1,
                    caller_index,
                    callee_index,
                ));
            }
        }
        CallSiteOutput {
            files,
            callables,
            calls,
        }
    }

    fn get_file_index(
        files: &mut Vec<String>,
        file_map: &mut HashMap<rustc_span::FileName, usize>,
        fname: &rustc_span::FileName,
    ) -> usize {
        match file_map.entry(fname.clone()) {
            Entry::Occupied(o) => *o.get(),
            Entry::Vacant(v) => {
                let index = files.len();
                v.insert(index);
                let mut file_name = None;
                if let rustc_span::FileName::Real(real_fname) = fname {
                    if let Some(p) = real_fname.remapped_path_if_available().to_str() {
                        file_name = Some(p.into());
                    }
                }
                files.push(file_name.unwrap_or_else(|| "unknown".into()));
                index
            }
        }
    }

    fn get_callable_index(
        callables: &mut Vec<Callable>,
        callable_index: &mut HashMap<DefId, usize>,
        callable: DefId,
        call_graph: &CallGraph,
        files: &mut Vec<String>,
        file_map: &mut HashMap<rustc_span::FileName, usize>,
    ) -> usize {
        let index = callable_index.len();
        match callable_index.entry(callable) {
            Entry::Occupied(o) => *o.get(),
            Entry::Vacant(v) => {
                v.insert(index);
                let tcx = call_graph.tcx;
                let name = crate::utils::def_id_as_qualified_name_str(tcx, callable).to_string();
                let local = !call_graph.non_local_defs.contains(&callable);
                let span = tcx.def_span(callable);
                let source_map = tcx.sess.source_map();
                let mut file_index = None;
                let mut first_line = None;
                if let Ok(line_and_file) = source_map.span_to_lines(span) {
                    file_index = Some(Self::get_file_index(
                        files,
                        file_map,
                        &line_and_file.file.name,
                    ));
                    first_line = line_and_file.lines.get(0).map(|l| l.line_index + 1);
                }
                let callable = Callable {
                    name,
                    file_index,
                    first_line,
                    local,
                };
                callables.push(callable);
                index
            }
        }
    }
}
