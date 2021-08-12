use mirai_annotations::*;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{DefaultIx, NodeIndex};
use petgraph::visit::Bfs;
use petgraph::{Direction, Graph};
use rustc_hir::def_id::DefId;
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
enum CallGraphReduction {
    /// Only include nodes reachable from the given node.
    /// See `CallGraph::filter_reachable`.
    Slice(String),
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
struct CallGraphConfig {
    /// Optionally specifies location for graph to be output in dot format
    /// (for graphviz).
    dot_output_path: Option<String>,
    /// Optionally specifies location for graph to be output as datalog input
    /// relations.
    ddlog_output_path: Option<String>,
    /// Optionally specifies location for mapping from type identifiers to
    /// type strings.
    type_map_output_path: Option<String>,
    /// Optionally specifies the location for manually defined type relations
    /// to be imported.
    type_relations_path: Option<String>,
    /// A list of call graph reductions to apply sequentially
    /// to the call graph.
    reductions: Vec<CallGraphReduction>,
    /// A list of crates to include in the call graph.
    /// Nodes belonging to crates not in this list will be removed.
    included_crates: Vec<String>,
}

impl Default for CallGraphConfig {
    fn default() -> CallGraphConfig {
        CallGraphConfig {
            dot_output_path: None,
            ddlog_output_path: None,
            type_map_output_path: None,
            type_relations_path: None,
            reductions: Vec::<CallGraphReduction>::new(),
            included_crates: Vec::<String>::new(),
        }
    }
}

/// The type of a call graph node.
#[derive(Debug, Clone, PartialEq)]
enum NodeType {
    /// Regular root
    Root,
    /// Crate root: Starting point for analysis (pub fn)
    CRoot,
}

/// Nodes in the call graph are functions defined by the program
/// that is being analyzed.
#[derive(Debug, Clone)]
struct CallGraphNode {
    /// The name of the function (derived from its DefId).
    name: String,
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
    fn format_name(defid: DefId) -> String {
        let tmp1 = format!("{:?}", defid);
        let tmp2 = tmp1.split("~ ").collect::<Vec<&str>>()[1].to_owned();
        tmp2.replace(")", "")
    }

    /// A node is excluded if its name does not include any
    /// one of the included crates' names.
    pub fn is_excluded(&self, included_crates: &[String]) -> bool {
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
    /// States that t1 is a subtype of t2.
    Sub,
}

/// A type relation relates types `rtype1` and `rtype2` by a
/// `TypeRelationKind`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct TypeRelation {
    kind: TypeRelationKind,
    rtype1: String,
    rtype2: String,
}

impl TypeRelation {
    fn new_eq(t1: String, t2: String) -> TypeRelation {
        TypeRelation {
            kind: TypeRelationKind::Eq,
            rtype1: t1,
            rtype2: t2,
        }
    }

    fn new_sub(t1: String, t2: String) -> TypeRelation {
        TypeRelation {
            kind: TypeRelationKind::Sub,
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
    name: String,
    type_relations: HashSet<TypeRelation>,
}

impl RType {
    fn new(id: RTypeIdx, name: String) -> RType {
        RType {
            id,
            name: name.to_owned(),
            type_relations: RType::derive_type_relations(&name),
        }
    }

    /// Derive equality and subtyping relationships from the following
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
                base_type.to_owned(),
                base_type_new.to_owned(),
            ));
            base_type = base_type_new;
        }
        if base_type.contains('[') && base_type.contains(']') {
            let base_type_new = base_type.replace("[", "").replace("]", "");
            relations.insert(TypeRelation::new_sub(
                base_type.to_owned(),
                base_type_new.to_owned(),
            ));
            base_type = base_type_new;
        }
        if base_type.contains("mut") {
            let base_type_new = base_type.replace("mut ", "");
            relations.insert(TypeRelation::new_eq(
                base_type.to_owned(),
                base_type_new.to_owned(),
            ));
            base_type = base_type_new;
        }
        if base_type.contains('&') {
            let base_type_new = base_type.replace("&", "");
            relations.insert(TypeRelation::new_eq(base_type, base_type_new));
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
    /// A map from type identifier to type string
    rtypes: HashMap<String, RType>,
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
            rtypes: HashMap::<String, RType>::new(),
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
        if !self.nodes.contains_key(&defid) {
            let croot = CallGraphNode::new_root(defid);
            let node_idx = self.graph.add_node(croot);
            self.nodes.insert(defid, node_idx);
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
            .or_insert(HashSet::<NodeIdx>::new())
            .insert(node_idx2);
    }

    /// Add a new RType to the call graph's `rtypes`.
    fn add_rtype(&mut self, rtype_str: String) -> RTypeIdx {
        let new_rtype_id = self.rtypes.len() as RTypeIdx;
        match self.rtypes.entry(rtype_str.to_owned()) {
            Entry::Occupied(rtype) => rtype.get().id,
            Entry::Vacant(v) => v.insert(RType::new(new_rtype_id, rtype_str.to_owned())).id,
        }
    }

    /// Add a new edge to the call graph.
    /// The edge is a call edge from `caller_id` to `callee_id` with type `rtype_str`.
    pub fn add_edge(&mut self, caller_id: DefId, callee_id: DefId, rtype_str: String) {
        let rtype_id = self.add_rtype(rtype_str);
        let caller_node = self.get_or_insert_node(caller_id);
        let callee_node = self.get_or_insert_node(callee_id);
        self.graph
            .add_edge(caller_node, callee_node, CallGraphEdge::new(rtype_id));
    }

    /// Find a node in the call graph given a `name` that may appear as
    /// a substring within the node's name. The first such node is returned, if any.
    fn get_node_by_name(&self, name: &str) -> Option<NodeIdx> {
        for node_idx in self.graph.node_indices() {
            let node = self.graph.node_weight(node_idx).expect("Should exist");
            if node.name.contains(name) {
                return Some(node_idx);
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
                // The edge must exist in the graph because we mapped over the graph's edges.
                assume!(self.graph.edge_endpoints(edge_idx).is_some());
                let endpoints = self.graph.edge_endpoints(edge_idx).unwrap();
                if edges.contains(&endpoints) {
                    None
                } else {
                    edges.insert(endpoints);
                    Some(edge.to_owned())
                }
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
            // The node must exist at this point since we just retrieved it from the graph.
            assume!(self.graph.node_weight(node_idx).is_some());
            let node = self.graph.node_weight(node_idx).unwrap();
            if node.is_croot() {
                if croot.is_none() {
                    croot = Some(node_idx);
                    reachable.insert(node_idx);
                }
            } else {
                reachable.insert(node_idx);
            }
        }
        reachable
    }

    fn filter_reachable(&self, name: &str) -> CallGraph {
        let start_node = self
            .get_node_by_name(name)
            .expect("Valid start node required");
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
    }

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
            if excluded.contains_key(&node_idx) {
                for node in excluded.get(&node_idx).unwrap().1.iter() {
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

    fn fold_excluded(&self) -> CallGraph {
        let mut excluded = MidpointExcludedMap::new();
        // 1. Find all excluded nodes
        let mut graph = self.graph.filter_map(
            |node_idx, node| {
                if node.is_excluded(&self.config.included_crates) {
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
                let (start_idx, end_idx) =
                    self.graph.edge_endpoints(edge_idx).expect("Should exist");
                if excluded.contains_key(&end_idx) {
                    excluded
                        .get_mut(&end_idx)
                        .expect("Exists")
                        .0
                        .insert((start_idx, edge.rtype_id));
                }
                if excluded.contains_key(&start_idx) {
                    excluded
                        .get_mut(&start_idx)
                        .expect("Exists")
                        .1
                        .insert((end_idx, edge.rtype_id));
                }
                Some(edge.to_owned())
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

    fn shortened_node_names(&self) -> Graph<String, ()> {
        self.graph
            .filter_map(|_, node| Some(node.name.to_owned()), |_, _| Some(()))
    }

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

    fn to_datalog(
        &self,
        ddlog_path: &Path,
        type_map_path: &Path,
        type_relations_path: Option<&Path>,
    ) {
        let mut output = "start;\n".to_string();
        let mut ctr = 0;
        let mut used_rtypes = HashSet::<RTypeIdx>::new();
        self.graph.map(
            |node_idx1, _| {
                if self.dominance.contains_key(&node_idx1) {
                    for node_idx2 in self.dominance.get(&node_idx1).expect("Exists") {
                        output.push_str(
                            format!("Dom({}, {});\n", node_idx1.index(), node_idx2.index())
                                .as_str(),
                        );
                    }
                }
            },
            |_, _| (),
        );
        self.graph.map(
            |_, _| (),
            |edge_idx, edge| {
                let (start_idx, end_idx) = self.graph.edge_endpoints(edge_idx).expect("Exists");
                output.push_str(
                    format!(
                        "Edge({}, {}, {});\n",
                        ctr,
                        start_idx.index(),
                        end_idx.index()
                    )
                    .as_str(),
                );
                output.push_str(format!("EdgeType({}, {});\n", ctr, edge.rtype_id).as_str());
                used_rtypes.insert(edge.rtype_id);
                ctr += 1;
            },
        );
        let mut index_to_rtype = HashMap::<RTypeIdx, &RType>::new();
        for (_, rtype) in self.rtypes.iter() {
            if used_rtypes.contains(&rtype.id) {
                index_to_rtype.insert(rtype.id, rtype);
            }
        }
        let mut type_relations = HashSet::<TypeRelation>::new();
        // Insert input type relations from file
        match type_relations_path {
            Some(path) => {
                #[derive(Serialize, Deserialize)]
                struct TypeRelationsRaw {
                    relations: Vec<TypeRelation>,
                }
                let input_type_relations_str = fs::read_to_string(path).expect("Should work");
                let input_type_relations_raw: TypeRelationsRaw =
                    serde_json::from_str(&input_type_relations_str)
                        .expect("Failed to deserialize type relations");
                let mut input_type_relations = HashSet::<TypeRelation>::new();
                for relation in input_type_relations_raw.relations.iter() {
                    input_type_relations.insert(relation.to_owned());
                }
                type_relations.extend(input_type_relations);
            }
            None => (),
        }
        for (_, rtype) in index_to_rtype.iter() {
            type_relations.extend(rtype.type_relations.to_owned());
        }
        for type_relation in type_relations.iter() {
            if let Some(rtype1) = self.rtypes.get(&type_relation.rtype1) {
                if let Some(rtype2) = self.rtypes.get(&type_relation.rtype2) {
                    match type_relation.kind {
                        TypeRelationKind::Eq => output
                            .push_str(format!("TypeEq({}, {})\n", rtype1.id, rtype2.id).as_str()),
                        TypeRelationKind::Sub => output
                            .push_str(format!("TypeSub({}, {})\n", rtype2.id, rtype2.id).as_str()),
                    }
                }
            }
        }
        output.push_str("commit;\n");
        fs::write(ddlog_path, output).expect("Failed to write ddlog output");

        let mut type_map_output = "{\n".to_string();
        for (i, (rtype_id, rtype)) in index_to_rtype.iter().enumerate() {
            type_map_output.push_str(format!("\t\"{}\": \"{}\"", rtype_id, rtype.name).as_str());
            if i == index_to_rtype.len() - 1 {
                type_map_output.push('\n');
            } else {
                type_map_output.push_str(",\n");
            }
        }
        type_map_output.push('}');
        fs::write(type_map_path, type_map_output).expect("Failed to write type map output");
    }

    fn to_dot(&self, dot_path: &Path) {
        let output = format!(
            "{:?}",
            Dot::with_config(&self.shortened_node_names(), &[Config::EdgeNoLabel])
        );
        fs::write(dot_path, output).expect("Failed to write dot file output");
    }

    pub fn output(&self) {
        let call_graph = self.reduce_graph(self.clone(), &self.config.reductions);
        match &self.config.ddlog_output_path {
            Some(ddlog_path) => match &self.config.type_map_output_path {
                Some(type_map_path) => call_graph.to_datalog(
                    Path::new(&ddlog_path),
                    Path::new(&type_map_path),
                    self.config
                        .type_relations_path
                        .as_ref()
                        .map(|v| Path::new(v)),
                ),
                None => (),
            },
            None => (),
        };
        match &self.config.dot_output_path {
            Some(dot_path) => call_graph.to_dot(Path::new(&dot_path)),
            None => (),
        };
    }
}
