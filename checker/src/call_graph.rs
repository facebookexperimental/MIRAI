use petgraph::dot::{Config, Dot};
use petgraph::graph::{DefaultIx, EdgeIndex, NodeIndex};
use petgraph::visit::Bfs;
use petgraph::{Direction, Graph};
use rustc_hir::def_id::DefId;
use std::collections::{HashMap, HashSet, VecDeque};

type NodeIdx = NodeIndex<DefaultIx>;
type EdgeIdx = EdgeIndex<DefaultIx>;
type HalfRawEdge = (NodeIdx, u32);
type RawEdge = (NodeIdx, NodeIdx, u32);
type MidpointExcludedMap = HashMap<NodeIdx, (HashSet<HalfRawEdge>, HashSet<HalfRawEdge>)>;

const EXCLUDED_CRATES: &[&str] = &[
    "std",
    "core",
    "alloc",
    "mirai_annotations",
    "anyhow",
    "bcs",
    "ref_cast",
];

// The type of a call graph node
#[derive(Debug, Clone, PartialEq)]
enum NodeType {
    // Regular root
    Root,
    // Crate root: Starting point for analysis (pub fn)
    CRoot,
}

#[derive(Debug, Clone)]
struct CallGraphNode {
    // A Node has a DefId and type.
    // Nodes are uniquely identified by their DefId.
    index: u32,
    defid: DefId,
    name: String,
    ntype: NodeType,
    graph_node: NodeIdx,
}

impl CallGraphNode {
    pub fn new_croot(index: u32, defid: DefId, graph_node: NodeIdx) -> CallGraphNode {
        CallGraphNode {
            index,
            defid,
            name: CallGraphNode::format_name(defid),
            ntype: NodeType::CRoot,
            graph_node,
        }
    }

    pub fn new_root(index: u32, defid: DefId, graph_node: NodeIdx) -> CallGraphNode {
        CallGraphNode {
            index,
            defid,
            name: CallGraphNode::format_name(defid),
            ntype: NodeType::Root,
            graph_node,
        }
    }

    fn format_name(defid: DefId) -> String {
        let tmp1 = format!("{:?}", defid);
        let tmp2 = tmp1.split("~ ").collect::<Vec<&str>>()[1].to_owned();
        tmp2.replace(")", "")
    }

    pub fn is_excluded(&self) -> bool {
        let mut is_std = false;
        for crate_name in EXCLUDED_CRATES.iter() {
            if self.name.contains(crate_name) {
                is_std = true;
                break;
            }
        }
        is_std
    }

    pub fn is_croot(&self) -> bool {
        self.ntype == NodeType::CRoot
    }
}

#[derive(Debug, Eq, Clone)]
struct CallGraphEdge {
    // An Edge connects two nodes.
    // Edges are uniquely identified by their index. They
    // have a caller_id, callee_id, and an associated Rust type.
    index: u32,
    caller_id: u32,
    callee_id: u32,
    rtype: String,
    graph_edge: EdgeIdx,
}

impl PartialEq for CallGraphEdge {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl CallGraphEdge {
    pub fn new(
        index: u32,
        caller_id: u32,
        callee_id: u32,
        rtype: String,
        graph_edge: EdgeIdx,
    ) -> CallGraphEdge {
        CallGraphEdge {
            index,
            caller_id,
            callee_id,
            rtype,
            graph_edge,
        }
    }
}

pub struct CallGraph {
    // The graph structure capturing calls between nodes
    graph: Graph<DefId, u32>,
    // A map from DefId to node information
    nodes: HashMap<DefId, CallGraphNode>,
    // Mapping from graph edge indexes to edge data
    edges: HashMap<EdgeIdx, CallGraphEdge>,
    // Bi-directional mapping of type number to type string
    rtype_to_index: HashMap<String, u32>,
    index_to_rtype: HashMap<u32, String>,
    // Dominance information
    dominance: HashMap<NodeIdx, HashSet<NodeIdx>>,
}

impl Default for CallGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl CallGraph {
    pub fn new() -> CallGraph {
        CallGraph {
            graph: Graph::<DefId, u32>::new(),
            nodes: HashMap::<DefId, CallGraphNode>::new(),
            edges: HashMap::<EdgeIdx, CallGraphEdge>::new(),
            rtype_to_index: HashMap::<String, u32>::new(),
            index_to_rtype: HashMap::<u32, String>::new(),
            dominance: HashMap::<NodeIdx, HashSet<NodeIdx>>::new(),
        }
    }

    fn update(&self, graph: Graph<DefId, u32>) -> CallGraph {
        CallGraph {
            graph,
            nodes: self.nodes.clone(),
            edges: self.edges.clone(),
            rtype_to_index: self.rtype_to_index.clone(),
            index_to_rtype: self.index_to_rtype.clone(),
            dominance: self.dominance.clone(),
        }
    }

    pub fn add_croot(&mut self, defid: DefId) {
        let node_id = self.nodes.len() as u32;
        let graph_node = self.graph.add_node(defid);
        let croot = CallGraphNode::new_croot(node_id, defid, graph_node);
        self.nodes.insert(defid, croot);
    }

    pub fn add_root(&mut self, defid: DefId) {
        if !self.nodes.contains_key(&defid) {
            let node_id = self.nodes.len() as u32;
            let graph_node = self.graph.add_node(defid);
            let root = CallGraphNode::new_root(node_id, defid, graph_node);
            self.nodes.insert(defid, root);
        }
    }

    pub fn add_dom(&mut self, defid1: DefId, defid2: DefId) {
        if !self.nodes.contains_key(&defid1) {
            self.add_root(defid1);
        }
        if !self.nodes.contains_key(&defid2) {
            self.add_root(defid2);
        }
        let node_idx1 = self.nodes.get(&defid1).expect("Exists").graph_node;
        let node_idx2 = self.nodes.get(&defid2).expect("Exists").graph_node;
        if !self.dominance.contains_key(&node_idx1) {
            self.dominance.insert(node_idx1, HashSet::<NodeIdx>::new());
        }
        self.dominance.get_mut(&node_idx1).expect("Exists").insert(node_idx2);
    }

    pub fn add_edge(&mut self, caller_id: DefId, callee_id: DefId, rtype: String) {
        let edge_id = self.edges.len() as u32;
        if !self.nodes.contains_key(&caller_id) {
            self.add_root(caller_id);
        }
        if !self.nodes.contains_key(&callee_id) {
            self.add_root(callee_id);
        }
        let caller_node = self
            .nodes
            .get(&caller_id)
            .expect("The node must exist at this point.");
        let callee_node = self
            .nodes
            .get(&callee_id)
            .expect("The node must exist at this point.");
        if !self.rtype_to_index.contains_key(&rtype) {
            let rtype_id = self.rtype_to_index.len() as u32;
            self.rtype_to_index.insert(rtype.to_owned(), rtype_id);
            self.index_to_rtype.insert(rtype_id, rtype.to_owned());
        }
        let rtype_id = *self.rtype_to_index.get(&rtype).expect("Should exist");
        let graph_edge =
            self.graph
                .add_edge(caller_node.graph_node, callee_node.graph_node, rtype_id);
        let edge = CallGraphEdge::new(
            edge_id,
            caller_node.index,
            callee_node.index,
            rtype,
            graph_edge,
        );
        self.edges.insert(graph_edge, edge);
    }

    fn get_node_by_name(&self, name: &str) -> Option<NodeIdx> {
        for nx in self.graph.node_indices() {
            let defid = self.graph.node_weight(nx).expect("Should exist");
            let node = self.nodes.get(defid).expect("Should exist");
            if node.name.contains(name) {
                return Some(nx);
            }
        }
        None
    }

    fn deduplicate_edges(&self) -> CallGraph {
        let mut edges = HashSet::<(NodeIdx, NodeIdx)>::new();
        let graph = self.graph.filter_map(
            |_, node| Some(node.to_owned()),
            |edge_idx, edge| {
                let endpoints = self.graph.edge_endpoints(edge_idx).expect("Should exist");
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

    fn reachable_from(&self, start_node: NodeIdx) -> HashSet<NodeIdx> {
        let mut reachable = HashSet::<NodeIdx>::new();
        let mut bfs = Bfs::new(&self.graph, start_node);
        let mut croot: Option<NodeIdx> = None;
        while let Some(nx) = bfs.next(&self.graph) {
            let defid = self.graph.node_weight(nx).expect("Should exist");
            if self.nodes.get(defid).expect("Should exist").is_croot() {
                if croot.is_none() {
                    croot = Some(nx);
                    reachable.insert(nx);
                }
            } else {
                reachable.insert(nx);
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
                if self.nodes.get(node).expect("Should exist").is_excluded() {
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
                        .insert((start_idx, *edge));
                }
                if excluded.contains_key(&start_idx) {
                    excluded
                        .get_mut(&start_idx)
                        .expect("Exists")
                        .1
                        .insert((end_idx, *edge));
                }
                Some(edge.to_owned())
            },
        );
        // 3. Condense edges and insert
        for (in_idx, out_idx, rtype) in self.condense_edge_set(&excluded).iter() {
            graph.add_edge(*in_idx, *out_idx, *rtype);
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
        self.graph.filter_map(
            |_, node| Some(self.nodes.get(node).expect("Should exist").name.to_owned()),
            |_, _| Some(()),
        )
    }

    fn output_dominance(&self) {
        for (defid1, defid2) in self.dominance.iter() {
            println!("Dom({:?}, {:?})", defid1, defid2);
        }
    }

    fn output_datalog(&self) {
        let mut ctr = 0;
        println!("start;");
        let mut used_rtypes = HashSet::<u32>::new();
        self.graph.map(
            |node_idx1, _| {
                if self.dominance.contains_key(&node_idx1) {
                    for node_idx2 in self.dominance.get(&node_idx1).expect("Exists") {
                        println!("Dom({}, {});", node_idx1.index(), node_idx2.index());
                    }
                }
            },
            |edge_idx, rtype_id| {
                let (start_idx, end_idx) = self.graph.edge_endpoints(edge_idx).expect("Exists");
                println!("Edge({}, {}, {});", ctr, start_idx.index(), end_idx.index());
                println!("EdgeType({}, {});", ctr, rtype_id);
                used_rtypes.insert(*rtype_id);
                ctr += 1;
            }
        );
        println!("commit;");
        println!("dump NotCheckedByTypeAt;");
        println!("{{");
        for rtype_id in used_rtypes.iter() {
            if let Some(rtype_str) = self.index_to_rtype.get(&rtype_id) {
                println!("\t\"{}\": {}", rtype_id, rtype_str);
            }
        }
        println!("}}");
    }

    pub fn to_dot(&self) {
        let call_graph1 = self.filter_reachable("verify_impl");
        let call_graph2 = call_graph1.fold_excluded();
        let call_graph3 = call_graph2.filter_no_edges();
        let call_graph4 = call_graph3.filter_reachable("verify_impl");
        call_graph4.output_datalog();
        println!(
            "{:?}",
            Dot::with_config(
                &call_graph4.deduplicate_edges().shortened_node_names(),
                &[Config::EdgeNoLabel]
            )
        );
    }
}
