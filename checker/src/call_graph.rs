use petgraph::dot::{Config, Dot};
use petgraph::graph::{DefaultIx, EdgeIndex, NodeIndex};
use petgraph::visit::Bfs;
use petgraph::{Graph, Direction};
use rustc_hir::def_id::DefId;
use std::collections::{HashMap, HashSet};

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
    graph_node: NodeIndex<DefaultIx>,
}

impl CallGraphNode {
    pub fn new_croot(index: u32, defid: DefId, graph_node: NodeIndex<DefaultIx>) -> CallGraphNode {
        CallGraphNode {
            index,
            defid,
            name: CallGraphNode::format_name(defid),
            ntype: NodeType::CRoot,
            graph_node,
        }
    }

    pub fn new_root(index: u32, defid: DefId, graph_node: NodeIndex<DefaultIx>) -> CallGraphNode {
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
    graph_edge: EdgeIndex<DefaultIx>,
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
        graph_edge: EdgeIndex<DefaultIx>,
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
    edges: HashMap<EdgeIndex<DefaultIx>, CallGraphEdge>,
    // Bi-directional mapping of type number to type string
    rtype_to_index: HashMap<String, u32>,
    index_to_rtype: HashMap<u32, String>,
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
            edges: HashMap::<EdgeIndex<DefaultIx>, CallGraphEdge>::new(),
            rtype_to_index: HashMap::<String, u32>::new(),
            index_to_rtype: HashMap::<u32, String>::new(),
        }
    }

    fn update(&self, graph: Graph<DefId, u32>) -> CallGraph {
        CallGraph {
            graph,
            nodes: self.nodes.clone(),
            edges: self.edges.clone(),
            rtype_to_index: self.rtype_to_index.clone(),
            index_to_rtype: self.index_to_rtype.clone(),
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

    fn get_node_by_name(&self, name: &str) -> Option<NodeIndex<DefaultIx>> {
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
        let mut edges = HashSet::<(u32, u32)>::new();
        let graph = self.graph.filter_map(
            |_, node| Some(node.to_owned()),
            |edge_idx, edge| {
                let edge_data = self.edges.get(&edge_idx).expect("Should exist");
                let to_from = (edge_data.caller_id, edge_data.callee_id);
                if edges.contains(&to_from) {
                    None
                } else {
                    edges.insert(to_from);
                    Some(edge.to_owned())
                }
            },
        );
        self.update(graph)
    }

    fn reachable_from(&self, start_node: NodeIndex<DefaultIx>) -> HashSet::<NodeIndex<DefaultIx>> {
        let mut reachable = HashSet::<NodeIndex<DefaultIx>>::new();
        let mut bfs = Bfs::new(&self.graph, start_node);
        let mut croot: Option<NodeIndex<DefaultIx>> = None;
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

    fn condense_edge_set(&self, excluded: &HashMap<NodeIndex<DefaultIx>, (Vec<(NodeIndex<DefaultIx>, u32)>, Vec<(NodeIndex<DefaultIx>, u32)>)>) -> HashSet<(NodeIndex<DefaultIx>, NodeIndex<DefaultIx>, u32)> {
        let mut condensed_edges = HashSet::<(NodeIndex<DefaultIx>, NodeIndex<DefaultIx>, u32)>::new();
        for (_, (in_nodes, out_nodes)) in excluded.iter() {
            for (in_node_idx, in_rtype) in in_nodes.iter() {
                if !excluded.contains_key(&in_node_idx) {
                    for (out_node_idx, _) in out_nodes.iter() {
                        if !excluded.contains_key(&out_node_idx) {
                            condensed_edges.insert((*in_node_idx, *out_node_idx, *in_rtype));
                        }
                    }
                }
            }
        }
        condensed_edges
    }

    fn fold_excluded(&self) -> CallGraph {
        // 1. Find all excluded nodes and edges
        let mut excluded = HashMap::<NodeIndex<DefaultIx>, (Vec<(NodeIndex<DefaultIx>, u32)>, Vec<(NodeIndex<DefaultIx>, u32)>)>::new();
        let mut graph = self.graph.filter_map(
            |node_idx, node| {  
                if self.nodes.get(&node).expect("Should exist").is_excluded() {
                    excluded.insert(node_idx, (Vec::<(NodeIndex<DefaultIx>, u32)>::new(), Vec::<(NodeIndex<DefaultIx>, u32)>::new()));
                }
                Some(node.to_owned())
            },
            |_, edge| {
                Some(edge.to_owned())
            }
        );
        graph.filter_map(
            |_, node| {  
                Some(node.to_owned())
            },
            |edge_idx, edge| {
                let (start_idx, end_idx) = self.graph.edge_endpoints(edge_idx).expect("Should exist");
                if excluded.contains_key(&end_idx) {
                    excluded.get_mut(&end_idx).expect("Exists").0.push((start_idx, *edge));
                }
                if excluded.contains_key(&start_idx) {
                    excluded.get_mut(&start_idx).expect("Exists").1.push((end_idx, *edge));
                }
                Some(edge.to_owned())
            }
        );
        // 2. Condense edges and insert
        for (in_idx, out_idx, rtype) in self.condense_edge_set(&excluded).iter() {
            graph.add_edge(*in_idx, *out_idx, *rtype);
        }
        // 3. Remove excluded nodes and edges
        graph = graph.filter_map(
            |node_idx, node| {  
                if excluded.contains_key(&node_idx) {
                    None 
                } else {
                    Some(node.to_owned())
                }
            },
            |_, edge| Some(edge.to_owned())
        );
        self.update(graph)
    }

    fn filter_excluded(&self) -> CallGraph {
        let graph = self.graph.filter_map(
            |_, node| {  
                if !self.nodes.get(&node).expect("Should exist").is_excluded() {
                    Some(node.to_owned())
                } else {
                    None
                }
            },
            |_, edge| Some(edge.to_owned()),
        );
        self.update(graph)
    }

    fn filter_no_edges(&self) -> CallGraph {
        let graph = self.graph.filter_map(
            |node_idx, node| {
                let has_in_edges = self.graph.edges_directed(node_idx, Direction::Incoming).next().is_some();
                let has_out_edges = self.graph.edges_directed(node_idx, Direction::Outgoing).next().is_some();
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

    pub fn to_dot(&self) {
        let call_graph = self.deduplicate_edges();
        let call_graph2 = call_graph.filter_reachable("verify_impl");
        let call_graph3 = call_graph2.fold_excluded();
        let call_graph4 = call_graph3.filter_no_edges();
        println!(
            "{:?}",
            Dot::with_config(
                &call_graph4.shortened_node_names(),
                &[Config::EdgeNoLabel]
            )
        );
    }
}
