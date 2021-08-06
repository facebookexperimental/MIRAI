use petgraph::dot::{Config, Dot};
use petgraph::graph::{DefaultIx, EdgeIndex, NodeIndex};
use petgraph::visit::Bfs;
use petgraph::Graph;
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
        }
    }

    fn update(&self, graph: Graph<DefId, u32>) -> CallGraph {
        CallGraph {
            graph,
            nodes: self.nodes.clone(),
            edges: self.edges.clone(),
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
        let graph_edge =
            self.graph
                .add_edge(caller_node.graph_node, callee_node.graph_node, edge_id);
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

    fn reachable_from(&self, name: &str) -> CallGraph {
        let mut reachable = HashSet::<NodeIndex<DefaultIx>>::new();
        let start_node = self
            .get_node_by_name(name)
            .expect("Valid start node required");
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

    fn filter_excluded(&self) -> CallGraph {
        let graph = self.graph.filter_map(
            |_, node| {
                if !self.nodes.get(node).expect("Should exist").is_excluded() {
                    Some(node.to_owned())
                } else {
                    None
                }
            },
            |_, edge| Some(edge.to_owned()),
        );
        self.update(graph)
    }

    pub fn to_dot(&self) {
        let call_graph = self.reachable_from("verify_impl");
        let call_graph2 = call_graph.filter_excluded();
        println!(
            "{:?}",
            Dot::with_config(
                &call_graph2.deduplicate_edges().graph,
                &[Config::EdgeNoLabel]
            )
        );
    }
}
