use petgraph::dot::{Config, Dot};
use petgraph::graph::{DefaultIx, NodeIndex};
use petgraph::Graph;
use rustc_hir::def_id::DefId;
use std::collections::HashMap;

// The type of a call graph node
pub enum NodeType {
    // Regular root
    Root,
    // Crate root: Starting point for analysis (pub fn)
    CRoot,
    // Closure
    Closure,
}

pub struct CallGraphNode {
    // A Node has a DefId and type.
    // Nodes are uniquely identified by their DefId.
    index: u32,
    defid: DefId,
    ntype: NodeType,
    graph_node: NodeIndex<DefaultIx>,
}

impl CallGraphNode {
    pub fn new_croot(index: u32, defid: DefId, graph_node: NodeIndex<DefaultIx>) -> CallGraphNode {
        CallGraphNode {
            index,
            defid,
            ntype: NodeType::CRoot,
            graph_node,
        }
    }

    pub fn new_root(index: u32, defid: DefId, graph_node: NodeIndex<DefaultIx>) -> CallGraphNode {
        CallGraphNode {
            index,
            defid,
            ntype: NodeType::Root,
            graph_node,
        }
    }
}

pub struct CallGraphEdge {
    // An Edge connects two nodes.
    // Edges are uniquely identified by their index, and have an associated Rust type.
    index: u32,
    rtype: String,
}

impl CallGraphEdge {
    pub fn new(index: u32, rtype: String) -> CallGraphEdge {
        CallGraphEdge { index, rtype }
    }
}

pub struct CallGraph {
    // The graph structure capturing calls between nodes
    graph: Graph<u32, u32>,
    // A map from DefId to node information
    nodes: HashMap<DefId, CallGraphNode>,
    // A map of edge indexes to edge information
    edges: HashMap<u32, CallGraphEdge>,
}

impl Default for CallGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl CallGraph {
    pub fn new() -> CallGraph {
        CallGraph {
            graph: Graph::<u32, u32>::new(),
            nodes: HashMap::<DefId, CallGraphNode>::new(),
            edges: HashMap::<u32, CallGraphEdge>::new(),
        }
    }

    pub fn add_croot(&mut self, defid: DefId) {
        let node_id = self.nodes.len() as u32;
        let graph_node = self.graph.add_node(node_id);
        let croot = CallGraphNode::new_croot(node_id, defid, graph_node);
        self.nodes.insert(defid, croot);
    }

    pub fn add_root(&mut self, defid: DefId) {
        if !self.nodes.contains_key(&defid) {
            let node_id = self.nodes.len() as u32;
            let graph_node = self.graph.add_node(node_id);
            let root = CallGraphNode::new_root(node_id, defid, graph_node);
            self.nodes.insert(defid, root);
        }
    }

    pub fn add_edge(&mut self, caller_id: DefId, callee_id: DefId, rtype: String) {
        let edge_id = self.edges.len() as u32;
        let edge = CallGraphEdge::new(edge_id, rtype);
        self.edges.insert(edge_id, edge);
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
            .get(&caller_id)
            .expect("The node must exist at this point.");
        self.graph
            .add_edge(caller_node.graph_node, callee_node.graph_node, edge_id);
    }

    pub fn to_dot(&self) {
        println!(
            "{:?}",
            Dot::with_config(&self.graph, &[Config::EdgeNoLabel])
        );
    }
}
