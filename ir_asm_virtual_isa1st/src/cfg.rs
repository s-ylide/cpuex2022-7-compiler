use std::{collections::HashMap, hash::Hash};

use ir_asm_virtual_ast_isa1st::FunDef;

pub struct Graph<'a, Node> {
    edges: HashMap<&'a Node, Vec<&'a Node>>,
    root: &'a Node,
}

pub struct Cfg<'fun, L, IR, FR> {
    f: &'fun FunDef<L, IR, FR>,
    graph: Graph<'fun, L>,
}

impl<'fun, L: std::ops::Deref, IR, FR> std::ops::Deref for Cfg<'fun, L, IR, FR> {
    type Target = Graph<'fun, L>;

    fn deref(&self) -> &Self::Target {
        &self.graph
    }
}

impl<'fun, L: Eq + Hash, IR, FR> Cfg<'fun, L, IR, FR> {
    pub fn from_fundef(f: &'fun FunDef<L, IR, FR>) -> Self {
        let mut edges = HashMap::new();
        for bb in &f.body {
            let u = &bb.id;
            let vs: Vec<_> = bb.terminator.dests().collect();
            if !vs.is_empty() {
                edges.insert(u, vs);
            }
        }
        let root = &f.body.front().unwrap().id;
        let graph = Graph { edges, root };
        Self { f, graph }
    }
    fn in_degree_map(&self) -> HashMap<&L, usize> {
        let mut in_degree_map = HashMap::new();
        for bb in &self.f.body {
            for dst in bb.terminator.dests() {
                in_degree_map
                    .entry(dst)
                    .and_modify(|c| *c += 1)
                    .or_insert(1);
            }
        }
        in_degree_map
    }
    fn out_degree_map(&self) -> HashMap<&L, usize> {
        self.f
            .body
            .iter()
            .map(|bb| (&bb.id, bb.terminator.out_degree()))
            .collect()
    }
    pub fn critical_edges(&self) -> impl Iterator<Item = (&L, &L)> {
        let in_degree_map = self.in_degree_map();
        let out_degree_map = self.out_degree_map();
        let mut critical_edges = Vec::new();
        for (&u, vs) in self.graph.edges.iter() {
            if out_degree_map[u] > 1 {
                for &v in vs {
                    if in_degree_map[v] > 1 {
                        critical_edges.push((u, v));
                    }
                }
            }
        }
        critical_edges.into_iter()
    }
}

impl<'a, Node: Eq + Hash> Graph<'a, Node> {
    #[inline]
    pub fn childs(&'a self, node: &Node) -> impl Iterator<Item = &'a Node> {
        self.edges.get(node).into_iter().flatten().copied()
    }
    pub fn find_back_edge_dsts(&'a self) -> impl Iterator<Item = &'a Node> {
        enum StackOp {
            Push,
            RemovePath,
        }
        use StackOp::*;
        #[derive(PartialEq)]
        enum VisitedNode {
            Visited,
            Removed,
        }
        use VisitedNode::*;
        let mut stack = vec![(Push, self.root)];
        let mut visited = HashMap::new();
        let mut back_edge_dsts = Vec::new();
        while let Some((op, node)) = stack.pop() {
            match op {
                RemovePath => {
                    if let Some(v) = visited.get_mut(node) {
                        *v = Removed;
                    }
                }
                Push => {
                    visited.insert(node, Visited);
                    stack.push((RemovePath, node));
                    for next in self.childs(node) {
                        match visited.get(next) {
                            Some(Visited) => {
                                back_edge_dsts.push(next);
                            }
                            Some(Removed) => {}
                            None => {
                                stack.push((Push, next));
                            }
                        }
                    }
                }
            }
        }
        back_edge_dsts.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_back_edge() {
        let node0 = 0;
        let node1 = 1;
        let node2 = 2;
        let node3 = 3;
        let cfg = Graph {
            edges: HashMap::from_iter([
                (&node0, vec![&node1, &node2]),
                (&node1, vec![&node3]),
                (&node2, vec![&node3]),
                (&node3, vec![&node0]),
            ]),
            root: &node0,
        };
        let ds: Vec<_> = cfg.find_back_edge_dsts().collect();

        assert_eq!(ds[0], &node0);
    }
}
