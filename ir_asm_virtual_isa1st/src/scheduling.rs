use std::{
    cmp::Reverse,
    collections::{BTreeMap, BinaryHeap, HashMap},
};

use ir_asm_ast_isa1st::abi::RegId;
use ir_asm_virtual_ast_isa1st::{Expr, Stmt, VAsmFunDef};
use itertools::Itertools;
use typedefs::IdentSymbol;

use crate::Collectable;

pub fn scheduling(fundef: &mut VAsmFunDef) {
    #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
    struct ProgramPoint(usize);

    #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
    struct MachineCycle(Reverse<isize>);

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    struct Node {
        priority: Option<isize>,
        id: ProgramPoint,
    }

    impl Node {
        fn new(id: ProgramPoint) -> Self {
            Self { priority: None, id }
        }
    }
    type DependencyGraph = HashMap<ProgramPoint, Node>;

    #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
    struct Edge {
        parent: ProgramPoint,
        latency: usize,
    }

    impl Edge {
        fn new(parent: ProgramPoint, latency: usize) -> Self {
            Self { parent, latency }
        }
    }

    for bb in &mut fundef.body {
        let len = bb.instrs.len();
        if len <= 1 {
            return;
        }
        let mut reg_map: HashMap<RegId, ProgramPoint> = HashMap::new();
        let mut def_map: HashMap<IdentSymbol, Edge> = HashMap::new();

        let mut last_stores: Vec<ProgramPoint> = Vec::with_capacity(len);
        let mut last_loads: Vec<ProgramPoint> = Vec::with_capacity(len);
        #[derive(PartialEq)]
        enum MemAccess {
            L,
            S,
        }
        use MemAccess::*;
        let mut current_mem = None;

        let mut counter = 0;
        let mut graph_nodes = DependencyGraph::new();
        let mut graph_edges: HashMap<ProgramPoint, Vec<Edge>> = HashMap::new();
        for stmt in &bb.instrs {
            let mut edges = Vec::new();
            let mut usage = Default::default();
            stmt.collect_usage(&mut usage);
            edges.extend(usage.usage_of_var().keys().filter_map(|id| def_map.get(id)));
            match stmt {
                Stmt::IncrABI(r, _) => {
                    if let Some(old) = reg_map.insert(*r, ProgramPoint(counter)) {
                        edges.push(Edge::new(old, 1));
                    }
                }
                Stmt::Assign(d, _, e) => {
                    if let Expr::Mov(p) = e {
                        if let Some(p) = p.as_p() {
                            if let Some(old) = reg_map.insert(*p, ProgramPoint(counter)) {
                                edges.push(Edge::new(old, 1));
                            }
                        }
                    }
                    let latency = match e {
                        Expr::LoadF32(_)
                        | Expr::LoadLabelAddr(_)
                        | Expr::Load(_, _)
                        | Expr::LoadFromLabelDisp(_, _, _) => {
                            for store in &last_stores {
                                edges.push(Edge::new(*store, 1));
                            }
                            if current_mem == Some(S) && !last_loads.is_empty() {
                                last_loads.clear();
                            }
                            current_mem = Some(L);
                            last_loads.push(ProgramPoint(counter));
                            2
                        }
                        _ => 1,
                    };
                    if let Some(d) = d {
                        def_map.insert(*d.id(), Edge::new(ProgramPoint(counter), latency));
                    }
                }
                Stmt::Store(_, _, _)
                | Stmt::StoreF(_, _, _)
                | Stmt::StoreLabelDisp(_, _, _, _)
                | Stmt::StoreFLabelDisp(_, _, _, _) => {
                    for load in &last_loads {
                        edges.push(Edge::new(*load, 1));
                    }
                    if current_mem == Some(L) && !last_stores.is_empty() {
                        last_stores.clear();
                    }
                    current_mem = Some(S);
                    last_stores.push(ProgramPoint(counter));
                }
            }
            graph_nodes.insert(ProgramPoint(counter), Node::new(ProgramPoint(counter)));
            graph_edges.insert(ProgramPoint(counter), edges);
            counter += 1;
        }

        let mut usage = Default::default();
        bb.terminator.collect_usage(&mut usage);
        let edges = usage
            .usage_of_var()
            .keys()
            .filter_map(|id| def_map.get(id).cloned())
            .collect();
        graph_nodes.insert(ProgramPoint(counter), Node::new(ProgramPoint(counter)));
        graph_edges.insert(ProgramPoint(counter), edges);

        // calc indegree
        let mut indegree = HashMap::new();

        for (key, edges) in graph_edges.iter() {
            for edge in edges {
                *indegree.entry(edge.parent).or_insert(0) += 1;
                let _ = indegree.try_insert(*key, 0);
            }
        }

        // give prio
        let unpointed = indegree
            .iter()
            .filter_map(|(n, indegree)| if *indegree == 0 { Some(*n) } else { None })
            .collect_vec();
        give_priority(
            unpointed.iter().map(|u| (0, *u)).collect_vec(),
            &mut graph_nodes,
            &graph_edges,
        );

        fn give_priority(
            mut stack: Vec<(isize, ProgramPoint)>,
            graph_nodes: &mut HashMap<ProgramPoint, Node>,
            graph_edges: &HashMap<ProgramPoint, Vec<Edge>>,
        ) {
            while let Some((prio, id)) = stack.pop() {
                let node = graph_nodes.get_mut(&id).unwrap();
                if Some(prio) > node.priority {
                    node.priority = Some(prio);
                    for edge in graph_edges.get(&id).unwrap() {
                        let prio = prio + edge.latency as isize;
                        stack.push((prio, edge.parent));
                    }
                }
            }
        }

        // scheduling
        let mut reservation: HashMap<MachineCycle, ProgramPoint> = HashMap::new();
        let mut pq: BinaryHeap<Node> = unpointed
            .into_iter()
            .map(|id| Node {
                priority: Some(0),
                id,
            })
            .collect();

        // get max element
        while let Some(n) = pq.pop() {
            let mut cycle = n.priority.unwrap();
            let mut update_prio = false;
            loop {
                let res = reservation.try_insert(MachineCycle(Reverse(cycle)), n.id);
                if res.is_err() {
                    cycle += 1;
                    update_prio = true;
                    continue;
                } else {
                    break;
                }
            }
            if update_prio {
                give_priority(vec![(cycle, n.id)], &mut graph_nodes, &graph_edges);
            }
            // remove node from graph
            if let Some(edges) = graph_edges.remove(&n.id) {
                for edge in edges {
                    let parent = edge.parent;
                    let indegree = indegree.get_mut(&parent).unwrap();
                    *indegree -= 1;
                    if *indegree == 0 {
                        pq.push(graph_nodes.get(&parent).unwrap().clone());
                    }
                }
            }
        }

        // end schedule
        let scheduling_result: HashMap<ProgramPoint, MachineCycle> =
            reservation.into_iter().map(|(k, v)| (v, k)).collect();
        let bt = std::mem::take(&mut bb.instrs)
            .into_iter()
            .enumerate()
            .map(|(index, stmt)| (*scheduling_result.get(&ProgramPoint(index)).unwrap(), stmt))
            .collect::<BTreeMap<MachineCycle, _>>();
        bb.instrs = bt.into_values().collect();
    }
}
