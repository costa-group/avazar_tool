use std::collections::{HashMap, HashSet};

use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::utils::signals_to_constraints_with_them;
use utils::union_find::UnionFind;

use crate::directed_acyclic_graph::dag_construction::dag_from_partition;

pub fn bridge_partitioning<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(circ: &'a S, strict_bridge: bool) -> HashMap<usize, DAGNode<'a, C, S>> {

    // partition the constraints into clusters based on connectedness through non-bridge nodes
    let mut connectedness = UnionFind::new(false);
    let prime = circ.prime();
    let constraints = circ.get_constraints();
    let signal_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);

    for (coni, con) in constraints.enumerate() { 
        connectedness.union([coni].into_iter().chain(
            con.signals().into_iter().flat_map(|signal| signal_to_coni[&signal].iter().copied()).collect::<HashSet<usize>>().into_iter().filter(|coni| !constraints[coni].is_bridge_constraint(prime, strict_bridge))
        ));
    }
    
    // get a constraint_to_node && node_to_constraint maps
    let mut node_to_coni: Vec<Vec<usize>> = connectedness.get_partition();
    let mut signal_to_node: HashMap<usize, usize> = HashMap::new();

    for (parti, part) in node_to_coni.iter().enumerate() {for signal in part.flat_map(|coni| constraints[coni].signals().into_iter()).collect::<HashSet<usize>>().into_iter() {
        signal_to_node.insert(signal, parti) // by connectedness this can never overlap
    }}

    // for bridge nodes if they are between two, keep separate -- otherwise add to part
    for (coni, con) in constraints.enumerate().filter(|&(coni, con)| constraints[coni].is_bridge_constraint(prime, strict_bridge)) {
        let adjacent_nodes: Vec<usize> = con.signals().map(|signal| signal_to_node[signal]).collect(); // len 2 because is_bridge_constraint
        if adjacent_nodes[0] == adjacent_nodes[1] {node_to_coni[adjacent_nodes[0]].push(coni);}
        else {node_to_coni.push(vec![coni]);}
    }

    // pass partition to hierarchy and return DAGNodes
    dag_from_partition(circ, node_to_coni);
}