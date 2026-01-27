use std::collections::{HashMap, HashSet};
use std::borrow::Borrow;

use circuits_and_constraints::circuit::Circuit;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::utils::signals_to_constraints_with_them;
use utils::union_find::UnionFind;

use crate::directed_acyclic_graph::{DAGNode};
use crate::directed_acyclic_graph::dag_from_partition::dag_from_partition;

pub fn bridge_partitioning<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(circ: &'a S, strict_bridge: bool) -> HashMap<usize, DAGNode<'a, C, S>> {

    // partition the constraints into clusters based on connectedness through non-bridge nodes
    let mut nonbridge_connectedness = UnionFind::new(false);

    let prime = circ.prime();
    let constraints = circ.get_constraints();
    let signal_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);

    for (coni, con) in constraints.into_iter().enumerate().filter(|&(_, con)| !con.borrow().is_bridge_constraint(prime, strict_bridge)) { 
        nonbridge_connectedness.union([coni].into_iter().chain(
            con.borrow().signals().into_iter().flat_map(|signal| signal_to_coni[&signal].iter().copied()).collect::<HashSet<usize>>().into_iter().filter(|coni| !constraints[*coni].borrow().is_bridge_constraint(prime, strict_bridge))
        ));
    }

    // get a constraint_to_node && node_to_constraint maps
    let mut node_to_coni: Vec<Vec<usize>> = nonbridge_connectedness.get_components();
    let mut signal_to_node: HashMap<usize, usize> = HashMap::new();

    for (parti, part) in node_to_coni.iter().enumerate() {for signal in part.iter().copied().flat_map(|coni| constraints[coni].borrow().signals().into_iter()).collect::<HashSet<usize>>().into_iter() {
        signal_to_node.insert(signal, parti); // by connectedness this can never overlap
    }}

    // for bridge nodes if they are between two, keep separate -- otherwise add to part

    let mut bridge_connectedness = UnionFind::new(false);
    for (coni, con) in constraints.into_iter().enumerate().filter(|&(_, con)| con.borrow().is_bridge_constraint(prime, strict_bridge)) { 
        bridge_connectedness.union([coni].into_iter().chain(
            con.borrow().signals().into_iter().flat_map(|signal| signal_to_coni[&signal].iter().copied()).collect::<HashSet<usize>>().into_iter().filter(|coni| constraints[*coni].borrow().is_bridge_constraint(prime, strict_bridge))
        ));
    }

    for component in bridge_connectedness.get_components().into_iter() {
        let adjacent_nodes: HashSet<usize> = component.iter().copied().flat_map(|coni| constraints[coni].borrow().signals().into_iter().flat_map(|signal| signal_to_node.get(&signal).copied().into_iter())).collect();
        if adjacent_nodes.len() == 1 {node_to_coni[adjacent_nodes.into_iter().next().unwrap()].extend(component.into_iter());}
        else {node_to_coni.push(component);}
    }

        
    // pass partition to hierarchy and return DAGNodes
    dag_from_partition(circ, node_to_coni, &mut (0..))
}