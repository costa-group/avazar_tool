use std::collections::{HashMap, HashSet};
use std::time::{Instant};

use circuits_constraints_and_algebra::circuit::Circuit;
use circuits_constraints_and_algebra::constraint::Constraint;
use circuits_constraints_and_algebra::utils::signals_to_constraints_with_them;
use utils::union_find::UnionFind;
use utils::small_utilities::HierarchyMode;

use crate::directed_acyclic_graph::{DAGNode};
use crate::directed_acyclic_graph::dag_from_partition::dag_from_partition;
use crate::directed_acyclic_graph::dag_postprocessing::merge_passthrough;

/// Looks for 'bridge' constraints within the circuit and creates an initial hierarchy based on this. A bridge constraint is one of the form `x = y` and is typically used when renaming signals for a different context. 
///
/// # Panics
/// If the graph is not connected the merge_passthrough call may panic
pub fn bridge_partitioning<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(circ: &'a S, strict_bridge: bool, hierarchy_mode: HierarchyMode, debug: usize) -> HashMap<usize, DAGNode<'a, C, S>> {

    // partition the constraints into clusters based on connectedness through non-bridge nodes
    if debug > 1 {println!("LOG: Beginning bridge partitioning");}
    let signal_to_coni_timer = Instant::now();

    let mut nonbridge_connectedness = UnionFind::new(false);

    let prime = circ.prime();
    let signal_to_coni = signals_to_constraints_with_them::<C>(&circ.constraints(), None, None);
    
    if debug > 1 {println!("LOG: Finished signal to coni in {:?}", signal_to_coni_timer.elapsed());}
    let nonbridge_connectedness_timer = Instant::now();

    for adjacent in signal_to_coni.values() {
        nonbridge_connectedness.union(adjacent.iter().copied().filter(|coni| !circ.get_constraint(*coni).is_bridge_constraint(prime, strict_bridge)));
    }

    if debug > 1 {println!("LOG: Finished nonbridge unionfind in {:?}", nonbridge_connectedness_timer.elapsed());}
    let signal_to_nodes_timer = Instant::now();

    // get a constraint_to_node && node_to_constraint maps
    let mut node_to_coni: Vec<Vec<usize>> = nonbridge_connectedness.get_components();
    let mut signal_to_node: HashMap<usize, usize> = HashMap::new();

    for (parti, part) in node_to_coni.iter().enumerate() {for signal in part.iter().copied().flat_map(|coni| circ.get_constraint(coni).signals().into_iter()).collect::<HashSet<usize>>().into_iter() {
        signal_to_node.insert(signal, parti); // by connectedness this can never overlap
    }}

    if debug > 1 {println!("LOG: Finished signal_to_nodes in {:?}", signal_to_nodes_timer.elapsed());}
    let bridge_connectnedness_timer = Instant::now();

    // for bridge nodes if they are between two, keep separate -- otherwise add to part

    let mut bridge_connectedness = UnionFind::new(false);
    for con in circ.constraints().into_iter().filter(|&con| con.is_bridge_constraint(prime, strict_bridge)) { 
        bridge_connectedness.union(
            con.signals().into_iter().flat_map(|signal| signal_to_coni[&signal].iter().copied()).collect::<HashSet<usize>>().into_iter().filter(|coni| circ.get_constraint(*coni).is_bridge_constraint(prime, strict_bridge))
        );
    }

    for component in bridge_connectedness.get_components().into_iter() {
        let adjacent_nodes: HashSet<usize> = component.iter().copied().flat_map(|coni| circ.get_constraint(coni).signals().into_iter().flat_map(|signal| signal_to_node.get(&signal).copied().into_iter())).collect();
        if adjacent_nodes.len() == 1 {node_to_coni[adjacent_nodes.into_iter().next().unwrap()].extend(component.into_iter());}
        else {node_to_coni.push(component);}
    }

    if debug > 1 {println!("LOG: Finished bridge_handling in {:?}", bridge_connectnedness_timer.elapsed());}
    let dag_from_partition_timer = Instant::now();

    // pass partition to hierarchy and return DAGNodes
    let mut dagnodes = dag_from_partition(circ, node_to_coni, &mut (0..), false, hierarchy_mode, debug);
    if debug > 1 {println!(
        "LOG: Number of passthrough clusters {:?} out of {:?}", dagnodes.values().filter(|&node| node.get_input_signals().intersection(node.get_output_signals()).count() > 0).count(), dagnodes.len()
    );}

    merge_passthrough(circ, &mut dagnodes);
    if debug > 0 {println!("LOG: Finished bridge partitioning in {:?}", dag_from_partition_timer.elapsed());}
    

    dagnodes
}