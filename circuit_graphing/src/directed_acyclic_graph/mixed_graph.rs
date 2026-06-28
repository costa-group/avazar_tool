use std::collections::{HashMap, HashSet};
use std::borrow::Borrow;
use itertools::Itertools;

use utils::small_utilities::{distance_to_source_set};
use utils::union_find::{UnionFind};
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use super::{DAGNode};
use super::dag_utils::{lt, add_arc_to_nodes};

pub struct MixedGraph {
    pub n: usize, pub m: usize,
    pub partition: Vec<Vec<usize>>,
    pub adjacencies: Vec<Vec<usize>>,
    pub dir_adjacencies: Vec<HashSet<usize>>,
    pub edges: Vec<(usize, usize)>,
    pub input_parts: HashSet<usize>,
    pub output_parts: HashSet<usize>
}

// NOTE: this struct doesn't handle correctness -- correctness is handled by the user
impl MixedGraph {

    pub fn new(partition: Vec<Vec<usize>>, adjacencies:Vec<Vec<usize>>, input_parts: HashSet<usize>, output_parts: HashSet<usize>) -> MixedGraph {
        let edges: Vec<(usize, usize)> = adjacencies.iter().enumerate()
                        .flat_map( |(idx, part)| part.into_iter().copied().map(move |x| (idx, x)))
                        .filter(|(a, b)| a < b)
                        .collect();

        let dir_adjacencies = vec![HashSet::new(); partition.len()];

        Self {n: partition.len(), m: edges.len(), partition, adjacencies, dir_adjacencies, edges, input_parts, output_parts}
    }

    pub fn merge(&self, mut undirected_components: UnionFind) -> MixedGraph {

        let components = undirected_components.get_components();
        let parent_to_newidx: HashMap<usize, usize> = components.iter().enumerate().map(|(idx, part)| (undirected_components.find(part[0]), idx)).collect();

        let mut merged_partition : Vec<Vec<usize>> = vec![Vec::new(); parent_to_newidx.len()];
        let mut merged_adjacencies : Vec<Vec<usize>> = vec![Vec::new(); parent_to_newidx.len()];
        let mut merged_dir_adjacencies : Vec<HashSet<usize>> = vec![HashSet::new(); parent_to_newidx.len()];
        let merged_inputs: HashSet<usize> = self.input_parts.iter().copied().map(|x| parent_to_newidx[&undirected_components.find(x)]).collect();
        let merged_outputs: HashSet<usize> = self.output_parts.iter().copied().map(|x| parent_to_newidx[&undirected_components.find(x)]).collect();

        for part in components.into_iter() {
            let newidx = parent_to_newidx[&undirected_components.find(part[0])];
            let part = part.into_iter().collect::<HashSet<_>>();

            merged_partition[newidx] = part.iter().copied().flat_map(|v| self.partition[v].iter().copied()).collect();
            merged_adjacencies[newidx] = part.iter().copied().flat_map(|v| self.adjacencies[v].iter().copied()).map(|x| parent_to_newidx[&undirected_components.find(x)]).collect::<HashSet<_>>().into_iter().filter(|x| *x != newidx).collect();
            merged_dir_adjacencies[newidx] = part.iter().copied().flat_map(|v| self.dir_adjacencies[v].iter().copied()).map(|x| parent_to_newidx[&undirected_components.find(x)]).filter(|x| *x  != newidx).collect();
        }

        let edges: Vec<(usize, usize)> = merged_adjacencies.iter().enumerate()
                        .flat_map( |(idx, part)| part.into_iter().copied().map(move |x| (idx, x)))
                        .filter(|(a, b)| a < b)
                        .collect();

        Self { n: merged_partition.len(), m: edges.len(), partition: merged_partition, adjacencies: merged_adjacencies, dir_adjacencies: merged_dir_adjacencies, edges, input_parts: merged_inputs, output_parts: merged_outputs }
    }

    pub fn pair_oriented(&self, u: usize, v: usize) -> bool { self.dir_adjacencies[u].contains(&v) || self.dir_adjacencies[v].contains(&u) }
    pub fn edge_oriented(&self, e: usize) -> bool { self.dir_adjacencies[self.edges[e].0].contains(&self.edges[e].1) || self.dir_adjacencies[self.edges[e].1].contains(&self.edges[e].0) }

    pub fn orient_by_partial_order(&mut self) -> Vec<(usize, usize)> {

        let distance_to_inputs = distance_to_source_set(self.input_parts.iter().copied(), &self.adjacencies);
        let distance_to_outputs = distance_to_source_set(self.output_parts.iter().copied(), &self.adjacencies);

        let part_to_preorder: Vec<(usize, usize)> = (0..self.n).map(|key| (distance_to_inputs[key], distance_to_outputs[key])).collect();

        for e in 0..self.m {
            if self.edge_oriented(e) {continue;}
            let (u, v) = self.edges[e];
            if lt(part_to_preorder[u], part_to_preorder[v]) {self.dir_adjacencies[u].insert(v);}
            else if lt(part_to_preorder[v], part_to_preorder[u]) {self.dir_adjacencies[v].insert(u);}
        }

        part_to_preorder
    }

    pub fn orient_leaf_parts(&mut self) -> () {

        // leafs that are not two adjacent leafs are directed towards the leaf
        for v in (0..self.n).filter(|&v| self.adjacencies[v].len() == 1 && self.adjacencies[self.adjacencies[v][0]].len() != 1) {
            let u = self.adjacencies[v][0];
            if self.pair_oriented(u, v) {continue;}
            self.dir_adjacencies[u].insert(v);
        }
    }

    pub fn initialise_dagnodes<'a, C: Constraint + 'a, S: Circuit<C> + 'a>(
        &self, circ: &'a S, node_id_generator: &mut dyn Iterator<Item = usize>,
    ) -> (HashMap<usize, DAGNode<'a, C, S>>, Vec<Vec<usize>>, Vec<usize>) {

        let part_to_signals_arr: Vec<Vec<usize>> = self.partition.iter().map(|part|
            part.into_iter().copied().flat_map(|idx| circ.get_constraints()[idx].borrow().signals()).sorted_unstable().dedup().collect()
        ).collect();
        let idx_to_nodeid: Vec<usize> = node_id_generator.take(self.n).collect();
        let mut nodes : HashMap<usize, DAGNode<'a, C, S>> = self.partition.clone().into_iter().enumerate().map(|(idx, part)| {
            (idx_to_nodeid[idx], 
            DAGNode::new(
                circ, 
                idx_to_nodeid[idx], 
                part, 
                part_to_signals_arr[idx].iter().copied().filter(|sig| circ.signal_is_input(sig)).collect(), // get global labelled signal in initially
                part_to_signals_arr[idx].iter().copied().filter(|sig| circ.signal_is_output(sig)).collect(),
                None, None))
        }).collect();
      
        for (v, outgoing) in self.dir_adjacencies.iter().enumerate() {for u in outgoing.into_iter().copied() {
            add_arc_to_nodes((u, v), &idx_to_nodeid, &part_to_signals_arr, &mut nodes);
        }}

        (nodes, part_to_signals_arr, idx_to_nodeid)
    }

    pub fn merge_equivalence_classes_by_distance_and_orient(&mut self) -> ()
    {
        
        let mut part_to_preorder: Vec<(usize, usize)>;
        // TODO: check if this will only ever take 1 iteration

        // merge equivalence classes into layers
        let exists_nontrivial_equivalence_classes = true;
        while exists_nontrivial_equivalence_classes {

            println!("---------------------------------------");
            // TODO: convince self that this wont create cycle
            part_to_preorder = self.orient_by_partial_order();

            let num_fuzzy_edges: usize = (0..self.m).filter(|&e| !self.edge_oriented(e)).count();
            println!("num_fuzzy: {:?}", num_fuzzy_edges);

            // Merge equivalence class
            let mut equal_distance = UnionFind::new(false);
            for v in 0..self.n {equal_distance.find(v);}
            
            for (e, &(a, b)) in self.edges.iter().enumerate() {
                if part_to_preorder[a] == part_to_preorder[b] && !self.edge_oriented(e) {equal_distance.union([a, b].into_iter());}
            }

            use utils::small_utilities::count_ints;
            if equal_distance.get_components().len() == self.partition.len() {
                break;
            }

            println!("merging: {:?}", count_ints(equal_distance.get_components().into_iter().map(|part| part.len())));
            *self = self.merge(equal_distance);
        }
}

}