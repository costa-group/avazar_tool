use std::collections::{HashMap, HashSet, VecDeque};
use std::borrow::Borrow;
use itertools::Itertools;

use utils::small_utilities::{distance_to_source_set};
use utils::union_find::{UnionFind};
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;
use super::{DAGNode};
use super::dag_utils::{lt, add_arc_to_nodes};
use super::export_to_dzn::write_dzn;
use circuits_and_constraints::utils::signals_to_constraints_with_them;

pub struct MixedGraph {
    pub n: usize, pub m: usize,
    pub partition: Vec<Vec<usize>>,
    pub adjacencies: Vec<Vec<usize>>,
    pub dir_adjacencies: Vec<HashSet<usize>>,
    pub edges: Vec<(usize, usize)>,
    pub input_parts: HashSet<usize>,
    pub output_parts: HashSet<usize>,
    dir_adjacencies_is_outgoing: bool
}

// NOTE: this struct doesn't handle correctness -- correctness is handled by the user
impl MixedGraph {

    pub fn from_circuit<C: Constraint, S: Circuit<C>>(
        circ: &S, partition: Vec<Vec<usize>>,
        dead_ends_as_outputs: bool
    ) -> MixedGraph {
        // have partitions keep Vec<Vec<usize>>, index by vec index throughout until we make the DAGNodes
        // sorted arr signal list
        let n_parts = partition.len();
        let part_to_signals_arr: Vec<Vec<usize>> = partition.iter().map(|part|
            part.iter().copied().flat_map(|idx| circ.get_constraints()[idx].borrow().signals()).sorted_unstable().dedup().collect()
        ).collect();

        let input_parts: HashSet<usize> = (0..n_parts).filter(|key| part_to_signals_arr[*key].iter().any(|sig| circ.signal_is_input(sig))).collect();
        let mut output_parts: HashSet<usize> = (0..n_parts).filter(|key| part_to_signals_arr[*key].iter().any(|sig| circ.signal_is_output(sig))).collect();

        const NO_PART: usize = usize::MAX;
        let mut coni_to_part: Vec<usize> = vec![NO_PART; circ.n_constraints()];
        for (idx, part) in partition.iter().enumerate() {
            for coni in part.iter().copied() {
                match coni_to_part[coni] {
                    NO_PART => {coni_to_part[coni] = idx;}
                    _ => {panic!("Given partition has overlapping parts");}
                }
            }
        }

        // get the signal indices
        let sig_to_coni = signals_to_constraints_with_them(circ.get_constraints(), None, None);
        
        let mut last_seen_at: Vec<usize> = vec![0;n_parts];
        // note that this is not sorted
        let adjacencies: Vec<Vec<usize>> = (0..n_parts).map(|idx| 
            {let mut neighbours =  Vec::new();
            for part in part_to_signals_arr[idx].iter().copied().flat_map(|sig| sig_to_coni[&sig].iter().copied().map(|coni| coni_to_part[coni])).filter(|opart_id| *opart_id != idx) {
                if last_seen_at[part] != idx + 1 {
                    last_seen_at[part] = idx + 1;
                    neighbours.push(part);
                }
            }
            neighbours}
        ).collect();

        // include dead-ends as outputs
        if dead_ends_as_outputs{ output_parts.extend((0..n_parts).filter(|parti| !input_parts.contains(parti) && adjacencies[*parti].len() == 1)); }
        
        Self::new(partition, adjacencies, input_parts, output_parts)
    }

    pub fn new(partition: Vec<Vec<usize>>, adjacencies:Vec<Vec<usize>>, input_parts: HashSet<usize>, output_parts: HashSet<usize>) -> Self {
        let edges: Vec<(usize, usize)> = adjacencies.iter().enumerate()
                        .flat_map( |(idx, part)| part.into_iter().copied().map(move |x| (idx, x)))
                        .filter(|(a, b)| a < b)
                        .collect();

        let dir_adjacencies = vec![HashSet::new(); partition.len()];

        Self {n: partition.len(), m: edges.len(), partition, adjacencies, dir_adjacencies, edges, input_parts, output_parts, dir_adjacencies_is_outgoing: true}
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

        Self { n: merged_partition.len(), m: edges.len(), partition: merged_partition, adjacencies: merged_adjacencies, dir_adjacencies: merged_dir_adjacencies, edges, input_parts: merged_inputs, output_parts: merged_outputs, dir_adjacencies_is_outgoing: true }
    }

    pub fn invert_edge_direction(&mut self) -> bool {self.dir_adjacencies_is_outgoing = !self.dir_adjacencies_is_outgoing; self.dir_adjacencies_is_outgoing}
    pub fn pair_oriented(&self, u: usize, v: usize) -> bool { self.dir_adjacencies[u].contains(&v) || self.dir_adjacencies[v].contains(&u) }
    pub fn edge_oriented(&self, e: usize) -> bool { self.dir_adjacencies[self.edges[e].0].contains(&self.edges[e].1) || self.dir_adjacencies[self.edges[e].1].contains(&self.edges[e].0) }

    pub fn orient_by_partial_order(&mut self) -> Vec<(usize, usize)> {

        let distance_to_inputs = distance_to_source_set(self.input_parts.iter().copied(), &self.adjacencies);
        let distance_to_outputs = distance_to_source_set(self.output_parts.iter().copied(), &self.adjacencies);

        let part_to_preorder: Vec<(usize, usize)> = (0..self.n).map(|key| (distance_to_inputs[key], distance_to_outputs[key])).collect();

        for e in 0..self.m {
            if self.edge_oriented(e) {continue;}
            let (u, v) = self.edges[e];
            let direction: Option<(usize, usize)> = if lt(part_to_preorder[u], part_to_preorder[v]) {Some((u,v))}
            else if lt(part_to_preorder[v], part_to_preorder[u]) {Some((v,u))} else {None};
            direction.map(|(u,v)| if self.dir_adjacencies_is_outgoing {(u,v)} else {(v,u)});
            if let Some((parent, child)) = direction {self.dir_adjacencies[parent].insert(child);}
        }

        part_to_preorder
    }

    // TODO: convince self that this will never lower the number of oriented edges
    // This is technically better than nothing (assuming the above) but it doesn't seem to help at all
    //      the hard case is when do we decide to go downstairs and doesn't help.
    //      Does help in general with repeated clusters -- though this structure hasn't been problematic otherwise.
    pub fn iterative_orient_by_partial_order(&mut self) -> Vec<(usize, usize)> {

        // A version of BFS that only allows distances if they follow oriented arc directions correctly
        fn distance_to_source_set_under_preorder(source_set: impl Iterator<Item = usize>, adjacencies: &Vec<Vec<usize>>, lt: impl Fn(usize, usize) -> Option<bool>) -> Vec<usize> {

            let mut distance: Vec<usize> = vec![usize::MAX; adjacencies.len()];
            let mut queue: VecDeque<usize> = source_set.collect();
            for idx in queue.iter() {distance[*idx] = 0;}

            while queue.len() > 0 {
                let curr = queue.pop_front().unwrap();
                let next_distance = distance[curr] + 1;
                for adj in adjacencies[curr].iter().copied().filter(|&adj| lt(curr, adj).is_none_or( |x| x ) ) {
                    if distance[adj] == usize::MAX {
                        queue.push_back(adj);
                        distance[adj] = next_distance;
                    }
                }
            }

            distance
        }

        let mut updated_at_least_one_arc = true;
        let mut current_preorder: Vec<(usize, usize)> = self.orient_by_partial_order();

        fn compare(x:usize, y:usize, part_to_preorder: &Vec<(usize, usize)>) -> Option<bool> {
            let x_ord = part_to_preorder[x]; let y_ord = part_to_preorder[y];
            if lt(x_ord, y_ord) {Some(true)} else if lt(y_ord, x_ord) {Some(false)} else {None}
        }

        let mut oriented_edges: usize = self.dir_adjacencies.iter().map(|x| x.len()).sum();
        println!("oriented_edges: {:?}", oriented_edges);

        while updated_at_least_one_arc {
            
            let distance_to_inputs = distance_to_source_set_under_preorder(self.input_parts.iter().copied(), &self.adjacencies, |x, y| compare(x, y, &current_preorder));
            let distance_to_outputs = distance_to_source_set_under_preorder(self.output_parts.iter().copied(), &self.adjacencies, |x, y| compare(y, x, &current_preorder));

            current_preorder = (0..self.n).into_iter().map(|x| (distance_to_inputs[x], distance_to_outputs[x])).collect();
            let new_oriented_edges = self.edges.iter().filter(|&&(x, y)| compare(x, y, &current_preorder).is_some() ).count();
            
            updated_at_least_one_arc = new_oriented_edges > oriented_edges;
            oriented_edges = new_oriented_edges;
            println!("oriented_edges: {:?}", oriented_edges);
        }

        self.dir_adjacencies = self.adjacencies.iter().enumerate().map(|(v, part)| part.into_iter().copied().filter(|&u| compare(v, u, &current_preorder).is_some_and(|x| x == self.dir_adjacencies_is_outgoing) ).collect()).collect();
        current_preorder
    }

    pub fn orient_leaf_parts(&mut self) -> () {

        // leafs that are not two adjacent leafs are directed towards the leaf
        for v in (0..self.n).filter(|&v| self.adjacencies[v].len() == 1 && self.adjacencies[self.adjacencies[v][0]].len() != 1) {
            let u = self.adjacencies[v][0];
            if self.pair_oriented(u, v) {continue;}
            if self.dir_adjacencies_is_outgoing {self.dir_adjacencies[u].insert(v);}
            else {self.dir_adjacencies[v].insert(u);}
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
      
        for (v, arcs) in self.dir_adjacencies.iter().enumerate() {for u in arcs.into_iter().copied() {
            add_arc_to_nodes(if self.dir_adjacencies_is_outgoing {(v,u)} else {(u,v)}, &idx_to_nodeid, &part_to_signals_arr, &mut nodes);
        }}

        (nodes, part_to_signals_arr, idx_to_nodeid)
    }

    pub fn merge_equivalence_classes_by_distance_and_orient(&mut self, debug: usize) ->  Vec<(usize, usize)>
    {
        
        let mut part_to_preorder: Vec<(usize, usize)>;
        // TODO: check if this will only ever take 1 iteration

        // merge equivalence classes into layers
        loop {
            if debug > 1 {println!("---------------------------------------");}
            // TODO: convince self that this wont create cycle
            part_to_preorder = self.orient_by_partial_order();

            let num_fuzzy_edges: usize = (0..self.m).filter(|&e| !self.edge_oriented(e)).count();
           if debug > 1 {println!("num_fuzzy: {:?}", num_fuzzy_edges);}

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

            if debug > 1 {println!("merging: {:?}", count_ints(equal_distance.get_components().into_iter().map(|part| part.len())));}
            *self = self.merge(equal_distance);
        }

        part_to_preorder
    }

    pub fn export_to_dzn(&mut self) -> () {
    
        let fuzzy: Vec<bool> = self.edges.iter()
                        .map(|&(a, b)| !self.pair_oriented(a, b))
                        .collect();
        
        let contains_value: usize = if self.dir_adjacencies_is_outgoing {2} else {1};

        let init_direction: Vec<usize> = self.edges.iter()
                        .map(|&(a, b)| if self.dir_adjacencies[a].contains(&b) {contains_value} else if self.dir_adjacencies[b].contains(&a) {3 - contains_value} else {0} )
                        .collect();
        
        write_dzn("data.dzn", &self.adjacencies, &self.edges, &fuzzy, &init_direction, &self.input_parts, &self.output_parts); 
    }

}