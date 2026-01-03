use std::marker::PhantomData;
use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};

use utils::structure::NodeInfo;
use circuits_and_constraints::constraint::Constraint;
use circuits_and_constraints::circuit::Circuit;

pub mod dag_from_partition;
pub mod dag_postprocessing;
pub mod equivalence_classes;
pub mod iterated_label_propagation;

pub struct DAGNode<'a, C: Constraint + 'a, S: Circuit<C> + 'a> {
    circ : &'a S,
    id : usize,
    constraints : Vec<usize>,
    input_signals : HashSet<usize>,
    output_signals : HashSet<usize>,
    successors : Vec<usize>,
    predecessors : Vec<usize>,

    _phantom: PhantomData<C>
}

impl<'a, C: Constraint + 'a, S: Circuit<C> + 'a> DAGNode<'a, C, S> {

    pub fn new(circ: &'a S, node_id: usize, constraints: Vec<usize>, input_signals: HashSet<usize>, output_signals: HashSet<usize>) -> DAGNode<'a, C, S> {
        
        Self { circ: circ, id: node_id, constraints: constraints, input_signals: input_signals, output_signals: output_signals, successors: Vec::new(), predecessors: Vec::new(), _phantom: PhantomData }
    }

    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    pub fn get_circ(&self) -> &'a S {
        self.circ
    }

    pub fn add_successors(&mut self, to_add: impl Iterator<Item = usize>) -> () {
        self.successors.extend(to_add)
    }

    pub fn get_successors(&self) -> &Vec<usize> {
        &self.successors
    }

    pub fn add_predecessors(&mut self, to_add: impl Iterator<Item = usize>) -> () {
        self.predecessors.extend(to_add)
    }

    pub fn get_predecessors(&self) -> &Vec<usize> {
        &self.predecessors
    }

    pub fn get_input_signals(&self) -> &HashSet<usize> {
        &self.input_signals
    }

    pub fn update_input_signals(&mut self, to_add: impl Iterator<Item = usize>) -> () {
        self.input_signals.extend(to_add)
    }

    pub fn get_output_signals(&self) -> &HashSet<usize> {
        &self.output_signals
    }

    pub fn update_output_signals(&mut self, to_add: impl Iterator<Item = usize>) -> () {
        self.output_signals.extend(to_add)
    }

    pub fn get_constraint_indices(&self) -> impl Iterator<Item = usize> {
        self.constraints.iter().copied()
    }

    pub fn get_subcircuit(&self) -> S::SubCircuit<'a> {
        self.circ.take_subcircuit(&self.constraints, Some(&self.input_signals), Some(&self.output_signals), None, None)
    }

    pub fn to_json(self, inverse_constraint_mapping: Option<&[usize]>, inverse_signal_mapping: Option<&[usize]>) -> NodeInfo {
        let signal_mapping = |sig: usize| if inverse_signal_mapping.is_none() {sig} else {inverse_signal_mapping.unwrap()[sig]};
        let constraint_mapping = |coni: usize| if inverse_constraint_mapping.is_none() {coni} else {inverse_constraint_mapping.unwrap()[coni]};
        let signals: Vec<usize> = self.constraints.iter().flat_map(|x| self.circ.get_constraints()[*x].borrow().signals()).collect::<HashSet<usize>>().into_iter().map(signal_mapping).collect();

        NodeInfo {
            node_id: self.id, 
            constraints: self.constraints.into_iter().map(constraint_mapping).collect(), 
            input_signals: self.input_signals.into_iter().map(signal_mapping).collect(), 
            output_signals: self.output_signals.into_iter().map(signal_mapping).collect(), 
            signals: signals, 
            successors: self.successors
        }
    }

    pub fn merge_nodes(to_merge: Vec<usize>, nodes: &mut HashMap<usize, DAGNode<'a, C, S>>, sig_to_coni: &HashMap<usize, Vec<usize>>, coni_to_node: &mut Vec<usize>) -> usize {
        // not especially elegant but whatever

        let root: usize = to_merge[0];

        let new_successors: Vec<usize> = to_merge.iter().flat_map(|nkey| nodes.get(nkey).unwrap().get_successors()).copied().filter(|nkey| !to_merge.contains(nkey)).collect::<HashSet<usize>>().into_iter().collect();
        let new_predecessors: Vec<usize> = to_merge.iter().flat_map(|nkey| nodes.get(nkey).unwrap().get_predecessors()).copied().filter(|nkey| !to_merge.contains(nkey)).collect::<HashSet<usize>>().into_iter().collect();

        // fix parents to point to root
        for nkey in new_predecessors.iter() {
            nodes.get_mut(nkey).unwrap().successors = nodes.get(nkey).unwrap().successors.iter().copied().filter(|okey| !to_merge.contains(okey)).chain([root].into_iter()).collect();
        }
        // fix children to point to root
        for nkey in new_successors.iter() {
            nodes.get_mut(&nkey).unwrap().predecessors = nodes.get(&nkey).unwrap().predecessors.iter().copied().filter(|okey| !to_merge.contains(okey)).chain([root].into_iter()).collect();
        }

        let new_constraints: Vec<usize> = to_merge.iter().flat_map(|nkey| nodes.get(nkey).unwrap().constraints.iter()).copied().collect();

        let circ: &'a S = nodes.get(&root).unwrap().circ;

        let new_input_signals: HashSet<usize> = to_merge.iter().flat_map(|nkey| nodes.get(nkey).unwrap().input_signals.iter()).copied().filter(|sig|
            circ.signal_is_input(sig) || sig_to_coni.get(sig).unwrap().iter().copied().any(|coni| new_predecessors.contains(&coni_to_node[coni]))
        ).collect();
        let new_output_signals: HashSet<usize> = to_merge.iter().flat_map(|nkey| nodes.get(nkey).unwrap().output_signals.iter()).copied().filter(|sig|
            circ.signal_is_output(sig) || sig_to_coni.get(sig).unwrap().iter().copied().any(|coni| new_successors.contains(&coni_to_node[coni]))
        ).collect();

        // fix coni_to_node
        for coni in new_constraints.iter().copied() { coni_to_node[coni] = root; };
        for okey in to_merge.iter().skip(1) {nodes.remove(okey);};

        let newnode = DAGNode { circ: circ, id: root, 
            constraints: new_constraints, 
            input_signals: new_input_signals, output_signals: new_output_signals, 
            successors: new_successors, predecessors: new_predecessors, 
            _phantom: PhantomData 
        };

        nodes.insert(root, newnode);
        root
    }
}
