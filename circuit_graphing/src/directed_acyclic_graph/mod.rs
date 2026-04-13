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

    pub fn new(circ: &'a S, node_id: usize, constraints: Vec<usize>, input_signals: HashSet<usize>, output_signals: HashSet<usize>, successors: Option<Vec<usize>>, predecessors: Option<Vec<usize>>) -> DAGNode<'a, C, S> {
        Self { circ: circ, id: node_id, constraints: constraints, input_signals: input_signals, output_signals: output_signals, successors: successors.unwrap_or_else(|| Vec::new()), predecessors: predecessors.unwrap_or_else(|| Vec::new()), _phantom: PhantomData }
    }

    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    pub fn get_circ(&self) -> &'a S {
        self.circ
    }

    pub fn signals(&self) -> HashSet<usize> {
        self.get_constraint_indices().flat_map(|coni| self.circ.get_constraints()[coni].borrow().signals()).collect()
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
            is_custom: false,
            predecessors: self.predecessors,
            successors: self.successors
        }
    }

    pub fn merge_nodes(to_merge: HashSet<usize>, nodes: &mut HashMap<usize, DAGNode<'a, C, S>>, sig_to_coni: &HashMap<usize, Vec<usize>>, coni_to_node: &mut Vec<usize>) -> usize {
        // not especially elegant but whatever
        if to_merge.len() == 0 {panic!("Attempting to merge no nodes");}
        let root: usize = *to_merge.iter().next().unwrap();

        let new_successors: HashSet<usize> = to_merge.iter().flat_map(|nkey| nodes.get(nkey).unwrap().get_successors()).copied().filter(|nkey| !to_merge.contains(nkey)).collect();
        let new_predecessors: HashSet<usize> = to_merge.iter().flat_map(|nkey| nodes.get(nkey).unwrap().get_predecessors()).copied().filter(|nkey| !to_merge.contains(nkey)).collect();

        // fix parents to point to root
        for nkey in new_predecessors.iter() {
            let nnode = nodes.get_mut(nkey).unwrap();nnode.successors.retain_mut(|okey| !to_merge.contains(okey));nnode.successors.push(root);
        }
        // fix children to point to root
        for nkey in new_successors.iter() {
            let nnode = nodes.get_mut(nkey).unwrap();nnode.predecessors.retain_mut(|okey| !to_merge.contains(okey));nnode.predecessors.push(root);
        }

        let circ: &'a S = nodes[&root].circ;        

        let mut new_constraints: Vec<usize> = Vec::new();
        let mut new_input_signals: HashSet<usize> = HashSet::new();
        let mut new_output_signals: HashSet<usize> = HashSet::new();

        for nkey in to_merge.iter() {

            let DAGNode { constraints, input_signals, output_signals, .. } = nodes.remove(nkey).unwrap();

            new_constraints.extend(constraints);
            new_input_signals.extend(input_signals.into_iter().filter(|sig|
                circ.signal_is_input(sig) || sig_to_coni[sig].iter().copied().map(|coni| coni_to_node[coni]).filter(|nodi| new_predecessors.contains(nodi)).count() > 0
            ));
            new_output_signals.extend(output_signals.into_iter().filter(|sig|
                circ.signal_is_output(sig) || sig_to_coni[sig].iter().copied().map(|coni| coni_to_node[coni]).filter(|nodi| new_successors.contains(nodi)).count() > 0
            ));

        }

        // fix coni_to_node
        for coni in new_constraints.iter().copied() { coni_to_node[coni] = root; };

        let newnode = DAGNode { circ: circ, id: root, 
            constraints: new_constraints, 
            input_signals: new_input_signals, output_signals: new_output_signals, 
            successors: new_successors.into_iter().collect(), predecessors: new_predecessors.into_iter().collect(), 
            _phantom: PhantomData 
        };

        nodes.insert(root, newnode);
        root
    }

    pub fn replace_circ<'b, T: Circuit<C> + 'b>(self, circ: &'b T) -> DAGNode<'b, C, T> where 'b : 'a {
        let Self { id, constraints, input_signals, output_signals, successors, predecessors, ..} = self;
        DAGNode::<'b, C, T>::new(circ, id, constraints, input_signals, output_signals, Some(successors), Some(predecessors))
    }

    pub fn signal_to_nodes(nodes: impl Iterator<Item = &'a DAGNode<'a, C, S>>) -> HashMap<usize, Vec<usize>> {
        let mut signal_to_nodes: HashMap<usize, Vec<usize>> = HashMap::new();

        for node in nodes {
            for sig in node.signals() {
                signal_to_nodes.entry(sig).or_insert_with(|| Vec::new()).push(node.id);
            }
        }

        signal_to_nodes
    }

    pub fn map_internal_indices(&mut self, inverse_constraint_mapping: Option<&[usize]>, inverse_signal_mapping: Option<&[usize]>) -> () {
        // TODO: code duplication
        let signal_mapping = |sig: usize| if inverse_signal_mapping.is_none() {sig} else {inverse_signal_mapping.unwrap()[sig]};
        let constraint_mapping = |coni: usize| if inverse_constraint_mapping.is_none() {coni} else {inverse_constraint_mapping.unwrap()[coni]};

        self.constraints = self.constraints.iter().copied().map(constraint_mapping).collect();
        self.input_signals = self.input_signals.iter().copied().map(signal_mapping).collect();
        self.output_signals = self.output_signals.iter().copied().map(signal_mapping).collect();
    }
}
