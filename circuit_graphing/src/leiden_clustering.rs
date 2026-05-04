use std::collections::{HashMap, HashSet};

use utils::structure::WeightedArcs;
use graphrs::IdentityIndexer;
use graphrs::algorithms::community::louvain::{louvain_communities_from_weighted_arcs as rs_louvain_communities};

use xgraph::Graph as XGraph;
use xgraph::graph::algorithms::leiden_clustering::{CommunityDetection, CommunityConfig as XCommunityConfig};


pub trait CanLeiden {
    fn num_edges(&self) -> usize;
    fn get_partition(self: Box<Self>, target: f64, max_iterations: usize, seed: Option<u64>) -> Vec<Vec<usize>>;
}

impl CanLeiden for XGraph<f64, (), ()> {
    fn num_edges(&self) -> usize {
        self.edges.len()
    }

    fn get_partition(self: Box<Self>, resolution: f64, max_iterations: usize, seed: Option<u64>) -> Vec<Vec<usize>> {
        
        let leiden_config = XCommunityConfig { gamma: 1.0, resolution: resolution, iterations: max_iterations, deterministic: true, seed: seed};
        let result: HashMap<usize, Vec<usize>> = self.detect_communities_with_config(leiden_config).unwrap();

        result.into_values().collect()
    }
}

impl CanLeiden for WeightedArcs<usize> {
    fn num_edges(&self) -> usize {
        self.arcs.len()
    }

    fn get_partition(self: Box<Self>, resolution: f64, _max_iterations: usize, seed: Option<u64>) -> Vec<Vec<usize>> {
        // graphrs erroneously divides by 0.5 * m instead of 2 * m ... so we need to divide by 4 to correct this.
        // NOTE: passing arcs directly is ONLY possible because of the use of the IdentityIndexer, otherwise it need to pass arcs with T mapped to usize by the indexer
        let result: Vec<HashSet<usize, _>> = rs_louvain_communities(self.original_nodes, self.arcs, IdentityIndexer, true, Some(resolution * 0.5), Some(1e-6), seed).unwrap(); // fixing a bug in their implementation
        result.into_iter().map(|set| set.into_iter().collect()).collect()
    }
}