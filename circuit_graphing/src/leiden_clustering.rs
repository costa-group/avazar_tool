use std::collections::{HashSet, HashMap, BTreeSet};

use graphrs::Graph as RSGraph;
use graphrs::IdentityIndexer;
use graphrs::algorithms::community::louvain::{louvain_communities_consume as rs_louvain_communities};

use xgraph::Graph as XGraph;
use xgraph::graph::algorithms::leiden_clustering::{CommunityDetection, CommunityConfig as XCommunityConfig};


pub trait CanLeiden {
    fn num_edges(&self) -> usize;
    fn get_partition(self: Box<Self>, target: f64, max_iterations: usize, seed: u64) -> Vec<Vec<usize>>;
}

impl CanLeiden for XGraph<f64, (), ()> {
    fn num_edges(&self) -> usize {
        self.edges.len()
    }

    fn get_partition(self: Box<Self>, resolution: f64, max_iterations: usize, seed: u64) -> Vec<Vec<usize>> {
        
        let leiden_config = XCommunityConfig { gamma: 1.0, resolution: resolution, iterations: max_iterations, deterministic: true, seed: Some(seed)};
        let result: HashMap<usize, Vec<usize>> = self.detect_communities_with_config(leiden_config).unwrap();

        result.into_values().collect()
    }
}

impl CanLeiden for RSGraph<usize, IdentityIndexer> {
    fn num_edges(&self) -> usize {
        self.number_of_edges()
    }

    fn get_partition(self: Box<Self>, resolution: f64, _max_iterations: usize, seed: u64) -> Vec<Vec<usize>> {
        // graphrs erroneously divides by 0.5 * m instead of 2 * m ... so we need to divide by 4 to correct this.

        // let result = leiden(&self, true, QualityFunction::Modularity, Some(resolution), None, None);
        let result: Vec<BTreeSet<usize>> = rs_louvain_communities(*self, true, Some(resolution * 0.5), Some(1e-6), Some(seed)).unwrap(); // fixing a bug in their implementation

        result.into_iter().map(|set| set.into_iter().collect()).collect()
    }
}