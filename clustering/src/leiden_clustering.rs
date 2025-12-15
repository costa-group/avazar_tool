use std::collections::HashSet;

use single_clustering::network::CSRNetwork;
use single_clustering::community_search::leiden::{LeidenOptimizer, LeidenConfig};
use single_clustering::community_search::leiden::partition::{RBConfigurationPartition, VertexPartition};
use single_clustering::network::grouping::{VectorGrouping};
use graphrs::Graph;
// use graphrs::algorithms::community::leiden::{leiden, QualityFunction};

use graphrs::algorithms::community::louvain::{louvain_communities};

pub trait CanLeiden {
    fn num_edges(&self) -> usize;
    fn get_partition(self: Box<Self>, target: f64, max_iterations: usize, seed: u64) -> Vec<Vec<usize>>;
}

impl CanLeiden for CSRNetwork<f64, f64> {
    fn num_edges(&self) -> usize {
        self.edge_count()
    }

    fn get_partition(self: Box<Self>, resolution: f64, max_iterations: usize, seed: u64) -> Vec<Vec<usize>> {
        let config = LeidenConfig {
            max_iterations: max_iterations,
            tolerance: 1e-6,
            seed: Some(seed),
            ..Default::default()
        };

        // Initialize the optimizer
        let mut optimizer = LeidenOptimizer::new(config);
        let mut partition: RBConfigurationPartition<f64, VectorGrouping> = RBConfigurationPartition::new_singleton(*self, resolution);

        // Find communities using modularity optimization
        let _ = optimizer.optimize_single_partition::<f64, VectorGrouping, RBConfigurationPartition<f64, VectorGrouping>>(&mut partition, None);

        partition.get_communities()
    }
}

impl CanLeiden for Graph<usize, usize> {
    fn num_edges(&self) -> usize {
        self.number_of_edges()
    }

    fn get_partition(self: Box<Self>, resolution: f64, _max_iterations: usize, seed: u64) -> Vec<Vec<usize>> {
        // let result = leiden(&self, true, QualityFunction::Modularity, Some(resolution), None, None);
        let result: Vec<HashSet<usize>> = louvain_communities(&self, true, Some(resolution), Some(1e-6), Some(seed)).unwrap(); // fixing a bug in their implementation


        result.into_iter().map(|set| set.into_iter().collect()).collect()
    }
}