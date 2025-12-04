// use std::collections::{BTreeMap, HashMap, VecDeque};
// use std::fmt::Debug;
// use std::hash::{DefaultHasher, Hash};
// use std::{collections::HashSet, default};

// use radguy::Assignment;
// use radguy::{
//     Arguments, Bottom, Maximal, PairUniverse, System, Universe, kleene_local, oracle::TrivialOracle,
// };

// // Can not use the Hash trait as both it and HashMap are foreign.
// fn hash(value: T) {
//     let hasher = DefaultHasher::new();
//     value
// }

// fn get_optimal_iterations<
//     V: Eq + PartialOrd + Bottom + Clone + Maximal + Hash,
//     S: System<K, V> + Arguments<K, HashSet<K>> + Universe<HashSet<K>> + PairUniverse<HashSet<(K, K)>>,
//     K: Copy + Hash + Eq + Debug + Ord,
// >(
//     system: &mut S,
//     target_key: K,
//     target_value: V,
// ) -> u32 {
//     let mut visited = HashSet::<BTreeMap<K, V>>::default();
//     let mut que = VecDeque::new();
//     let hasher = DefaultHasher::new();
//     let mut assignment = system.bottom_assignment();
//     que.push_back(assignment);

//     let mut depth = 0;

//     while let Some(assignment) = que.pop_front()
//         && assignment.get_assignment(&target_key) != target_value
//     {

//     }

//     todo!()
// }'

// fn main() {
//     println!("Hello, world!");
// }
