#![feature(negative_impls)]
use crate::oracle::LocalOracle;
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

pub mod extension;
pub mod oracle;

pub trait System<VarKey: Clone + Copy, VarValue: PartialOrd> {
    fn evaluate(&self, key: VarKey, assignment: &dyn Assignment<VarKey, VarValue>) -> VarValue;

    fn arguments(&self, key: VarKey) -> HashSet<VarKey>;
    fn variables(&self) -> HashSet<VarKey>;
    fn bottom_assignment(&self) -> impl Assignment<VarKey, VarValue>;
}

pub trait Assignment<K, V> {
    fn get(&self, key: &K) -> V;
    fn update(&mut self, key: K, value: V);
}

impl<K: Hash + Eq, V: Bottom + Clone, S: ::std::hash::BuildHasher> Assignment<K, V>
    for HashMap<K, V, S>
{
    fn get(&self, key: &K) -> V {
        self.get(key).cloned().unwrap_or_else(V::bottom)
    }

    fn update(&mut self, key: K, value: V) {
        self.insert(key, value);
    }
}

pub fn kleene_local<K: Clone + Copy + Hash + Eq, V: Eq + PartialOrd, S: System<K, V>>(
    system: &S,
    target: K,
    oracle: &dyn LocalOracle<K, V, S>,
) -> V {
    let mut assignment = system.bottom_assignment();
    let mut visited = HashSet::from([target]);
    let mut todo = local_dependencies(target, &visited, &assignment, oracle, system);

    while let Some(&x) = todo.iter().next() {
        todo.remove(&x);
        let evaluated = system.evaluate(x, &assignment);
        if assignment.get(&x) != evaluated || !system.arguments(x).is_subset(&visited) {
            assignment.update(x, evaluated);
            visited = visited.union(&system.arguments(x)).copied().collect();
            todo = local_dependencies(target, &visited, &assignment, oracle, system);
        }
    }

    assignment.get(&target)
}

fn local_dependencies<K: Clone + Copy + Hash + Eq, V: PartialOrd, S: System<K, V>>(
    variable: K,
    visited: &HashSet<K>,
    assignment: &dyn Assignment<K, V>,
    oracle: &dyn LocalOracle<K, V, S>,
    system: &S,
) -> HashSet<K> {
    let variables = &system.variables();
    let d = oracle.approximate_flow(
        visited,
        assignment,
        &cartesian(variables, variables),
        system,
    );
    d.into_iter()
        .filter_map(|(x, y)| if y == variable { Some(x) } else { None })
        .filter(|x| visited.contains(x))
        .collect()
}

fn cartesian<T: Hash + Eq + Clone, U: Hash + Eq + Clone>(
    a: &HashSet<T>,
    b: &HashSet<U>,
) -> HashSet<(T, U)> {
    a.iter()
        .flat_map(|x| b.iter().map(|y| (x.clone(), y.clone())).collect::<Vec<_>>())
        .collect()
}

pub trait Maximal: PartialOrd {
    fn is_maximal(&self) -> bool;
}

impl Maximal for bool {
    fn is_maximal(&self) -> bool {
        *self
    }
}

pub trait Bottom: PartialOrd {
    fn bottom() -> Self;
}

impl Bottom for bool {
    fn bottom() -> Self {
        false
    }
}

#[cfg(test)]
mod tests {}
