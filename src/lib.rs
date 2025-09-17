use std::{collections::HashSet, hash::Hash};

pub mod extension;

pub trait System<VarKey: Clone + Copy, VarValue> {
    fn evaluate(&self, key: VarKey, assignment: &dyn Assignment<VarKey, VarValue>) -> VarValue;

    fn arguments(&self, key: VarKey) -> HashSet<VarKey>;
    fn variables(&self) -> HashSet<VarKey>;
    fn bottom_assignment(&self) -> Box<dyn Assignment<VarKey, VarValue>>;
}

pub trait Assignment<K, V> {
    fn get(&self, key: K) -> V;
    fn update(&mut self, key: K, value: V);
}

pub trait LocalOracle<K: Hash + Eq + Copy, V, S: System<K, V>> {
    fn flow(
        &self,
        visited: &HashSet<K>,
        assignment: &dyn Assignment<K, V>,
        possible: &HashSet<(K, K)>,
        system: &S,
    ) -> HashSet<(K, K)>;
}

pub fn kleene_local<K: Clone + Copy + Hash + Eq, V: Eq, S: System<K, V>>(
    system: &S,
    target: K,
    oracle: &dyn LocalOracle<K, V, S>,
) -> V {
    let mut assignment = system.bottom_assignment();
    let mut visited = HashSet::from([target]);
    let mut todo = local_dependencies(target, &visited, &*assignment, oracle, system);

    while let Some(&x) = todo.iter().next() {
        let evaluated = system.evaluate(x, &*assignment);
        if assignment.get(x) != evaluated || !system.arguments(x).is_subset(&visited) {
            assignment.update(x, evaluated);
            visited = visited.union(&system.arguments(x)).copied().collect();
            todo = local_dependencies(target, &visited, &*assignment, oracle, system);
        }
    }

    assignment.get(target)
}

fn local_dependencies<K: Clone + Copy + Hash + Eq, V, S: System<K, V>>(
    variable: K,
    visited: &HashSet<K>,
    assignment: &dyn Assignment<K, V>,
    oracle: &dyn LocalOracle<K, V, S>,
    system: &S,
) -> HashSet<K> {
    let variables = &system.variables();
    let d = oracle.flow(
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

#[cfg(test)]
mod tests {}
