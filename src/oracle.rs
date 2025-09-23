use crate::{Assignment, Maximal, System, cartesian};
use std::fmt::Debug;
use std::{collections::HashSet, hash::Hash, marker::PhantomData};

pub trait LocalOracle<K: Hash + Eq + Copy, V: PartialOrd, S: System<K, V>> {
    // TODO: Change hashset to impl Iterator
    fn approximate_flow(
        &self,
        visited: &HashSet<K>,
        assignment: &dyn Assignment<K, V>,
        possible: &HashSet<(K, K)>,
        system: &S,
    ) -> HashSet<(K, K)>;

    #[must_use]
    fn then(self, other: impl LocalOracle<K, V, S>) -> impl LocalOracle<K, V, S>
    where
        Self: std::marker::Sized,
    {
        ComposeLocal {
            outer: other,
            inner: self,
            _phantom_data: PhantomData,
        }
    }

    #[must_use]
    fn and(self, other: impl LocalOracle<K, V, S>) -> impl LocalOracle<K, V, S>
    where
        Self: std::marker::Sized,
    {
        IntersectLocal {
            left: other,
            right: self,
            _phantom_data: PhantomData,
        }
    }
}

pub struct LocalMaxR;

impl<K: Hash + Eq + Copy + Debug, V: Maximal, S: System<K, V>> LocalOracle<K, V, S> for LocalMaxR {
    fn approximate_flow(
        &self,
        visited: &HashSet<K>,
        assignment: &dyn Assignment<K, V>,
        _possible: &HashSet<(K, K)>,
        system: &S,
    ) -> HashSet<(K, K)> {
        let unvisited = system
            .variables()
            .into_iter()
            .filter(|v| !visited.contains(v))
            .collect::<HashSet<_>>();
        let unvisited_dep = crate::cartesian(&system.variables(), &unvisited);
        let self_dep = visited.iter().map(|&x| (x, x)).collect();
        let max_dep = visited.iter().flat_map(|&y| {
            if system.evaluate(y, assignment).is_maximal() {
                // TODO: is it correct to just include every `x` from variables?
                // TODO: could probably be improved with smallvec
                system
                    .variables()
                    .iter()
                    .map(|&x| (x, y))
                    .collect::<HashSet<_>>()
            } else {
                HashSet::new()
            }
        });
        unvisited_dep
            .union(&self_dep)
            .copied()
            .chain(max_dep)
            .collect()
    }
}

pub struct SMax;

impl<K: Hash + Eq + Copy, V: Maximal, S: System<K, V>> LocalOracle<K, V, S> for SMax {
    fn approximate_flow(
        &self,
        _visited: &HashSet<K>,
        assignment: &dyn Assignment<K, V>,
        _possible: &HashSet<(K, K)>,
        system: &S,
    ) -> HashSet<(K, K)> {
        let variables = system.variables();
        cartesian(&variables, &variables)
            .into_iter()
            .filter(|(x, y)| !assignment.get(x).is_maximal() && !assignment.get(y).is_maximal())
            .collect()
    }
}

pub struct ComposeLocal<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    S: System<K, V>,
    T: LocalOracle<K, V, S>,
    U: LocalOracle<K, V, S>,
> {
    outer: T,
    inner: U,
    _phantom_data: PhantomData<(K, V, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    S: System<K, V>,
    T: LocalOracle<K, V, S>,
    U: LocalOracle<K, V, S>,
> LocalOracle<K, V, S> for ComposeLocal<K, V, S, T, U>
{
    fn approximate_flow(
        &self,
        visited: &HashSet<K>,
        assignment: &dyn Assignment<K, V>,
        possible: &HashSet<(K, K)>,
        system: &S,
    ) -> HashSet<(K, K)> {
        let Self { outer, inner, .. } = self;
        outer.approximate_flow(
            visited,
            assignment,
            &inner.approximate_flow(visited, assignment, possible, system),
            system,
        )
    }
}

pub struct IntersectLocal<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    S: System<K, V>,
    T: LocalOracle<K, V, S>,
    U: LocalOracle<K, V, S>,
> {
    left: T,
    right: U,
    _phantom_data: PhantomData<(K, V, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    S: System<K, V>,
    T: LocalOracle<K, V, S>,
    U: LocalOracle<K, V, S>,
> LocalOracle<K, V, S> for IntersectLocal<K, V, S, T, U>
{
    fn approximate_flow(
        &self,
        visited: &HashSet<K>,
        assignment: &dyn Assignment<K, V>,
        possible: &HashSet<(K, K)>,
        system: &S,
    ) -> HashSet<(K, K)> {
        let Self { left, right, .. } = self;
        let left = left.approximate_flow(visited, assignment, possible, system);
        let right = right.approximate_flow(visited, assignment, possible, system);
        left.intersection(&right).copied().collect()
    }
}
