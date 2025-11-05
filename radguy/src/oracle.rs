use crate::{
    Assignment, Cartesian, Diagonal, Intersect, Maximal, PairUniverse, System, Union, Universe,
    Without,
};
use std::fmt::Debug;
use std::{collections::HashSet, hash::Hash, marker::PhantomData};

pub trait LocalOracle<K: Hash + Eq + Copy, V: PartialOrd, PS, S: System<K, V>> {
    fn approximate_flow(
        &self,
        visited: &HashSet<K>,
        assignment: &impl Assignment<K, V>,
        possible: &PS,
        system: &S,
    ) -> PS;

    #[must_use]
    fn then(self, other: impl LocalOracle<K, V, PS, S>) -> impl LocalOracle<K, V, PS, S>
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
    fn and(self, other: impl LocalOracle<K, V, PS, S>) -> impl LocalOracle<K, V, PS, S>
    where
        Self: std::marker::Sized,
        PS: Intersect,
    {
        IntersectLocal {
            left: other,
            right: self,
            _phantom_data: PhantomData,
        }
    }
}

#[derive(Default)]
pub struct LocalMaxR;

impl<
    K: Hash + Eq + Copy + Debug,
    V: Maximal,
    PS: FromIterator<(K, K)> + Union,
    S: System<K, V> + Universe<HashSet<K>>,
> LocalOracle<K, V, PS, S> for LocalMaxR
where
    HashSet<K>: Cartesian<Output = PS> + Without<HashSet<K>> + Diagonal<Output = PS>,
{
    fn approximate_flow(
        &self,
        visited: &HashSet<K>,
        assignment: &impl Assignment<K, V>,
        _possible: &PS,
        system: &S,
    ) -> PS {
        let unvisited = system.universe().without(visited);
        let unvisited_dep = system.universe().cartesian(&unvisited);
        // TODO: Use universe diagonal as it is easier to construct
        let self_dep = visited.diagonal();

        // Alternative version
        let max_dep = visited
            .iter()
            .flat_map(|&y| {
                if system.evaluate(y, assignment).is_maximal() {
                    std::iter::empty().collect::<Vec<_>>()
                } else {
                    system.universe().iter().map(|&x| (x, y)).collect()
                }
            })
            .collect();

        unvisited_dep.union(self_dep).union(max_dep)
    }
}

#[derive(Default)]
pub struct SMax;

// TODO: Make this more general than HashSet
impl<K: Hash + Eq + Copy, V: Maximal, S: System<K, V> + PairUniverse<K, HashSet<(K, K)>>>
    LocalOracle<K, V, HashSet<(K, K)>, S> for SMax
{
    fn approximate_flow(
        &self,
        _visited: &HashSet<K>,
        assignment: &impl Assignment<K, V>,
        _possible: &HashSet<(K, K)>,
        system: &S,
    ) -> HashSet<(K, K)> {
        system
            .pair_universe()
            .into_iter()
            .filter(|(x, y)| !assignment.get(x).is_maximal() && !assignment.get(y).is_maximal())
            .collect::<HashSet<_>>()
    }
}

pub struct ComposeLocal<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S>,
    U: LocalOracle<K, V, PairSet, S>,
> {
    outer: T,
    inner: U,
    _phantom_data: PhantomData<(K, V, PairSet, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S>,
    U: LocalOracle<K, V, PairSet, S>,
> LocalOracle<K, V, PairSet, S> for ComposeLocal<K, V, PairSet, S, T, U>
{
    fn approximate_flow(
        &self,
        visited: &HashSet<K>,
        assignment: &impl Assignment<K, V>,
        possible: &PairSet,
        system: &S,
    ) -> PairSet {
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
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S>,
    U: LocalOracle<K, V, PairSet, S>,
> {
    left: T,
    right: U,
    _phantom_data: PhantomData<(K, V, PairSet, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet: Intersect,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S>,
    U: LocalOracle<K, V, PairSet, S>,
> LocalOracle<K, V, PairSet, S> for IntersectLocal<K, V, PairSet, S, T, U>
{
    fn approximate_flow(
        &self,
        visited: &HashSet<K>,
        assignment: &impl Assignment<K, V>,
        possible: &PairSet,
        system: &S,
    ) -> PairSet {
        let Self { left, right, .. } = self;
        let left = left.approximate_flow(visited, assignment, possible, system);
        let right = right.approximate_flow(visited, assignment, possible, system);
        left.intersect(&right)
    }
}

#[derive(Default)]
pub struct TrivialOracle;

impl<K: Hash + Eq + Copy, V: Maximal, PairSet, S: System<K, V> + PairUniverse<K, PairSet>>
    LocalOracle<K, V, PairSet, S> for TrivialOracle
{
    fn approximate_flow(
        &self,
        _visited: &HashSet<K>,
        _assignment: &impl Assignment<K, V>,
        _possible: &PairSet,
        system: &S,
    ) -> PairSet {
        system.pair_universe()
    }
}
