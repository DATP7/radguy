use itertools::iproduct;

use crate::{Assignment, Cartesian, IterSet, Maximal, System};
use std::fmt::Debug;
use std::{collections::HashSet, hash::Hash, marker::PhantomData};

pub trait LocalOracle<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PS: IterSet<Item = (K, K)>,
    VS: IterSet<Item = K>,
    S: System<K, V, PS, VS>,
>
{
    fn approximate_flow(
        &self,
        visited: &VS,
        assignment: &impl Assignment<K, V>,
        possible: &PS,
        system: &S,
    ) -> PS;

    #[must_use]
    fn then(self, other: impl LocalOracle<K, V, PS, VS, S>) -> impl LocalOracle<K, V, PS, VS, S>
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
    fn and(self, other: impl LocalOracle<K, V, PS, VS, S>) -> impl LocalOracle<K, V, PS, VS, S>
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

impl<
    K: Hash + Eq + Copy + Debug,
    V: Maximal,
    PS: IterSet<Item = (K, K)> + FromIterator<(K, K)>,
    VS: IterSet<Item = K>,
    S: System<K, V, PS, VS>,
> LocalOracle<K, V, PS, VS, S> for LocalMaxR
{
    fn approximate_flow(
        &self,
        visited: &VS,
        assignment: &impl Assignment<K, V>,
        _possible: &PS,
        system: &S,
    ) -> PS {
        let unvisited = system
            .variables()
            .iter()
            .copied()
            .filter(|v| !visited.contains(v))
            .collect::<HashSet<_>>();
        let variables = system.variables();
        let unvisited_dep = iproduct!(variables.iter().copied(), unvisited.iter().copied());
        let self_dep = visited.iter().map(|&x| (x, x));
        let max_dep = visited.iter().flat_map(|&y| {
            // TODO: Maybe not hashsets
            if system.evaluate(y, assignment).is_maximal() {
                HashSet::new()
            } else {
                // TODO: Can this just be visited instead?
                system
                    .variables()
                    .iter()
                    .map(|&x| (x, y))
                    .collect::<HashSet<_>>()
            }
        });
        unvisited_dep.chain(self_dep).chain(max_dep).collect()
    }
}

pub struct SMax;

impl<K: Hash + Eq + Copy, V: Maximal, S: System<K, V, HashSet<(K, K)>, HashSet<K>>>
    LocalOracle<K, V, HashSet<(K, K)>, HashSet<K>, S> for SMax
{
    fn approximate_flow(
        &self,
        _visited: &HashSet<K>,
        assignment: &impl Assignment<K, V>,
        _possible: &HashSet<(K, K)>,
        system: &S,
    ) -> HashSet<(K, K)> {
        let variables = system.variables();
        variables
            .cartesian(&variables)
            .into_iter()
            .filter(|(x, y)| !assignment.get(x).is_maximal() && !assignment.get(y).is_maximal())
            // TODO: Consider adding FromIterator to IterSet and using that here
            .collect::<HashSet<_>>()
    }
}

pub struct ComposeLocal<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    P: IterSet<Item = (K, K)>,
    I: IterSet<Item = K>,
    S: System<K, V, P, I>,
    T: LocalOracle<K, V, P, I, S>,
    U: LocalOracle<K, V, P, I, S>,
> {
    outer: T,
    inner: U,
    _phantom_data: PhantomData<(K, V, P, I, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    P: IterSet<Item = (K, K)>,
    I: IterSet<Item = K>,
    S: System<K, V, P, I>,
    T: LocalOracle<K, V, P, I, S>,
    U: LocalOracle<K, V, P, I, S>,
> LocalOracle<K, V, P, I, S> for ComposeLocal<K, V, P, I, S, T, U>
{
    fn approximate_flow(
        &self,
        visited: &I,
        assignment: &impl Assignment<K, V>,
        possible: &P,
        system: &S,
    ) -> P {
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
    P: IterSet<Item = (K, K)>,
    I: IterSet<Item = K>,
    S: System<K, V, P, I>,
    T: LocalOracle<K, V, P, I, S>,
    U: LocalOracle<K, V, P, I, S>,
> {
    left: T,
    right: U,
    _phantom_data: PhantomData<(K, V, P, I, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    P: IterSet<Item = (K, K)>,
    I: IterSet<Item = K>,
    S: System<K, V, P, I>,
    T: LocalOracle<K, V, P, I, S>,
    U: LocalOracle<K, V, P, I, S>,
> LocalOracle<K, V, P, I, S> for IntersectLocal<K, V, P, I, S, T, U>
{
    fn approximate_flow(
        &self,
        visited: &I,
        assignment: &impl Assignment<K, V>,
        possible: &P,
        system: &S,
    ) -> P {
        let Self { left, right, .. } = self;
        let left = left.approximate_flow(visited, assignment, possible, system);
        let right = right.approximate_flow(visited, assignment, possible, system);
        left.intersect(right)
    }
}

pub struct TrivialOracle;

impl<
    K: Hash + Eq + Copy,
    V: Maximal,
    P: IterSet<Item = (K, K)>,
    I: IterSet<Item = K> + Cartesian<Output = P>,
    S: System<K, V, P, I>,
> LocalOracle<K, V, P, I, S> for TrivialOracle
{
    fn approximate_flow(
        &self,
        _visited: &I,
        _assignment: &impl Assignment<K, V>,
        _possible: &P,
        system: &S,
    ) -> P {
        system.variables().cartesian(&system.variables())
    }
}
