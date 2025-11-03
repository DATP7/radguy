use crate::{
    Assignment, Cartesian, Diagonal, Intersect, Maximal, Set, System, Union, Universe, Without,
};
use std::fmt::Debug;
use std::{collections::HashSet, hash::Hash, marker::PhantomData};

pub trait LocalOracle<K: Hash + Eq + Copy, V: PartialOrd, PS, VS, S: System<K, V, PS, VS>> {
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
pub struct LocalMaxR<U>(PhantomData<U>);

impl<
    K: Hash + Eq + Copy + Debug,
    V: Maximal,
    PS: FromIterator<(K, K)> + Union,
    VS: Set<K> + Diagonal<Output = PS>,
    S: System<K, V, PS, VS> + Universe<U>,
    U: Cartesian<Output = PS> + Without<VS>,
> LocalOracle<K, V, PS, VS, S> for LocalMaxR<U>
where
    for<'a> &'a VS: IntoIterator<Item = &'a K>,
    for<'a> &'a U: IntoIterator<Item = &'a K>,
{
    fn approximate_flow(
        &self,
        visited: &VS,
        assignment: &impl Assignment<K, V>,
        _possible: &PS,
        system: &S,
    ) -> PS {
        let unvisited = system.universe().without(visited);
        let universe = system.universe();
        let unvisited_dep = universe.cartesian(&unvisited);
        let self_dep = visited.diagonal();

        // Alternative version
        let max_dep = visited
            .into_iter()
            .flat_map(|&y| {
                if system.evaluate(y, assignment).is_maximal() {
                    std::iter::empty().collect::<Vec<_>>()
                } else {
                    universe.into_iter().map(|&x| (x, y)).collect()
                }
            })
            .collect();

        unvisited_dep.union(self_dep).union(max_dep)
    }
}

#[derive(Default)]
pub struct SMax<U>(PhantomData<U>);

impl<
    K: Hash + Eq + Copy,
    V: Maximal,
    S: System<K, V, HashSet<(K, K)>, HashSet<K>> + Universe<U>,
    U: Cartesian<Output = HashSet<(K, K)>>,
> LocalOracle<K, V, HashSet<(K, K)>, HashSet<K>, S> for SMax<U>
{
    fn approximate_flow(
        &self,
        _visited: &HashSet<K>,
        assignment: &impl Assignment<K, V>,
        _possible: &HashSet<(K, K)>,
        system: &S,
    ) -> HashSet<(K, K)> {
        let variables = system.universe();
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
    P,
    I,
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
    P,
    I,
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
    P,
    I,
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
    P: Intersect,
    I,
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
        left.intersect(&right)
    }
}

#[derive(Default)]
pub struct TrivialOracle<U>(PhantomData<U>);

impl<
    K: Hash + Eq + Copy,
    V: Maximal,
    P,
    I: Cartesian<Output = P>,
    S: System<K, V, P, I> + Universe<U>,
    U: Cartesian<Output = P>,
> LocalOracle<K, V, P, I, S> for TrivialOracle<U>
{
    fn approximate_flow(
        &self,
        _visited: &I,
        _assignment: &impl Assignment<K, V>,
        _possible: &P,
        system: &S,
    ) -> P {
        let universe = system.universe();
        universe.cartesian(&universe)
    }
}
