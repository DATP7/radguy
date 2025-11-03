use crate::{
    Assignment, Cartesian, Diagonal, Intersect, Maximal, PairUniverse, Set, System, Union,
    Universe, Without,
};
use std::fmt::Debug;
use std::{collections::HashSet, hash::Hash, marker::PhantomData};

pub trait LocalOracle<K: Hash + Eq + Copy, V: PartialOrd, VS, PS, S: System<K, V>> {
    fn approximate_flow(
        &self,
        visited: &VS,
        assignment: &impl Assignment<K, V>,
        possible: &PS,
        system: &S,
    ) -> PS;

    #[must_use]
    fn then(self, other: impl LocalOracle<K, V, VS, PS, S>) -> impl LocalOracle<K, V, VS, PS, S>
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
    fn and(self, other: impl LocalOracle<K, V, VS, PS, S>) -> impl LocalOracle<K, V, VS, PS, S>
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

impl<K, S: ::std::hash::BuildHasher> LocalMaxR<HashSet<K, S>> {
    #[must_use]
    pub const fn hash() -> Self {
        Self(PhantomData)
    }
}

impl<
    K: Hash + Eq + Copy + Debug,
    V: Maximal,
    VS: Set<K> + Diagonal<Output = PS>,
    PS: FromIterator<(K, K)> + Union,
    S: System<K, V> + Universe<U>,
    U: Cartesian<Output = PS> + Without<VS>,
> LocalOracle<K, V, VS, PS, S> for LocalMaxR<U>
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

impl<K, S: ::std::hash::BuildHasher> SMax<HashSet<(K, K), S>> {
    #[must_use]
    pub const fn hash() -> Self {
        Self(PhantomData)
    }
}

// TODO: Make this more general than HashSet
impl<
    K: Hash + Eq + Copy,
    V: Maximal,
    S: System<K, V> + PairUniverse<U>,
    U: IntoIterator<Item = (K, K)>,
> LocalOracle<K, V, HashSet<K>, HashSet<(K, K)>, S> for SMax<U>
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
    VarSet,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, VarSet, PairSet, S>,
    U: LocalOracle<K, V, VarSet, PairSet, S>,
> {
    outer: T,
    inner: U,
    _phantom_data: PhantomData<(K, V, VarSet, PairSet, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    VarSet,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, VarSet, PairSet, S>,
    U: LocalOracle<K, V, VarSet, PairSet, S>,
> LocalOracle<K, V, VarSet, PairSet, S> for ComposeLocal<K, V, VarSet, PairSet, S, T, U>
{
    fn approximate_flow(
        &self,
        visited: &VarSet,
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
    VarSet,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, VarSet, PairSet, S>,
    U: LocalOracle<K, V, VarSet, PairSet, S>,
> {
    left: T,
    right: U,
    _phantom_data: PhantomData<(K, V, VarSet, PairSet, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    VarSet,
    PairSet: Intersect,
    S: System<K, V>,
    T: LocalOracle<K, V, VarSet, PairSet, S>,
    U: LocalOracle<K, V, VarSet, PairSet, S>,
> LocalOracle<K, V, VarSet, PairSet, S> for IntersectLocal<K, V, VarSet, PairSet, S, T, U>
{
    fn approximate_flow(
        &self,
        visited: &VarSet,
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

impl<
    K: Hash + Eq + Copy,
    V: Maximal,
    VarSet: Cartesian<Output = PairSet>,
    PairSet,
    S: System<K, V> + PairUniverse<PairSet>,
> LocalOracle<K, V, VarSet, PairSet, S> for TrivialOracle
{
    fn approximate_flow(
        &self,
        _visited: &VarSet,
        _assignment: &impl Assignment<K, V>,
        _possible: &PairSet,
        system: &S,
    ) -> PairSet {
        system.pair_universe()
    }
}
