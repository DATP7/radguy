use crate::{
    Arguments, Assignment, Bottom, Cartesian, CopiedIter, DependencyGraphSystem, Diagonal,
    FromLefts, FromRights, Intersect, Maximal, PairUniverse, RightSliced, Set, System, Union,
    UnionWith, Universe, Visited, Without,
    arena::{Key, SecondaryArena},
    set::bitset::{BitSet, BitsetRelation},
};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::{collections::HashSet, hash::Hash, marker::PhantomData};

pub trait LocalOracle<K, V: PartialOrd, PS, S: System<K, V>> {
    fn approximate_flow(&self, assignment: &HashMap<K, V>, possible: &PS, system: &S) -> PS;

    #[must_use]
    fn then<O: LocalOracle<K, V, PS, S>>(self, other: O) -> ComposeLocal<K, V, PS, S, O, Self>
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
    fn and<O: LocalOracle<K, V, PS, S>>(self, other: O) -> IntersectLocal<K, V, PS, S, O, Self>
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

#[derive(Default, Clone)]
pub struct LocalMaxR<U>(PhantomData<U>);

impl<
    K: Hash + Eq + Copy + Debug,
    V: Maximal,
    PS: FromIterator<(K, K)>
        + Union
        + Union<HashSet<(K, K)>>
        + RightSliced<K, K, SlicedRight = U>
        + FromRights<U, K>,
    S: System<K, V> + Universe<U> + Visited<U>,
    U: Cartesian<Output = PS> + Without<U> + for<'a> CopiedIter<'a, K> + Diagonal<Output = PS> + Clone,
> LocalOracle<K, V, PS, S> for LocalMaxR<U>
{
    fn approximate_flow(&self, assignment: &HashMap<K, V>, _possible: &PS, system: &S) -> PS {
        let visited = system.visited();
        let unvisited = system.universe().without(&visited);
        let universe = system.universe();
        let unvisited_dep = universe.cartesian(&unvisited);
        let self_dep = visited.diagonal();

        let rights = visited.copied_iter().filter_map(|y| {
            if system.evaluate(y, assignment).is_maximal() {
                None
            } else {
                Some((universe.clone(), y))
            }
        });
        let max_dep = PS::from_rights(rights);

        unvisited_dep.union(self_dep).union(max_dep)
    }
}

#[expect(
    clippy::implicit_hasher,
    reason = "we don't want to specify the hasher everytime we construct LocalMaxR"
)]
impl<K> LocalMaxR<HashSet<K>> {
    #[must_use]
    pub fn hashset() -> Self {
        Self::default()
    }
}

impl<K> LocalMaxR<BitSet<K>> {
    #[must_use]
    pub fn bitset() -> Self {
        Self::default()
    }
}

impl<K, S: ::std::hash::BuildHasher> Display for LocalMaxR<HashSet<K, S>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LocalMaxR:hashset")
    }
}

impl<K> Display for LocalMaxR<BitSet<K>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LocalMaxR:bitset")
    }
}

// having `PS` as a type parameter on `SMax` isn't techinically required, however it allows us to
// specify the output type of it at compile-time.
pub struct SMax<PS>(PhantomData<PS>);

impl<PS> Default for SMax<PS> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

#[expect(
    clippy::implicit_hasher,
    reason = "we don't want to specify the hasher everytime we construct SMax"
)]
impl<VarKey> SMax<HashSet<(VarKey, VarKey)>> {
    #[must_use]
    pub fn hashset() -> Self {
        Self::default()
    }
}

impl<VarKey> SMax<BitsetRelation<VarKey, VarKey>> {
    #[must_use]
    pub fn bitset() -> Self {
        Self::default()
    }
}

impl<PS> Clone for SMax<PS> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<K, S: ::std::hash::BuildHasher> Display for SMax<HashSet<(K, K), S>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SMax:hashset")
    }
}

impl<K> Display for SMax<BitsetRelation<K, K>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SMax:bitset")
    }
}

// TODO: Make this more general than HashSet
impl<
    K: Hash + Eq + Copy + Debug,
    V: Maximal + Bottom + Clone,
    S: System<K, V>,
    PS: for<'a> CopiedIter<'a, (K, K)> + FromIterator<(K, K)>,
> LocalOracle<K, V, PS, S> for SMax<PS>
{
    fn approximate_flow(&self, assignment: &HashMap<K, V>, possible: &PS, _system: &S) -> PS {
        // TODO: currently it's actually faster to just iterate over `system.pair_universe` with
        // the ordered algorithm, because we construct the initial strategy each time.
        // this (hopefully) isn't the case when we start reusing the relation
        possible
            .copied_iter()
            .filter(|(x, y)| {
                !assignment.get_assignment(x).is_maximal()
                    && !assignment.get_assignment(y).is_maximal()
            })
            .collect()
    }
}

pub struct ComposeLocal<
    K,
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
    K,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S>,
    U: LocalOracle<K, V, PairSet, S>,
> LocalOracle<K, V, PairSet, S> for ComposeLocal<K, V, PairSet, S, T, U>
{
    fn approximate_flow(
        &self,
        assignment: &HashMap<K, V>,
        possible: &PairSet,
        system: &S,
    ) -> PairSet {
        let Self { outer, inner, .. } = self;
        outer.approximate_flow(
            assignment,
            &inner.approximate_flow(assignment, possible, system),
            system,
        )
    }
}

impl<
    K,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S> + Display,
    U: LocalOracle<K, V, PairSet, S> + Display,
> Display for ComposeLocal<K, V, PairSet, S, T, U>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ∘ {})", self.outer, self.inner)
    }
}

pub struct IntersectLocal<
    K,
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
    K,
    V: PartialOrd,
    PairSet: Intersect,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S>,
    U: LocalOracle<K, V, PairSet, S>,
> LocalOracle<K, V, PairSet, S> for IntersectLocal<K, V, PairSet, S, T, U>
{
    fn approximate_flow(
        &self,
        assignment: &HashMap<K, V>,
        possible: &PairSet,
        system: &S,
    ) -> PairSet {
        let Self { left, right, .. } = self;
        let left = left.approximate_flow(assignment, possible, system);
        let right = right.approximate_flow(assignment, possible, system);
        left.intersect(&right)
    }
}

impl<
    K,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S> + Display,
    U: LocalOracle<K, V, PairSet, S> + Display,
> Display for IntersectLocal<K, V, PairSet, S, T, U>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ∩ {})", self.left, self.right)
    }
}

// We need to manually implement `Clone` for these oracles, because the derive macro requires that
// all type parameters of the type implement `Clone`, meaning that `S` needs to implement clone,
// even though it isn't part of the actual struct
impl<
    K,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S> + Clone,
    U: LocalOracle<K, V, PairSet, S> + Clone,
> Clone for ComposeLocal<K, V, PairSet, S, T, U>
{
    fn clone(&self) -> Self {
        Self {
            outer: self.outer.clone(),
            inner: self.inner.clone(),
            _phantom_data: self._phantom_data,
        }
    }
}

impl<
    K,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S> + Clone,
    U: LocalOracle<K, V, PairSet, S> + Clone,
> Clone for IntersectLocal<K, V, PairSet, S, T, U>
{
    fn clone(&self) -> Self {
        Self {
            left: self.left.clone(),
            right: self.right.clone(),
            _phantom_data: self._phantom_data,
        }
    }
}

#[derive(Clone, Default)]
pub struct TrivialOracle<PS>(PhantomData<PS>);

#[expect(
    clippy::implicit_hasher,
    reason = "we don't want to specify the hasher everytime we construct TrivialOracle"
)]
impl<K> TrivialOracle<HashSet<(K, K)>> {
    #[must_use]
    pub fn hashset() -> Self {
        Self::default()
    }
}

impl<K> TrivialOracle<BitsetRelation<K, K>> {
    #[must_use]
    pub fn bitset() -> Self {
        Self::default()
    }
}

impl<K: Hash + Eq + Copy, V: Maximal, PairSet, S: System<K, V> + PairUniverse<PairSet>>
    LocalOracle<K, V, PairSet, S> for TrivialOracle<PairSet>
{
    fn approximate_flow(
        &self,
        _assignment: &HashMap<K, V>,
        _possible: &PairSet,
        system: &S,
    ) -> PairSet {
        system.pair_universe()
    }
}

impl<K, S: ::std::hash::BuildHasher> Display for TrivialOracle<HashSet<(K, K), S>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Trivial:hashset")
    }
}
impl<K> Display for TrivialOracle<BitsetRelation<K, K>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Trivial:bitset")
    }
}

#[derive(Clone, Debug)]
pub struct ArgumentsOracle<VarKey, VarSet, PairSet> {
    successors: RefCell<SecondaryArena<VarKey, VarSet>>,
    ancestors: RefCell<SecondaryArena<VarKey, VarSet>>,
    previous_visited: RefCell<VarSet>,
    relation_cache: RefCell<PairSet>,
}

impl<K, VS, PS> Default for ArgumentsOracle<K, VS, PS>
where
    VS: Default,
    PS: Default + RightSliced<K, K, SlicedRight = VS>,
{
    fn default() -> Self {
        Self {
            successors: RefCell::default(),
            ancestors: RefCell::default(),
            previous_visited: RefCell::default(),
            relation_cache: RefCell::default(),
        }
    }
}

#[expect(
    clippy::implicit_hasher,
    reason = "we don't want to specify the hasher everytime we construct SMax"
)]
impl<K: Default + Eq + Hash + Copy> ArgumentsOracle<K, HashSet<K>, HashSet<(K, K)>> {
    #[must_use]
    pub fn hashset() -> Self {
        Self::default()
    }
}

impl<K: Key> ArgumentsOracle<K, BitSet<K>, BitsetRelation<K, K>> {
    #[must_use]
    pub fn bitset() -> Self {
        Self::default()
    }
}

impl<
    K: Key,
    VS: Set<K>
        + for<'a> UnionWith<&'a VS>
        + Without
        + for<'a> CopiedIter<'a, K>
        + From<[K; 1]>
        + FromIterator<K>
        + Default
        + Clone,
    PS: UnionWith + FromLefts<K, VS> + Default + Clone,
> ArgumentsOracle<K, VS, PS>
{
    fn get_updated_closure<S: Arguments<K, HashSet<K>>>(&self, visited: &VS, system: &S) -> PS {
        let mut successors = self.successors.borrow_mut();
        let mut ancestors = self.ancestors.borrow_mut();
        let mut previous_visited = self.previous_visited.take();

        if previous_visited.len() == visited.len() {
            return self.relation_cache.borrow().clone();
        }

        let new_variables: VS = visited.clone().without(&previous_visited);
        let mut updated_ancestors = VS::default();

        let mut to_add = PS::default();
        for variable in new_variables.copied_iter() {
            let args = system.arguments(variable);
            let var_ancestors = ancestors
                .entry(variable)
                .or_insert_with(|| VS::from([variable]))
                .clone();

            let new_successors: VS = args
                .copied_iter()
                .flat_map(|a| {
                    successors
                        .entry(a)
                        .or_insert_with(|| VS::from([a]))
                        .copied_iter()
                        .collect::<Vec<_>>()
                })
                .chain([variable])
                .collect();

            let var_successors = successors.entry(variable).or_default();

            var_successors.union_with(&new_successors);

            // Clone and shadow since we look at the entry again later and don't want to reference
            // the same object
            let var_successors = var_successors.clone();

            // each new variable has its parent's ancestors as ancestors, and itself
            for succ in var_successors.copied_iter() {
                let ancs = ancestors.entry(succ).or_default();
                ancs.union_with(&var_ancestors);
                ancs.insert(succ);
            }

            for ancestor in var_ancestors.copied_iter() {
                if ancestor == variable {
                    continue;
                }
                // TODO: we don't actually need to update the weight of `ancestor` if extending its
                // successors added nothing
                successors
                    .get_mut(ancestor)
                    .expect("ancestor must have successors")
                    .union_with(&var_successors);
            }

            // TODO: this is probably very inefficient
            let anc_rel = successors
                .get(variable)
                .expect("variable should have successors")
                .copied_iter()
                .map(|arg| {
                    (
                        arg,
                        ancestors
                            .get(arg)
                            .expect("argument should have ancestors")
                            .clone(),
                    )
                });
            let anc_rel = PS::from_lefts(anc_rel);
            to_add.union_with(anc_rel);
            updated_ancestors.union_with(&var_ancestors);
        }

        let mut relation = self.relation_cache.borrow_mut();
        relation.union_with(to_add);

        previous_visited.union_with(&new_variables);
        self.previous_visited.replace(previous_visited);

        relation.clone()
    }
}

// TODO: Make this generic on set/strategy implementation
impl<
    K: Key,
    V: PartialOrd,
    VS: Set<K>
        + for<'a> UnionWith<&'a VS>
        + Without
        + for<'a> CopiedIter<'a, K>
        + From<[K; 1]>
        + FromIterator<K>
        + Default
        + Clone,
    PS: UnionWith + FromLefts<K, VS> + Default + Clone,
    S: System<K, V> + Arguments<K, HashSet<K>> + Visited<VS>,
> LocalOracle<K, V, PS, S> for ArgumentsOracle<K, VS, PS>
{
    fn approximate_flow(&self, _assignment: &HashMap<K, V>, _relation: &PS, system: &S) -> PS {
        let visited = system.visited();
        self.get_updated_closure(&visited, system)
    }
}

impl<VarKey, VarSet, S: ::std::hash::BuildHasher> Display
    for ArgumentsOracle<VarKey, VarSet, HashSet<(VarKey, VarKey), S>>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Args:hashset")
    }
}

impl<VarKey, VarSet> Display for ArgumentsOracle<VarKey, VarSet, BitsetRelation<VarKey, VarKey>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Args:bitset")
    }
}

#[derive(Default)]
pub struct IdentityOracle<PS>(PhantomData<PS>);

#[expect(
    clippy::implicit_hasher,
    reason = "we don't want to specify the hasher everytime we construct TrivialOracle"
)]
impl<K> IdentityOracle<HashSet<(K, K)>> {
    #[must_use]
    pub fn hashset() -> Self {
        Self::default()
    }
}

impl<K> IdentityOracle<BitsetRelation<K, K>> {
    #[must_use]
    pub fn bitset() -> Self {
        Self::default()
    }
}

impl<K: Hash + Eq + Copy, V: Maximal, PairSet: Clone, S: System<K, V> + PairUniverse<PairSet>>
    LocalOracle<K, V, PairSet, S> for IdentityOracle<PairSet>
{
    fn approximate_flow(
        &self,
        _assignment: &HashMap<K, V>,
        possible: &PairSet,
        _system: &S,
    ) -> PairSet {
        possible.clone()
    }
}

impl<K, S: ::std::hash::BuildHasher> Display for IdentityOracle<HashSet<(K, K), S>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Identity:hashset")
    }
}
impl<K> Display for IdentityOracle<BitsetRelation<K, K>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Identity:bitset")
    }
}

#[derive(Default, Clone)]
pub struct WeightedDepOracle<PS>(PhantomData<PS>);

#[expect(clippy::implicit_hasher)]
impl<K> WeightedDepOracle<HashSet<(K, K)>> {
    #[must_use]
    pub const fn hashset() -> Self {
        Self(PhantomData)
    }
}

impl<K> WeightedDepOracle<BitsetRelation<K, K>> {
    #[must_use]
    pub const fn bitset() -> Self {
        Self(PhantomData)
    }
}

impl<
    K: Hash + Eq + Copy,
    V: Maximal + Ord + Bottom + Clone,
    VS: for<'a> CopiedIter<'a, K>,
    PS: Set<(K, K)>
        + FromIterator<(K, K)>
        + for<'a> CopiedIter<'a, (K, K)>
        + RightSliced<K, K, SlicedRight = VS>,
    S: System<K, V> + DependencyGraphSystem<K, (K, V)> + Universe<VS>,
> LocalOracle<K, V, PS, S> for WeightedDepOracle<PS>
{
    fn approximate_flow(&self, assignment: &HashMap<K, V>, possible: &PS, system: &S) -> PS {
        let universe = system.universe();
        possible
            .copied_iter()
            .filter(|(x, y)| {
                if x == y {
                    return true;
                }
                let Some(hyperedges) = system.get_hyperedges(*y) else {
                    return true;
                };
                if universe
                    .copied_iter()
                    .any(|z| possible.contains(&(*x, z)) && possible.contains(&(z, *y)))
                {
                    return true;
                }

                hyperedges.into_iter().any(|targets| {
                    targets.iter().any(|(z, _)| z == x)
                        && targets
                            .into_iter()
                            .all(|(_, w)| w < assignment.get_assignment(y))
                })
            })
            .collect()
    }
}

impl<K, S: ::std::hash::BuildHasher> Display for WeightedDepOracle<HashSet<(K, K), S>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "WeightedDep:hashset")
    }
}

impl<K> Display for WeightedDepOracle<BitsetRelation<K, K>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "WeightedDep:bitset")
    }
}

/// This test module is copy paste from [`StrategicArgumentsOracle`], with weights removed
#[cfg(test)]
mod tests {
    mod arguments {
        use crate::{CopiedIter, UnionWith, set::bitset::BitSet};
        use std::collections::HashSet;

        use crate::{Arguments, arena::Arena, oracle::ArgumentsOracle};

        #[derive(Default, Debug)]
        struct MockSystem {
            variables: Arena<usize, HashSet<usize>>,
        }

        impl MockSystem {
            fn add_variable(&mut self) -> usize {
                self.variables.insert(HashSet::new())
            }

            fn set_arguments(&mut self, variable: usize, arguments: HashSet<usize>) {
                *self.variables.get_mut(variable) = arguments;
            }
        }

        impl Arguments<usize, HashSet<usize>> for MockSystem {
            fn arguments(&self, key: usize) -> HashSet<usize> {
                self.variables.get(key).clone()
            }
        }

        impl Arguments<usize, BitSet<usize>> for MockSystem {
            fn arguments(&self, key: usize) -> BitSet<usize> {
                self.variables.get(key).copied_iter().collect()
            }
        }

        macro_rules! system_def {
            ($($name:ident = {$($dep:ident),* $(,)?};)*) => {
                {
                    let mut system = MockSystem::default();
                    $(
                        let $name = system.add_variable();
                    )*
                    $(
                        system.set_arguments($name, HashSet::from([$($dep,)*]));
                    )*
                    (system, [$($name,)*])
                }
            };
        }

        macro_rules! test_arguments {
            ($(
                $test_name:ident: {
                    with {$(
                        $var_name:ident = {$($dep:ident),* $(,)?};
                    )*};
                    $(
                        $(
                        visit {$($visited_var:ident),* $(,)?} => {$(($l:ident, $r:ident)),* $(,)?};
                        )+
                        reset;
                    )*
                };
            )*) => {
                $(
                    mod $test_name {
                        use super::*;
                        use std::collections::HashSet;
                        use $crate::{Set, set::bitset::{BitSet, BitsetRelation}};

                        #[test]
                        fn hashset() {
                            let (system, [$($var_name,)*]) = system_def! {$(
                                $var_name = {$($dep,)*};
                            )*};
                            $(
                            let oracle = ArgumentsOracle::<_, HashSet<_>, HashSet<_>>::default();
                            assert!(
                                oracle.relation_cache.borrow().is_empty(),
                                "strategy should start empty"
                            );

                            let mut visited = HashSet::new();
                            let mut visit_seq = Vec::new();
                            $(
                                visited.extend(HashSet::from([$($visited_var,)*]));
                                visit_seq.push(stringify!($($visited_var),*));
                                let expected = HashSet::from([$(($l, $r),)*]);
                                let got = oracle.get_updated_closure(&visited, &system);

                                assert_eq!(
                                    expected,
                                    got,
                                    "wrong strategy when visiting {{{}}}. sequence: {visit_seq:#?} state: {oracle:#?}", stringify!($($visited_var),*)
                                );
                            )+
                            )*
                        }

                        #[test]
                        fn bitset() {
                            let (system, [$($var_name,)*]) = system_def! {$(
                                $var_name = {$($dep,)*};
                            )*};
                            $(
                            let oracle = ArgumentsOracle::<_, BitSet<_>, BitsetRelation<_, _>>::default();
                            assert!(
                                oracle.relation_cache.borrow().is_empty(),
                                "strategy should start empty"
                            );

                            let mut visited = BitSet::new();
                            let mut visit_seq = Vec::new();
                            $(
                                visited.union_with(BitSet::from([$($visited_var,)*]));
                                visit_seq.push(stringify!($($visited_var),*));
                                let expected = BitsetRelation::from_iter([$(($l, $r),)*]);
                                let got = oracle.get_updated_closure(&visited, &system);

                                assert_eq!(
                                    expected,
                                    got,
                                    "wrong strategy when visiting {{{}}}. sequence: {visit_seq:#?} state: {oracle:#?}", stringify!($($visited_var),*)
                                );
                            )+
                            )*
                        }
                    }
                )*
            };
        }

        test_arguments! {
            single_variable: {
                with {
                    x = {};
                };
                visit {x} => {(x, x)};
                reset;
            };
            direct_cycle: {
                with {
                    x = {x};
                };
                visit {x} => {(x, x)};
                reset;
            };
            chain: {
                with {
                    x = {y};
                    y = {z};
                    z = {};
                };
                visit {x} => {(x, x), (y, x), (y, y)};
                visit {y} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                visit {z} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
                visit {z} => {(z, z)};
                visit {y} => {(z, z), (y, y), (z, y)};
                visit {x} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
                visit {x} => {(x, x), (y, x), (y, y)};
                visit {z} => {(x, x), (y, x), (y, y), (z, z)};
                visit {y} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
                visit {x, z} => {(x, x), (y, x), (y, y), (z, z)};
                visit {y} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
                visit {z, y} => {(z, z), (y, y), (z, y)};
                visit {x} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
                visit {y, x} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                visit {z} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
            };
            multiple_arguments: {
                with {
                    x = {y, z};
                    y = {};
                    z = {};
                };
                visit {x} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                visit {y} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                visit {z} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                reset;
                visit {x} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                visit {y, z} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                reset;
                visit {x, y} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                visit {z} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                reset;
            };
            existing_children: {
                with {
                    x = {y, z};
                    y = {z};
                    z = {};
                };
                visit {x} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                visit {y} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                visit {z} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
            };
            four_cycle: {
                with {
                    x = {y};
                    y = {z};
                    z = {w};
                    w = {x};
                };
                visit {x} => {(x, x), (y, y), (y, x)};
                visit {y} => {(x, x), (y, y), (y, x), (z, z), (z, y), (z, x)};
                visit {z} => {(x, x), (y, y), (y, x), (z, z), (z, y), (z, x), (w, w), (w, x), (w, y), (w, z)};
                visit {w} => {
                    (x, x), (x, y), (x, z), (x, w),
                    (y, x), (y, y), (y, z), (y, w),
                    (z, x), (z, y), (z, z), (z, w),
                    (w, x), (w, y), (w, z), (w, w),
                };
                reset;
                visit {x} => {(x, x), (y, y), (y, x)};
                visit {z} => {(x, x), (y, y), (y, x), (z, z), (w, z), (w, w)};
                visit {y} => {
                    (x, x),
                    (y, x), (y, y),
                    (z, x), (z, y), (z, z),
                    (w, x), (w, y), (w, z), (w, w),
                };
                visit {w} => {
                    (x, x), (x, y), (x, z), (x, w),
                    (y, x), (y, y), (y, z), (y, w),
                    (z, x), (z, y), (z, z), (z, w),
                    (w, x), (w, y), (w, z), (w, w),
                };
                reset;
            };
            four_cycle_with_center: {
                with {
                    x = {y};
                    y = {z, u};
                    z = {w, u};
                    w = {x};
                    u = {x, w};
                };
                visit {x} => {(x, x), (y, y), (y, x)};
                visit {y} => {
                    (x, x),
                    (y, x), (y, y),
                    (z, x), (z, y), (z, z),
                    (u, x), (u, y), (u, u)
                };
                visit {u} => {
                    (x, x), (x, y),              (x, u),
                    (y, x), (y, y),              (y, u),
                    (z, x), (z, y), (z, z), (z, u),
                    (u, x), (u, y),              (u, u),
                    (w, x), (w, y),              (w, u), (w, w),
                };
                visit {w} => {
                    (x, x), (x, y),              (x, u), (x, w),
                    (y, x), (y, y),              (y, u), (y, w),
                    (z, x), (z, y), (z, z), (z, u), (z, w),
                    (u, x), (u, y),              (u, u), (u, w),
                    (w, x), (w, y),              (w, u), (w, w),
                };
                visit {z} => {
                    (x, x), (x, y), (x, z), (x, u), (x, w),
                    (y, x), (y, y), (y, z), (y, u), (y, w),
                    (z, x), (z, y), (z, z), (z, u), (z, w),
                    (u, x), (u, y), (u, z), (u, u), (u, w),
                    (w, x), (w, y), (w, z), (w, u), (w, w),
                };
                reset;
            };
            discover_into_existing_chain: {
                with {
                    a = {b, d};
                    b = {c};
                    c = {};
                    d = {e};
                    e = {b};
                };
                visit {a} => {(a, a), (b, a), (b, b), (d, a), (d, d)};
                visit {b} => {(a, a), (b, a), (b, b), (c, c), (c, b), (c, a), (d, a), (d, d)};
                visit {c} => {(a, a), (b, a), (b, b), (c, c), (c, b), (c, a), (d, a), (d, d)};
                visit {d} => {(a, a), (b, a), (b, b), (c, c), (c, b), (c, a), (d, a), (d, d), (e, a), (e, d), (e, e)};
                visit {e} => {
                    (a, a),
                    (b, a), (b, b),              (b, d), (b, e),
                    (c, a), (c, b), (c, c), (c, d), (c, e),
                    (d, a),                           (d, d),
                    (e, a),                           (e, d), (e, e),
                };
                reset;
            };
            ancestors_updated: {
                with {
                    a = {b, c};
                    b = {d, e};
                    c = {d};
                    d = {e};
                    e = {f};
                    f = {};
                };
                visit {a} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                };
                visit {b} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                    (d, a), (d, b),              (d, d),
                    (e, a), (e, b),                           (e, e),
                };
                visit {c} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                    (d, a), (d, b), (d, c), (d, d),
                    (e, a), (e, b),                           (e, e),
                };
                visit {d} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                    (d, a), (d, b), (d, c), (d, d),
                    (e, a), (e, b), (e, c), (e, d), (e, e),
                };
                visit {e} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                    (d, a), (d, b), (d, c), (d, d),
                    (e, a), (e, b), (e, c), (e, d), (e, e),
                    (f, a), (f, b), (f, c), (f, d), (f, e), (f, f),
                };
                visit {f} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                    (d, a), (d, b), (d, c), (d, d),
                    (e, a), (e, b), (e, c), (e, d), (e, e),
                    (f, a), (f, b), (f, c), (f, d), (f, e), (f, f),
                };
                reset;
            };
        }
    }
}
