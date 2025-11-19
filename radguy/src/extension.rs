use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
    marker::PhantomData,
};

use crate::{Cartesian, System, Union, Universe, Without, oracle::LocalOracle};

pub trait TermSystem<VarKey: Copy, VarValue: PartialOrd, TermKey: Copy>:
    System<VarKey, VarValue>
{
    fn definition(&self, variable: VarKey) -> TermKey;
}

pub trait TermToKey<
    VarKey: Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    PairSet,
    S: TermSystem<VarKey, VarValue, TermKey>,
>
{
    fn term_to_key(&self, visited: &HashSet<VarKey>, system: &S) -> PairSet;
}

impl<
    VarKey: Copy + Hash + Eq,
    VarValue: PartialOrd,
    TermKey: Copy + Eq + Hash,
    S: TermSystem<VarKey, VarValue, TermKey>,
    H: ::std::hash::BuildHasher + Default,
> TermToKey<VarKey, VarValue, TermKey, HashSet<(VarKey, VarKey)>, S>
    for HashSet<(VarKey, TermKey), H>
{
    fn term_to_key(&self, visited: &HashSet<VarKey>, system: &S) -> HashSet<(VarKey, VarKey)> {
        visited
            .iter()
            .flat_map(|&y| {
                self.iter()
                    .filter_map(|(x, ty)| {
                        if system.definition(y) == *ty {
                            Some((*x, y))
                        } else {
                            None
                        }
                    })
                    .collect::<HashSet<(VarKey, VarKey)>>()
            })
            .collect()
    }
}

pub trait LocalExtension<
    VarKey: Hash + Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    PairSet,
    TermSet,
    System: TermSystem<VarKey, VarValue, TermKey>,
>
{
    fn depends(
        &self,
        visited: &HashSet<VarKey>,
        assignment: &HashMap<VarKey, VarValue>,
        possible: &PairSet,
        system: &System,
    ) -> TermSet;

    #[must_use]
    fn oracle() -> ExtensionOracle<VarKey, VarValue, TermKey, PairSet, TermSet, System, Self>
    where
        Self: Default,
        VarKey: Hash + Eq + Copy,
        VarValue: PartialOrd,
        TermKey: Copy + Eq,
        PairSet: Union + FromIterator<(VarKey, VarKey)>,
        TermSet: TermToKey<VarKey, VarValue, TermKey, PairSet, System>,
        System: Universe<HashSet<VarKey>>,
    {
        ExtensionOracle::from(Self::default())
    }
}

pub struct ExtensionOracle<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy,
    PS,
    TS,
    S: TermSystem<K, V, T>,
    E: LocalExtension<K, V, T, PS, TS, S>,
> {
    extension: E,
    _phantom_data: PhantomData<(K, V, T, PS, TS, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    PS: Union + Union<HashSet<(K, K)>> + FromIterator<(K, K)>,
    TS: TermToKey<K, V, T, PS, S>,
    S: TermSystem<K, V, T> + Universe<HashSet<K>>,
    E: LocalExtension<K, V, T, PS, TS, S>,
> LocalOracle<K, V, PS, S> for ExtensionOracle<K, V, T, PS, TS, S, E>
{
    fn approximate_flow(
        &self,
        visited: &HashSet<K>,
        assignment: &HashMap<K, V>,
        possible: &PS,
        system: &S,
    ) -> PS {
        let unvisited = system.universe().without(visited);
        let unvisited_dep = system.universe().cartesian(&unvisited);
        let self_dep: PS = visited.iter().map(|&x| (x, x)).collect();
        let terms = self
            .extension
            .depends(visited, assignment, possible, system);
        let term_dep = terms.term_to_key(visited, system);

        self_dep.union(unvisited_dep).union(term_dep)
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    PS: Union + FromIterator<(K, K)>,
    TS: TermToKey<K, V, T, PS, S>,
    S: TermSystem<K, V, T> + Universe<HashSet<K>>,
    E: LocalExtension<K, V, T, PS, TS, S>,
> From<E> for ExtensionOracle<K, V, T, PS, TS, S, E>
{
    fn from(extension: E) -> Self {
        Self {
            extension,
            _phantom_data: PhantomData,
        }
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    PS: Union + FromIterator<(K, K)>,
    TS: TermToKey<K, V, T, PS, S>,
    S: TermSystem<K, V, T> + Universe<HashSet<K>>,
    E: LocalExtension<K, V, T, PS, TS, S> + Display,
> Display for ExtensionOracle<K, V, T, PS, TS, S, E>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "E^({})", self.extension)
    }
}
