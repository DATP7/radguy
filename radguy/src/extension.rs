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

pub trait LocalExtension<
    VarKey: Hash + Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    PairSet,
    System: TermSystem<VarKey, VarValue, TermKey>,
>
{
    fn depends(
        &self,
        term: TermKey,
        visited: &HashSet<VarKey>,
        assignment: &HashMap<VarKey, VarValue>,
        possible: &PairSet,
        system: &System,
    ) -> HashSet<VarKey>;

    #[must_use]
    fn oracle() -> ExtensionOracle<VarKey, VarValue, TermKey, PairSet, System, Self>
    where
        Self: Default,
        VarKey: Hash + Eq + Copy,
        VarValue: PartialOrd,
        TermKey: Copy + Eq,
        PairSet: Union + FromIterator<(VarKey, VarKey)>,
        System: Universe<HashSet<VarKey>>,
    {
        ExtensionOracle::from(Self::default())
    }
}

#[derive(Debug)]
pub struct ExtensionOracle<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy,
    PS,
    S: TermSystem<K, V, T>,
    E: LocalExtension<K, V, T, PS, S>,
> {
    extension: E,
    _phantom_data: PhantomData<(K, V, T, PS, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    PS: Union + Union<HashSet<(K, K)>> + FromIterator<(K, K)>,
    S: TermSystem<K, V, T> + Universe<HashSet<K>>,
    E: LocalExtension<K, V, T, PS, S>,
> LocalOracle<K, V, PS, S> for ExtensionOracle<K, V, T, PS, S, E>
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
        let term_dep: PS = visited
            .iter()
            .flat_map(|var| {
                self.extension
                    .depends(
                        system.definition(*var),
                        visited,
                        assignment,
                        possible,
                        system,
                    )
                    .into_iter()
                    .map(|dep| (dep, *var))
            })
            .collect();

        self_dep.union(unvisited_dep).union(term_dep)
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    PS: Union + FromIterator<(K, K)>,
    S: TermSystem<K, V, T> + Universe<HashSet<K>>,
    E: LocalExtension<K, V, T, PS, S>,
> From<E> for ExtensionOracle<K, V, T, PS, S, E>
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
    T: Copy,
    PS,
    S: TermSystem<K, V, T>,
    E: LocalExtension<K, V, T, PS, S> + Clone,
> Clone for ExtensionOracle<K, V, T, PS, S, E>
{
    fn clone(&self) -> Self {
        Self {
            extension: self.extension.clone(),
            _phantom_data: PhantomData,
        }
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    PS: Union + FromIterator<(K, K)>,
    S: TermSystem<K, V, T> + Universe<HashSet<K>>,
    E: LocalExtension<K, V, T, PS, S> + Display,
> Display for ExtensionOracle<K, V, T, PS, S, E>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "E^({})", self.extension)
    }
}
