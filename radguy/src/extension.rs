use std::{collections::HashSet, fmt::Display, hash::Hash, marker::PhantomData};

use crate::{Assignment, Cartesian, System, Union, Universe, Without, oracle::LocalOracle};

pub trait TermSystem<VarKey: Copy, VarValue: PartialOrd, TermKey: Copy>:
    System<VarKey, VarValue>
{
    fn definition(&self, variable: VarKey) -> TermKey;
}

pub trait TermToKey<
    VarKey: Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    VarSet,
    PairSet,
    S: TermSystem<VarKey, VarValue, TermKey>,
>
{
    fn term_to_key(&self, visited: &VarSet, system: &S) -> PairSet;
}

impl<
    VarKey: Copy + Hash + Eq,
    VarValue: PartialOrd,
    TermKey: Copy + Eq + Hash,
    S: TermSystem<VarKey, VarValue, TermKey>,
    H: ::std::hash::BuildHasher + Default,
> TermToKey<VarKey, VarValue, TermKey, HashSet<VarKey>, HashSet<(VarKey, VarKey)>, S>
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
    VarSet,
    PairSet,
    TermSet,
    System: TermSystem<VarKey, VarValue, TermKey>,
>
{
    fn depends(
        &self,
        visited: &VarSet,
        assignment: &dyn Assignment<VarKey, VarValue>,
        possible: &PairSet,
        system: &System,
    ) -> TermSet;
}

pub trait ExtensionToOracle<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    VS: Cartesian<Output = PS> + Without,
    PS: Union + FromIterator<(K, K)>,
    TS: TermToKey<K, V, T, VS, PS, S>,
    S: TermSystem<K, V, T> + Universe<U>,
    U: Without<VS> + Cartesian<Output = PS>,
>: LocalExtension<K, V, T, VS, PS, TS, S> + Default
{
    #[must_use]
    fn oracle() -> ExtensionOracle<K, V, T, VS, PS, TS, S, Self, U> {
        ExtensionOracle::from(Self::default())
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    VS: Cartesian<Output = PS> + Without,
    PS: Union + FromIterator<(K, K)>,
    TS: TermToKey<K, V, T, VS, PS, S>,
    S: TermSystem<K, V, T> + Universe<U>,
    U: Without<VS> + Cartesian<Output = PS>,
    E: LocalExtension<K, V, T, VS, PS, TS, S> + Default,
> ExtensionToOracle<K, V, T, VS, PS, TS, S, U> for E
{
}

#[allow(clippy::type_complexity)]
pub struct ExtensionOracle<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy,
    VS,
    PS,
    TS,
    S: TermSystem<K, V, T>,
    E: LocalExtension<K, V, T, VS, PS, TS, S>,
    U,
> {
    extension: E,
    _phantom_data: PhantomData<(K, V, T, VS, PS, TS, S, U)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    VS: Cartesian<Output = PS> + Without,
    PS: Union + FromIterator<(K, K)>,
    TS: TermToKey<K, V, T, VS, PS, S>,
    S: TermSystem<K, V, T> + Universe<U>,
    E: LocalExtension<K, V, T, VS, PS, TS, S>,
    U: Without<VS> + Cartesian<Output = PS>,
> LocalOracle<K, V, VS, PS, S> for ExtensionOracle<K, V, T, VS, PS, TS, S, E, U>
where
    for<'a> &'a VS: IntoIterator<Item = &'a K>,
{
    fn approximate_flow(
        &self,
        visited: &VS,
        assignment: &impl Assignment<K, V>,
        possible: &PS,
        system: &S,
    ) -> PS {
        let unvisited = system.universe().without(visited);
        let unvisited_dep = system.universe().cartesian(&unvisited);
        let self_dep: PS = visited.into_iter().map(|&x| (x, x)).collect();
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
    VS: Cartesian<Output = PS> + Without,
    PS: Union + FromIterator<(K, K)>,
    TS: TermToKey<K, V, T, VS, PS, S>,
    S: TermSystem<K, V, T> + Universe<U>,
    E: LocalExtension<K, V, T, VS, PS, TS, S>,
    U: Without<VS> + Cartesian<Output = PS>,
> From<E> for ExtensionOracle<K, V, T, VS, PS, TS, S, E, U>
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
    VS: Cartesian<Output = PS> + Without,
    PS: Union + FromIterator<(K, K)>,
    TS: TermToKey<K, V, T, VS, PS, S>,
    S: TermSystem<K, V, T> + Universe<U>,
    E: LocalExtension<K, V, T, VS, PS, TS, S> + Display,
    U: Without<VS> + Cartesian<Output = PS>,
> Display for ExtensionOracle<K, V, T, VS, PS, TS, S, E, U>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "E^({})", self.extension)
    }
}
