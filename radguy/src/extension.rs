use std::{collections::HashSet, hash::Hash, marker::PhantomData};

use crate::{Assignment, Cartesian, System, Union, Without, oracle::LocalOracle};

pub trait TermToKey<
    VarKey: Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    PairSet,
    VarSet,
    TermSet,
    S: TermSystem<VarKey, VarValue, TermKey, PairSet, VarSet>,
>
{
    fn term_to_key(&self, visited: &VarSet, system: &S) -> PairSet;
}

impl<
    VarKey: Copy + Hash + Eq,
    VarValue: PartialOrd,
    TermKey: Copy + Eq + Hash,
    S: TermSystem<VarKey, VarValue, TermKey, HashSet<(VarKey, VarKey)>, HashSet<VarKey>>,
    H: ::std::hash::BuildHasher + Default,
> TermToKey<VarKey, VarValue, TermKey, HashSet<(VarKey, VarKey)>, HashSet<VarKey>, Self, S>
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

pub trait TermSystem<VarKey: Copy, VarValue: PartialOrd, TermKey: Copy, PairSet, VarSet>:
    System<VarKey, VarValue, PairSet, VarSet>
{
    fn definition(&self, variable: VarKey) -> TermKey;
}

pub trait LocalExtension<
    VarKey: Hash + Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    PairSet,
    VarSet,
    TermSet,
>
{
    type System: TermSystem<VarKey, VarValue, TermKey, PairSet, VarSet>;

    fn depends(
        &self,
        visited: &VarSet,
        assignment: &dyn Assignment<VarKey, VarValue>,
        possible: &PairSet,
        system: &Self::System,
    ) -> TermSet;
}

pub struct ExtensionOracle<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy,
    PS,
    VS,
    TS,
    S: TermSystem<K, V, T, PS, VS>,
    E: LocalExtension<K, V, T, PS, VS, TS, System = S>,
> {
    extension: E,
    _phantom_data: PhantomData<(K, V, T, PS, VS, TS)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    PS: Union + FromIterator<(K, K)>,
    VS: Cartesian<Output = PS> + Without,
    TS: TermToKey<K, V, T, PS, VS, TS, S>,
    S: TermSystem<K, V, T, PS, VS>,
    E: LocalExtension<K, V, T, PS, VS, TS, System = S>,
> LocalOracle<K, V, PS, VS, S> for ExtensionOracle<K, V, T, PS, VS, TS, S, E>
where
    for<'a> &'a VS: IntoIterator<Item = &'a K>,
{
    fn approximate_flow(
        &self,
        visited: &VS,
        assignment: &impl Assignment<K, V>,
        possible: &PS,
        system: &E::System,
    ) -> PS {
        let unvisited = system.variables().without(visited);
        let unvisited_dep = system.variables().cartesian(&unvisited);
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
    PS: FromIterator<(K, K)>,
    VS,
    TS,
    S: TermSystem<K, V, T, PS, VS>,
    E: LocalExtension<K, V, T, PS, VS, TS, System = S>,
> From<E> for ExtensionOracle<K, V, T, PS, VS, TS, S, E>
{
    fn from(extension: E) -> Self {
        Self {
            extension,
            _phantom_data: PhantomData,
        }
    }
}
