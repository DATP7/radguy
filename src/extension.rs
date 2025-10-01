use std::{hash::Hash, marker::PhantomData};

use crate::{Assignment, Cartesian, IterSet, System, oracle::LocalOracle};

pub trait TermToKey<
    VarKey: Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    PairSet: IterSet<Item = (VarKey, VarKey)>,
    VarSet: IterSet<Item = VarKey>,
    TermSet: IterSet<Item = (VarKey, TermKey)>,
    S: TermSystem<VarKey, VarValue, TermKey, PairSet, VarSet>,
>
{
    fn term_to_key(&self, visited: &VarSet, system: &S) -> PairSet;
}

pub trait TermSystem<
    VarKey: Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    PairSet: IterSet<Item = (VarKey, VarKey)>,
    VarSet: IterSet<Item = VarKey>,
>: System<VarKey, VarValue, PairSet, VarSet>
{
    fn definition(&self, variable: VarKey) -> TermKey;
}

pub trait LocalExtension<
    VarKey: Hash + Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    PairSet: IterSet<Item = (VarKey, VarKey)>,
    VarSet: IterSet<Item = VarKey>,
    TermSet: IterSet<Item = (VarKey, TermKey)>,
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
    PS: IterSet<Item = (K, K)>,
    VS: IterSet<Item = K>,
    TS: IterSet<Item = (K, T)>,
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
    PS: IterSet<Item = (K, K)> + FromIterator<(K, K)>,
    VS: IterSet<Item = K> + Cartesian<Output = PS>,
    TS: IterSet<Item = (K, T)> + TermToKey<K, V, T, PS, VS, TS, S>,
    S: TermSystem<K, V, T, PS, VS>,
    E: LocalExtension<K, V, T, PS, VS, TS, System = S>,
> LocalOracle<K, V, PS, VS, S> for ExtensionOracle<K, V, T, PS, VS, TS, S, E>
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
    PS: IterSet<Item = (K, K)> + FromIterator<(K, K)>,
    VS: IterSet<Item = K>,
    TS: IterSet<Item = (K, T)>,
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
