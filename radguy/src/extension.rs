use std::{
    cmp::PartialOrd,
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
};

use crate::{
    Cartesian, CopiedIter, Diagonal, FromRights, System, Union, Universe, Visited, Without,
    oracle::LocalOracle,
};

pub trait TermSystem<VarKey: Copy, VarValue: PartialOrd, TermKey: Copy>:
    System<VarKey, VarValue>
{
    fn definition(&self, variable: VarKey) -> TermKey;
}

pub trait LocalExtension<
    VarKey: Hash + Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    VarSet,
    PairSet,
    System: TermSystem<VarKey, VarValue, TermKey>,
>
{
    fn depends(
        &self,
        term: TermKey,
        assignment: &HashMap<VarKey, VarValue>,
        possible: &PairSet,
        system: &System,
    ) -> VarSet;

    #[must_use]
    fn oracle() -> ExtensionOracle<VarKey, VarValue, TermKey, VarSet, PairSet, System, Self>
    where
        Self: Default,
        VarKey: Hash + Eq + Copy,
        VarValue: PartialOrd,
        TermKey: Copy + Eq,
        VarSet: Without
            + Cartesian<Output = PairSet>
            + Diagonal<Output = PairSet>
            + for<'a> CopiedIter<'a, VarKey>,
        PairSet: Union + FromIterator<(VarKey, VarKey)>,
    {
        ExtensionOracle::from(Self::default())
    }
}

#[derive(Debug)]
pub struct ExtensionOracle<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy,
    VS,
    PS,
    S: TermSystem<K, V, T>,
    E: LocalExtension<K, V, T, VS, PS, S>,
> {
    extension: E,
    _phantom_data: PhantomData<(K, V, T, VS, PS, S)>,
}

impl<
    K: Hash + Eq + Copy + Debug,
    V: PartialOrd,
    T: Copy + Eq,
    VS: Without + Cartesian<Output = PS> + Diagonal<Output = PS> + for<'a> CopiedIter<'a, K> + Debug,
    PS: Union + Union<HashSet<(K, K)>> + FromIterator<(K, K)> + FromRights<VS, K> + Debug,
    S: TermSystem<K, V, T> + Universe<VS> + Visited<VS>,
    E: LocalExtension<K, V, T, VS, PS, S>,
> LocalOracle<K, V, PS, S> for ExtensionOracle<K, V, T, VS, PS, S, E>
{
    fn approximate_flow(&self, assignment: &HashMap<K, V>, possible: &PS, system: &S) -> PS {
        let visited = system.visited();
        let unvisited = system.universe().without(&visited);
        let unvisited_dep = system.universe().cartesian(&unvisited);
        let self_dep: PS = visited.diagonal();
        let term_dep = visited.copied_iter().map(|var| {
            let deps = self
                .extension
                .depends(system.definition(var), assignment, possible, system);
            (deps, var)
        });
        let term_dep = PS::from_rights(term_dep);

        self_dep.union(unvisited_dep).union(term_dep)
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    T: Copy + Eq,
    VS,
    PS: Union + FromIterator<(K, K)>,
    S: TermSystem<K, V, T>,
    E: LocalExtension<K, V, T, VS, PS, S>,
> From<E> for ExtensionOracle<K, V, T, VS, PS, S, E>
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
    VS,
    PS,
    S: TermSystem<K, V, T>,
    E: LocalExtension<K, V, T, VS, PS, S> + Clone,
> Clone for ExtensionOracle<K, V, T, VS, PS, S, E>
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
    VS,
    PS,
    S: TermSystem<K, V, T>,
    E: LocalExtension<K, V, T, VS, PS, S> + Display,
> Display for ExtensionOracle<K, V, T, VS, PS, S, E>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "E^({})", self.extension)
    }
}
