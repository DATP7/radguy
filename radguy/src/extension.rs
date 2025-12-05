use crate::Assignment;
use crate::Bottom;
use crate::Intersect;
use crate::Set;
use crate::ordered::oracle::StrategicLocalOracle;
use crate::ordered::strategy::GetWeight;
use crate::ordered::strategy::Strategy;
use crate::ordered::strategy::StrategyItem;
use std::{
    cmp::PartialOrd,
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
};

use crate::{
    Cartesian, CopiedIter, Diagonal, FromRights, System, Union, Universe, Visited, Without,
    oracle::LocalOracle, ordered::strategy::StrategyWeight,
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

//---------------------------------------------------------------------------------------------------//

pub trait StrategicExtension<
    VarKey,
    VarValue,
    TermKey,
    VarName,
    VS,
    VarStrat,
    PairStrat,
    S,
    // VarKey: Hash + Copy,
    // VarValue: Bottom + Clone,
    // TermKey: Hash + Copy,
    // VarName: Hash + Copy + Eq,
    // VS: for<'a> CopiedIter<'a, VarKey> + Debug,
    // VarStrat,
    // PairStrat: Strategy<(VarKey, VarKey)>
    //     + FromIterator<StrategyItem<(VarKey, VarKey)>>
    //     + IntoIterator<Item = StrategyItem<(VarKey, VarKey)>>
    //     + GetWeight<(VarKey, VarKey)>
    //     + Clone,
    // S: TermSystem<VarKey, VarValue, TermKey>,
>
{
    fn depends(
        &self,
        x: TermKey,
        assignment: &HashMap<VarKey, VarValue>,
        strategy: &PairStrat,
        system: &S,
    ) -> VarStrat;

    #[must_use]
    fn oracle() -> StrategicExtensionOracle<VarKey, VarValue, TermKey, VarName, VS, VarStrat, S, Self>
    where
        Self: Default,
    {
        StrategicExtensionOracle::from(Self::default())
    }
}

pub struct StrategicExtensionOracle<
    VarKey,
    VarValue,
    TermKey,
    VarName,
    VS,
    VarStrat,
    S,
    E,
    // VarKey: Hash + Copy,
    // VarValue: Bottom + Clone,
    // TermKey: Hash + Copy,
    // VarName: Hash + Copy + Eq,
    // VS: for<'a> CopiedIter<'a, VarKey> + Debug,
    // PairStrat: Strategy<(VarKey, VarKey)>
    //     + FromIterator<StrategyItem<(VarKey, VarKey)>>
    //     + IntoIterator<Item = StrategyItem<(VarKey, VarKey)>>
    //     + GetWeight<(VarKey, VarKey)>
    //     + Clone,
    // S: TermSystem<VarKey, VarValue, TermKey>,
    // E: StrategicExtension<VarKey, VarValue, TermKey, VarName, VS, PairStrat, S>,
> {
    extension: E,
    _phantom_data: PhantomData<(TermKey, VarKey, VarValue, VarName, VS, VarStrat, S)>,
}

impl<VarKey, VarValue, TermKey, VarName, VS, PS, VarStrat, PairStrat, S, E>
    StrategicLocalOracle<VarKey, VarValue, PairStrat, S>
    for StrategicExtensionOracle<VarKey, VarValue, TermKey, VarName, VS, VarStrat, S, E>
where
    VarKey: Hash + Eq + Copy,
    VarValue: Bottom + Clone,
    TermKey: Hash + Copy,
    VarName: Hash + Copy + Eq,
    VS: for<'a> CopiedIter<'a, VarKey> + Debug + Set<VarKey> + Without + Cartesian<Output = PS>,
    VarStrat: for<'a> CopiedIter<'a, StrategyItem<VarKey>> + IntoIterator<Item = StrategyItem<VarKey>>,
    PairStrat: Strategy<(VarKey, VarKey)>
        + FromIterator<StrategyItem<(VarKey, VarKey)>>
        + GetWeight<(VarKey, VarKey)>
        + Clone + Union + Intersect<PS>,
    S: TermSystem<VarKey, VarValue, TermKey> + Visited<VS> + Universe<VS>,
    E: StrategicExtension<VarKey, VarValue, TermKey, VarName, VS, VarStrat, PairStrat, S>,
{
    fn get_strategy(
        &self,
        assignment: &HashMap<VarKey, VarValue>,
        strategy: &PairStrat,
        system: &S,
    ) -> PairStrat {
        let visited = system.visited();
        let unvisited = system.universe().without(&visited);
        let unvisited_dep = strategy.clone().intersect(&system.universe().cartesian(&unvisited));

        let term_dep: PairStrat = visited
            .copied_iter()
            .flat_map(|y| {
                 self.extension.depends(system.definition(y), assignment, strategy, system).into_iter().map(move |StrategyItem(w, x)| if x != y {
                    StrategyItem(w, (x, y))
                } else if assignment.get_assignment(&x) != system.evaluate(x, assignment) {
                    StrategyItem(StrategyWeight::Num(0), (x,y))
                    } else {
                    StrategyItem(StrategyWeight::Infinity, (x,y))
                    }
                )
            }).collect();
        term_dep.union(unvisited_dep)
    }
}

impl<
    VarKey,
    VarValue,
    TermKey,
    VarName,
    VS,
    PairStrat,
    S,
    E,
> From<E> for StrategicExtensionOracle<VarKey, VarValue, TermKey, VarName, VS, PairStrat, S, E>
{
    fn from(extension: E) -> Self {
        Self {
            extension,
            _phantom_data: PhantomData,
        }
    }
}

//Without
//  + Cartesian<Output = PairStrat>
//  + Diagonal<Output = PairStrat>
//  + for<'a> CopiedIter<'a, VarKey> + Debug,
//let new_strat = strategy.clone();
//new_strat
//    .into_iter()
//    .filter_map(|StrategyItem(_, (x, y))| {
//        if x == y && assignment.get_assignment(&x) != system.evaluate(x, assignment) {
//            Some(StrategyItem(StrategyWeight::Num(0), (x, y)))
//        } else if x != y {
//            let y_term_key = system.definition(y);
//            let weight = self
//                .extension
//                .strategic_extend(x, y_term_key, assignment, strategy, system);
//            weight.map(|w| StrategyItem(w, (x, y)))
//        } else {
//            // Throws wrong stuff out and makes the big sad happen :c
//            None
//        }
//    })
//    .collect()

//let unvisited = system.universe().without(&visited);
//let unvisited_dep = system.universe().cartesian(&unvisited);
//let self_dep: PS = visited.diagonal();
//let term_dep = visited.copied_iter().map(|var| {
//    let deps = self
//        .extension
//        .depends(system.definition(var), assignment, possible, system);
//    (deps, var)
//});
//let term_dep = PS::from_rights(term_dep);

//self_dep.union(unvisited_dep).union(term_dep)
/*
new_strategy
    .into_iter()
    .filter_map(|StrategyItem(_, (x, y))| {
        if x == y && assignment.get_assignment(&x) != system.evaluate(x, assignment) {
            Some(StrategyItem(StrategyWeight::Num(0), (x, y)))
        } else if x != y {
            Some((new_strategy.GetWeight(x,y), (x,y)))
        } else {
            None
        }
    })
    .collect()*/
