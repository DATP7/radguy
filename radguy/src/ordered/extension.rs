use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
};

use crate::{
    Assignment, Bottom, Cartesian, CopiedIter, Diagonal, Intersect, Set, Union, Universe, Visited,
    Without,
    extension::TermSystem,
    ordered::{
        oracle::StrategicLocalOracle,
        strategy::{
            GetWeight, HashMapStrategy, Strategy, StrategyItem, StrategyWeight, UnionWithBy,
        },
    },
};

pub trait StrategicExtension<VarKey, VarValue, TermKey, VarName, VS, VarStrat, PairStrat, S> {
    fn depends(
        &self,
        x: TermKey,
        assignment: &HashMap<VarKey, VarValue>,
        strategy: &PairStrat,
        system: &S,
    ) -> VarStrat;

    #[must_use]
    fn oracle()
    -> StrategicExtensionOracle<VarKey, VarValue, TermKey, VarName, VS, VarStrat, S, Self>
    where
        Self: Default,
    {
        StrategicExtensionOracle::from(Self::default())
    }
}

pub struct StrategicExtensionOracle<VarKey, VarValue, TermKey, VarName, VS, VarStrat, S, E> {
    extension: E,
    _phantom_data: PhantomData<(TermKey, VarKey, VarValue, VarName, VS, VarStrat, S)>,
}

impl<VarKey, VarValue, TermKey, VarName, VS, PS, VarStrat, PairStrat, S, E>
    StrategicLocalOracle<VarKey, VarValue, PairStrat, S>
    for StrategicExtensionOracle<VarKey, VarValue, TermKey, VarName, VS, VarStrat, S, E>
where
    VarKey: Hash + Eq + Copy + Debug,
    VarValue: Bottom + Clone,
    TermKey: Hash + Copy,
    VarName: Hash + Copy + Eq,
    VS: for<'a> CopiedIter<'a, VarKey>
        + Debug
        + Set<VarKey>
        + Without
        + Cartesian<Output = PS>
        + Diagonal,
    PairStrat: Strategy<(VarKey, VarKey)>
        + FromIterator<StrategyItem<(VarKey, VarKey)>>
        + for<'a> CopiedIter<'a, StrategyItem<(VarKey, VarKey)>>
        + GetWeight<(VarKey, VarKey)>
        + Clone
        + Union
        + Intersect<PS>
        + UnionWithBy<(VarKey, VarKey)>,
    S: TermSystem<VarKey, VarValue, TermKey> + Visited<VS> + Universe<VS>,
    E: StrategicExtension<
            VarKey,
            VarValue,
            TermKey,
            VarName,
            VS,
            HashMapStrategy<VarKey>,
            HashMapStrategy<(VarKey, VarKey)>,
            S,
        >,
{
    fn get_strategy(
        &self,
        assignment: &HashMap<VarKey, VarValue>,
        strategy: &PairStrat,
        system: &S,
    ) -> PairStrat {
        let visited = system.visited();
        let unvisited = system.universe().without(&visited);
        let unvisited_dep = strategy
            .clone()
            .intersect(&system.universe().cartesian(&unvisited));

        let self_dep = visited
            .copied_iter()
            .map(|x| {
                if assignment.get_assignment(&x) == system.evaluate(x, assignment) {
                    StrategyItem::infinite((x, x))
                } else {
                    StrategyItem(StrategyWeight::Num(0), (x, x))
                }
            })
            .collect();

        let map: HashMapStrategy<_> = strategy.copied_iter().collect();

        let term_dep: PairStrat = visited
            .copied_iter()
            .flat_map(|y| {
                self.extension
                    .depends(system.definition(y), assignment, &map, system)
                    .into_iter()
                    .map(move |StrategyItem(w, x)| StrategyItem(w, (x, y)))
            })
            .collect();
        let mut ret = term_dep.union(unvisited_dep);
        ret.union_with_by(self_dep, std::cmp::min);
        ret
    }
}

impl<VarKey, VarValue, TermKey, VarName, VS, PairStrat, S, E> From<E>
    for StrategicExtensionOracle<VarKey, VarValue, TermKey, VarName, VS, PairStrat, S, E>
{
    fn from(extension: E) -> Self {
        Self {
            extension,
            _phantom_data: PhantomData,
        }
    }
}

impl<VarKey, VarValue, TermKey, VarName, VS, VarStrat, S, E: Clone> Clone
    for StrategicExtensionOracle<VarKey, VarValue, TermKey, VarName, VS, VarStrat, S, E>
{
    fn clone(&self) -> Self {
        Self {
            extension: self.extension.clone(),
            _phantom_data: PhantomData,
        }
    }
}

impl<VarKey, VarValue, TermKey, VarName, VS, VarStrat, S, E: Display> Display
    for StrategicExtensionOracle<VarKey, VarValue, TermKey, VarName, VS, VarStrat, S, E>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "StratE^({})", self.extension)
    }
}
