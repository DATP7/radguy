use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
};

use crate::{
    System,
    ordered::{
        StrategicLocalOracle,
        strategy::{Length, SliceLeft, SliceRight, Strategy, StrategyItem, StrategyWeight},
    },
};

#[derive(Default, Clone, Debug)]
pub struct DependencyCountOracle<VS>(PhantomData<VS>);

impl<
    K: Eq + Copy + Hash,
    V: PartialOrd,
    VS: Strategy<K> + Length,
    PS: Strategy<(K, K)> + SliceRight<K, K, VS> + FromIterator<StrategyItem<(K, K)>> + Clone + Debug,
    S: System<K, V>,
> StrategicLocalOracle<K, V, PS, S> for DependencyCountOracle<VS>
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn get_strategy(&self, _assignment: &HashMap<K, V>, strategy: &PS, _system: &S) -> PS {
        let mut lens = HashMap::<K, u64>::new();
        strategy
            .into_iter()
            .map(|StrategyItem(_, (x, y))| {
                StrategyItem(
                    StrategyWeight::Num(
                        *lens
                            .entry(x)
                            .or_insert_with(|| strategy.clone().slice_right(x).length() as u64),
                    ),
                    (x, y),
                )
            })
            .collect()
    }
}

impl<VS> Display for DependencyCountOracle<VS> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DependencyCount")
    }
}

#[derive(Clone, Default)]
pub struct InverseDependencyCountOracle<VS>(PhantomData<VS>);

impl<
    K: Eq + Copy + Hash,
    V: PartialOrd,
    VS: Strategy<K> + Length,
    PS: Strategy<(K, K)> + SliceRight<K, K, VS> + FromIterator<StrategyItem<(K, K)>> + Clone,
    S: System<K, V>,
> StrategicLocalOracle<K, V, PS, S> for InverseDependencyCountOracle<VS>
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn get_strategy(&self, _assignment: &HashMap<K, V>, strategy: &PS, _system: &S) -> PS {
        let mut lens = HashMap::<K, u64>::new();
        strategy
            .into_iter()
            .map(|StrategyItem(_, (x, y))| {
                StrategyItem(
                    StrategyWeight::Num(*lens.entry(x).or_insert_with(|| {
                        u64::MAX - (strategy.clone().slice_right(x).length() as u64)
                    })),
                    (x, y),
                )
            })
            .collect()
    }
}

impl<VS> Display for InverseDependencyCountOracle<VS> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DependencyCount⁻¹")
    }
}

#[derive(Default, Clone, Debug)]
pub struct DependentCountOracle<VS>(PhantomData<VS>);

impl<
    K: Eq + Copy + Hash,
    V: PartialOrd,
    VS: Strategy<K> + Length,
    PS: Strategy<(K, K)> + SliceLeft<K, K, VS> + FromIterator<StrategyItem<(K, K)>> + Clone + Debug,
    S: System<K, V>,
> StrategicLocalOracle<K, V, PS, S> for DependentCountOracle<VS>
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn get_strategy(&self, _assignment: &HashMap<K, V>, strategy: &PS, _system: &S) -> PS {
        let mut lens = HashMap::<K, u64>::new();
        strategy
            .into_iter()
            .map(|StrategyItem(_, (x, y))| {
                StrategyItem(
                    StrategyWeight::Num(
                        *lens
                            .entry(x)
                            .or_insert_with(|| strategy.clone().slice_left(x).length() as u64),
                    ),
                    (x, y),
                )
            })
            .collect()
    }
}

impl<VS> Display for DependentCountOracle<VS> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DependentCount")
    }
}

#[derive(Clone, Default)]
pub struct InverseDependentCountOracle<VS>(PhantomData<VS>);

impl<
    K: Eq + Copy + Hash,
    V: PartialOrd,
    VS: Strategy<K> + Length,
    PS: Strategy<(K, K)> + SliceLeft<K, K, VS> + FromIterator<StrategyItem<(K, K)>> + Clone,
    S: System<K, V>,
> StrategicLocalOracle<K, V, PS, S> for InverseDependentCountOracle<VS>
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn get_strategy(&self, _assignment: &HashMap<K, V>, strategy: &PS, _system: &S) -> PS {
        let mut lens = HashMap::<K, u64>::new();
        strategy
            .into_iter()
            .map(|StrategyItem(_, (x, y))| {
                StrategyItem(
                    StrategyWeight::Num(*lens.entry(x).or_insert_with(|| {
                        u64::MAX - (strategy.clone().slice_left(x).length() as u64)
                    })),
                    (x, y),
                )
            })
            .collect()
    }
}

impl<VS> Display for InverseDependentCountOracle<VS> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DependentCount⁻¹")
    }
}
