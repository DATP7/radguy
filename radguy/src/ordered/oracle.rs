use std::cmp::Reverse;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Display;
use std::hash::Hash;
use std::marker::PhantomData;

use crate::System;
use crate::oracle::LocalOracle;
use crate::ordered::strategy::Domain;
use crate::ordered::strategy::IntersectBy;
use crate::ordered::strategy::SliceRight;
use crate::ordered::strategy::StrategyHeap;
use crate::ordered::strategy::StrategyItem;
use crate::ordered::strategy::StrategyWeight;
use crate::{Assignment, ordered::Strategy};

pub trait StrategicLocalOracle<
    K: Eq + Copy,
    V: PartialOrd,
    VS,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
>
{
    fn get_strategy(
        &self,
        visited: &VS,
        assignment: &impl Assignment<K, V>,
        strategy: &PairStrategy,
        system: &S,
    ) -> PairStrategy;

    #[must_use]
    fn then<O: StrategicLocalOracle<K, V, VS, PairStrategy, S>>(
        self,
        other: O,
    ) -> ComposeStrategic<K, V, VS, PairStrategy, S, O, Self>
    where
        Self: std::marker::Sized,
    {
        ComposeStrategic {
            outer: other,
            inner: self,
            _phantom_data: PhantomData,
        }
    }

    #[must_use]
    fn and_by<
        O: StrategicLocalOracle<K, V, VS, PairStrategy, S>,
        F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    >(
        self,
        other: O,
        f: F,
    ) -> IntersectByStrategic<K, V, VS, PairStrategy, S, O, Self, F>
    where
        Self: std::marker::Sized,
        PairStrategy: IntersectBy<(K, K)>,
    {
        IntersectByStrategic {
            left: other,
            right: self,
            f,
            _phantom_data: PhantomData,
        }
    }
}

pub struct Constant<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    VS,
    PS,
    S: System<K, V>,
    O: LocalOracle<K, V, VS, PS, S>,
> {
    oracle: O,
    value: StrategyWeight,
    _phantom_data: PhantomData<(K, V, VS, PS, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    VS,
    PS: IntoIterator<Item = (K, K)> + FromIterator<(K, K)>,
    S: System<K, V>,
    O: LocalOracle<K, V, VS, PS, S>,
> StrategicLocalOracle<K, V, VS, StrategyHeap<(K, K)>, S> for Constant<K, V, VS, PS, S, O>
{
    fn get_strategy(
        &self,
        visited: &VS,
        assignment: &impl Assignment<K, V>,
        strategy: &StrategyHeap<(K, K)>,
        system: &S,
    ) -> StrategyHeap<(K, K)> {
        self.oracle
            .approximate_flow(visited, assignment, &strategy.clone().domain(), system)
            .into_iter()
            .map(|v| Reverse(StrategyItem(self.value, v)))
            .collect()
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    VS,
    PS: IntoIterator<Item = (K, K)> + FromIterator<(K, K)>,
    S: System<K, V>,
    O: LocalOracle<K, V, VS, PS, S> + Display,
> Display for Constant<K, V, VS, PS, S, O>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_({})", self.oracle, self.value)
    }
}

pub trait ToConstant<K: Hash + Eq + Copy, V: PartialOrd, VS, PS, S: System<K, V>>:
    LocalOracle<K, V, VS, PS, S> + Sized
{
    /// Convert a classical local oracle to a strategic local oracle, where all elements in the
    /// relation are assigned to `value`
    fn constant(self, value: StrategyWeight) -> Constant<K, V, VS, PS, S, Self> {
        Constant {
            oracle: self,
            value,
            _phantom_data: PhantomData,
        }
    }
}

impl<K: Hash + Eq + Copy, V: PartialOrd, VS, PS, S: System<K, V>, O: LocalOracle<K, V, VS, PS, S>>
    ToConstant<K, V, VS, PS, S> for O
{
}

pub struct ComposeStrategic<
    K: Eq + Copy,
    V: PartialOrd,
    VS,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, VS, PairStrategy, S>,
    U: StrategicLocalOracle<K, V, VS, PairStrategy, S>,
> {
    outer: T,
    inner: U,
    _phantom_data: PhantomData<(K, V, VS, PairStrategy, S)>,
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    VS,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, VS, PairStrategy, S>,
    U: StrategicLocalOracle<K, V, VS, PairStrategy, S>,
> StrategicLocalOracle<K, V, VS, PairStrategy, S>
    for ComposeStrategic<K, V, VS, PairStrategy, S, T, U>
{
    fn get_strategy(
        &self,
        visited: &VS,
        assignment: &impl Assignment<K, V>,
        strategy: &PairStrategy,
        system: &S,
    ) -> PairStrategy {
        self.outer.get_strategy(
            visited,
            assignment,
            &self
                .inner
                .get_strategy(visited, assignment, strategy, system),
            system,
        )
    }
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    VS,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, VS, PairStrategy, S> + Display,
    U: StrategicLocalOracle<K, V, VS, PairStrategy, S> + Display,
> Display for ComposeStrategic<K, V, VS, PairStrategy, S, T, U>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ∘ {})", self.outer, self.inner)
    }
}

pub struct IntersectByStrategic<
    K: Eq + Copy,
    V: PartialOrd,
    VS,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, VS, PairStrategy, S>,
    U: StrategicLocalOracle<K, V, VS, PairStrategy, S>,
    F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
> {
    left: T,
    right: U,
    f: F,
    _phantom_data: PhantomData<(K, V, VS, PairStrategy, S)>,
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    VS,
    PairStrategy: Strategy<(K, K)> + IntersectBy<(K, K), PairStrategy>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, VS, PairStrategy, S>,
    U: StrategicLocalOracle<K, V, VS, PairStrategy, S>,
    F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
> StrategicLocalOracle<K, V, VS, PairStrategy, S>
    for IntersectByStrategic<K, V, VS, PairStrategy, S, T, U, F>
{
    fn get_strategy(
        &self,
        visited: &VS,
        assignment: &impl Assignment<K, V>,
        strategy: &PairStrategy,
        system: &S,
    ) -> PairStrategy {
        // PERF: it might be a lot more efficient to just have a hard-coded `IntersectMin`
        self.left
            .get_strategy(visited, assignment, strategy, system)
            .intersect_by(
                &self
                    .right
                    .get_strategy(visited, assignment, strategy, system),
                &self.f,
            )
    }
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    VS,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, VS, PairStrategy, S> + Display,
    U: StrategicLocalOracle<K, V, VS, PairStrategy, S> + Display,
    F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
> Display for IntersectByStrategic<K, V, VS, PairStrategy, S, T, U, F>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ∩_f {})", self.left, self.right)
    }
}

pub struct CountOracle;

// TODO: Make this generic on set/strategy implementation
impl<K: Eq + Copy + Hash, V: PartialOrd, S: System<K, V>>
    StrategicLocalOracle<K, V, HashSet<K>, StrategyHeap<(K, K)>, S> for CountOracle
{
    fn get_strategy(
        &self,
        _visited: &HashSet<K>,
        _assignment: &impl Assignment<K, V>,
        strategy: &StrategyHeap<(K, K)>,
        _system: &S,
    ) -> StrategyHeap<(K, K)> {
        let mut lens = HashMap::<K, u64>::new();
        strategy
            .iter()
            .map(|Reverse(StrategyItem(_, (x, y)))| {
                Reverse(StrategyItem(
                    StrategyWeight::Num(
                        *lens
                            .entry(*x)
                            .or_insert_with(|| strategy.clone().slice_right(*x).len() as u64),
                    ),
                    (*x, *y),
                ))
            })
            .collect()
    }
}

impl Display for CountOracle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Count")
    }
}

pub struct InverseCountOracle;

// TODO: Make this generic on set/strategy implementation
impl<K: Eq + Copy + Hash, V: PartialOrd, S: System<K, V>>
    StrategicLocalOracle<K, V, HashSet<K>, StrategyHeap<(K, K)>, S> for InverseCountOracle
{
    fn get_strategy(
        &self,
        _visited: &HashSet<K>,
        _assignment: &impl Assignment<K, V>,
        strategy: &StrategyHeap<(K, K)>,
        _system: &S,
    ) -> StrategyHeap<(K, K)> {
        let mut lens = HashMap::<K, u64>::new();
        strategy
            .iter()
            .map(|Reverse(StrategyItem(_, (x, y)))| {
                Reverse(StrategyItem(
                    StrategyWeight::Num(*lens.entry(*x).or_insert_with(|| {
                        u64::MAX - (strategy.clone().slice_right(*x).len() as u64)
                    })),
                    (*x, *y),
                ))
            })
            .collect()
    }
}

impl Display for InverseCountOracle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Count⁻¹")
    }
}
