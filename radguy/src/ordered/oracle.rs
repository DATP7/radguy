use std::{cmp::Reverse, fmt::Display, hash::Hash, marker::PhantomData};

use crate::{
    Assignment, System,
    oracle::LocalOracle,
    ordered::{
        Strategy,
        strategy::{Domain, IntersectBy, StrategyHeap, StrategyItem, StrategyWeight},
    },
};

mod generic;
pub use generic::*;

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
    ) -> IntersectByStrategic<K, V, VS, PairStrategy, S, Self, O, F>
    where
        Self: std::marker::Sized,
        PairStrategy: IntersectBy<(K, K)>,
    {
        IntersectByStrategic {
            left: self,
            right: other,
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

// We need to manually implement `Clone` for these oracles, because the derive macro requires that
// all type parameters of the type implement `Clone`, meaning that `S` needs to implement clone,
// even though it isn't part of the actual struct
impl<
    K: Eq + Copy,
    V: PartialOrd,
    VS,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, VS, PairStrategy, S> + Clone,
    U: StrategicLocalOracle<K, V, VS, PairStrategy, S> + Clone,
    F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight + Clone,
> Clone for IntersectByStrategic<K, V, VS, PairStrategy, S, T, U, F>
{
    fn clone(&self) -> Self {
        Self {
            left: self.left.clone(),
            right: self.right.clone(),
            f: self.f.clone(),
            _phantom_data: self._phantom_data,
        }
    }
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    VS,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, VS, PairStrategy, S> + Clone,
    U: StrategicLocalOracle<K, V, VS, PairStrategy, S> + Clone,
> Clone for ComposeStrategic<K, V, VS, PairStrategy, S, T, U>
{
    fn clone(&self) -> Self {
        Self {
            outer: self.outer.clone(),
            inner: self.inner.clone(),
            _phantom_data: self._phantom_data,
        }
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    VS,
    PS,
    S: System<K, V>,
    O: LocalOracle<K, V, VS, PS, S> + Clone,
> Clone for Constant<K, V, VS, PS, S, O>
{
    fn clone(&self) -> Self {
        Self {
            oracle: self.oracle.clone(),
            value: self.value,
            _phantom_data: self._phantom_data,
        }
    }
}
