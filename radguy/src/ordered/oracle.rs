use std::{cmp, collections::HashMap, fmt::Display, hash::Hash, marker::PhantomData};

use crate::{
    Set, System,
    oracle::LocalOracle,
    ordered::{
        Strategy,
        strategy::{Domain, IntersectBy, StrategyItem, StrategyWeight},
    },
};

mod dependency;
mod generic;
pub use dependency::*;
pub use generic::*;

pub trait StrategicLocalOracle<
    K: Eq + Copy,
    V: PartialOrd,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
>
{
    fn get_strategy(
        &self,
        assignment: &HashMap<K, V>,
        strategy: &PairStrategy,
        system: &S,
    ) -> PairStrategy;

    #[must_use]
    fn then<O: StrategicLocalOracle<K, V, PairStrategy, S>>(
        self,
        other: O,
    ) -> ComposeStrategic<K, V, PairStrategy, S, O, Self>
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
        O: StrategicLocalOracle<K, V, PairStrategy, S>,
        F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    >(
        self,
        other: O,
        f: F,
    ) -> IntersectByStrategic<K, V, PairStrategy, S, Self, O, F>
    where
        Self: std::marker::Sized,
        PairStrategy: IntersectBy<(K, K)>,
    {
        IntersectByStrategic {
            left: self,
            right: other,
            f,
            name: None,
            _phantom_data: PhantomData,
        }
    }

    #[must_use]
    fn and_by_with_name<
        O: StrategicLocalOracle<K, V, PairStrategy, S>,
        F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    >(
        self,
        other: O,
        f: F,
        name: &'static str,
    ) -> IntersectByStrategic<K, V, PairStrategy, S, Self, O, F>
    where
        Self: std::marker::Sized,
        PairStrategy: IntersectBy<(K, K)>,
    {
        IntersectByStrategic {
            left: self,
            right: other,
            f,
            name: Some(name),
            _phantom_data: PhantomData,
        }
    }
}

pub struct Constant<K, V: PartialOrd, PS, S: System<K, V>, O: LocalOracle<K, V, PS, S>> {
    oracle: O,
    value: StrategyWeight,
    _phantom_data: PhantomData<(K, V, PS, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PS: IntoIterator<Item = (K, K)> + FromIterator<(K, K)>,
    PairStrategy: Domain<(K, K), PS> + FromIterator<StrategyItem<(K, K)>> + Clone,
    S: System<K, V>,
    O: LocalOracle<K, V, PS, S>,
> StrategicLocalOracle<K, V, PairStrategy, S> for Constant<K, V, PS, S, O>
{
    fn get_strategy(
        &self,
        assignment: &HashMap<K, V>,
        strategy: &PairStrategy,
        system: &S,
    ) -> PairStrategy {
        self.oracle
            .approximate_flow(assignment, &strategy.clone().domain(), system)
            .into_iter()
            .map(|v| StrategyItem(self.value, v))
            .collect()
    }
}
impl<K, V: PartialOrd, PS, S: System<K, V>, O: LocalOracle<K, V, PS, S> + Clone> Clone
    for Constant<K, V, PS, S, O>
{
    fn clone(&self) -> Self {
        Self {
            oracle: self.oracle.clone(),
            value: self.value,
            _phantom_data: self._phantom_data,
        }
    }
}

impl<K: Hash + Eq + Copy, V: PartialOrd, PS, S: System<K, V>, O: LocalOracle<K, V, PS, S> + Display>
    Display for Constant<K, V, PS, S, O>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_({})", self.oracle, self.value)
    }
}

pub trait ToConstant<K: Hash + Eq + Copy, V: PartialOrd, S: System<K, V>>: Sized {
    /// Convert a classical local oracle to a strategic local oracle, where all elements in the
    /// relation are assigned to `value`
    fn constant<PS>(self, value: StrategyWeight) -> Constant<K, V, PS, S, Self>
    where
        Self: LocalOracle<K, V, PS, S>,
    {
        Constant {
            oracle: self,
            value,
            _phantom_data: PhantomData,
        }
    }
}

impl<K: Hash + Eq + Copy, V: PartialOrd, S: System<K, V>, O> ToConstant<K, V, S> for O {}

pub struct Ordered<K, V: PartialOrd, PS, S: System<K, V>, O: LocalOracle<K, V, PS, S>> {
    oracle: O,
    _phantom_data: PhantomData<(K, V, PS, S)>,
}

impl<
    K: Copy + Eq,
    V: PartialOrd,
    PS: Set<(K, K)>,
    PairStrategy: Domain<(K, K), PS> + FromIterator<StrategyItem<(K, K)>> + Clone,
    S: System<K, V>,
    O: LocalOracle<K, V, PS, S>,
> StrategicLocalOracle<K, V, PairStrategy, S> for Ordered<K, V, PS, S, O>
where
    for<'a> &'a PairStrategy: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn get_strategy(
        &self,
        assignment: &HashMap<K, V>,
        strategy: &PairStrategy,
        system: &S,
    ) -> PairStrategy {
        let rel = self
            .oracle
            .approximate_flow(assignment, &strategy.clone().domain(), system);
        strategy
            .into_iter()
            .filter(|x| rel.contains(&x.1))
            .collect()
    }
}

impl<K, V: PartialOrd, PS, S: System<K, V>, O: LocalOracle<K, V, PS, S> + Clone> Clone
    for Ordered<K, V, PS, S, O>
{
    fn clone(&self) -> Self {
        Self {
            oracle: self.oracle.clone(),
            _phantom_data: PhantomData,
        }
    }
}

impl<
    K,
    V: PartialOrd,
    PS: IntoIterator<Item = (K, K)> + FromIterator<(K, K)>,
    S: System<K, V>,
    O: LocalOracle<K, V, PS, S> + Display,
> Display for Ordered<K, V, PS, S, O>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}\u{2191}", self.oracle)
    }
}

pub trait ToOrdered<K: Hash + Eq + Copy, V: PartialOrd, S: System<K, V>>: Sized {
    /// Convert a classical local oracle to a strategic local oracle, keeping the weights of the
    /// input strategy
    fn ordered<PS>(self) -> Ordered<K, V, PS, S, Self>
    where
        Self: LocalOracle<K, V, PS, S>,
    {
        Ordered {
            oracle: self,
            _phantom_data: PhantomData,
        }
    }
}

impl<K: Hash + Eq + Copy, V: PartialOrd, S: System<K, V>, O> ToOrdered<K, V, S> for O {}

pub struct ComposeStrategic<
    K: Eq + Copy,
    V: PartialOrd,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, PairStrategy, S>,
    U: StrategicLocalOracle<K, V, PairStrategy, S>,
> {
    outer: T,
    inner: U,
    _phantom_data: PhantomData<(K, V, PairStrategy, S)>,
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, PairStrategy, S>,
    U: StrategicLocalOracle<K, V, PairStrategy, S>,
> StrategicLocalOracle<K, V, PairStrategy, S> for ComposeStrategic<K, V, PairStrategy, S, T, U>
{
    fn get_strategy(
        &self,
        assignment: &HashMap<K, V>,
        strategy: &PairStrategy,
        system: &S,
    ) -> PairStrategy {
        self.outer.get_strategy(
            assignment,
            &self.inner.get_strategy(assignment, strategy, system),
            system,
        )
    }
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, PairStrategy, S> + Display,
    U: StrategicLocalOracle<K, V, PairStrategy, S> + Display,
> Display for ComposeStrategic<K, V, PairStrategy, S, T, U>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ∘ {})", self.outer, self.inner)
    }
}

pub struct IntersectByStrategic<
    K: Eq + Copy,
    V: PartialOrd,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, PairStrategy, S>,
    U: StrategicLocalOracle<K, V, PairStrategy, S>,
    F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
> {
    left: T,
    right: U,
    name: Option<&'static str>,
    f: F,
    _phantom_data: PhantomData<(K, V, PairStrategy, S)>,
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    PairStrategy: Strategy<(K, K)> + IntersectBy<(K, K), PairStrategy>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, PairStrategy, S>,
    U: StrategicLocalOracle<K, V, PairStrategy, S>,
    F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
> StrategicLocalOracle<K, V, PairStrategy, S>
    for IntersectByStrategic<K, V, PairStrategy, S, T, U, F>
{
    fn get_strategy(
        &self,
        assignment: &HashMap<K, V>,
        strategy: &PairStrategy,
        system: &S,
    ) -> PairStrategy {
        // PERF: it might be a lot more efficient to just have a hard-coded `IntersectMin`
        self.left
            .get_strategy(assignment, strategy, system)
            .intersect_by(
                &self.right.get_strategy(assignment, strategy, system),
                &self.f,
            )
    }
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, PairStrategy, S> + Display,
    U: StrategicLocalOracle<K, V, PairStrategy, S> + Display,
    F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
> Display for IntersectByStrategic<K, V, PairStrategy, S, T, U, F>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({} ∩_{} {})",
            self.left,
            self.name.unwrap_or("f"),
            self.right
        )
    }
}

// We need to manually implement `Clone` for these oracles, because the derive macro requires that
// all type parameters of the type implement `Clone`, meaning that `S` needs to implement clone,
// even though it isn't part of the actual struct
impl<
    K: Eq + Copy,
    V: PartialOrd,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, PairStrategy, S> + Clone,
    U: StrategicLocalOracle<K, V, PairStrategy, S> + Clone,
    F: Fn(StrategyWeight, StrategyWeight) -> StrategyWeight + Clone,
> Clone for IntersectByStrategic<K, V, PairStrategy, S, T, U, F>
{
    fn clone(&self) -> Self {
        Self {
            left: self.left.clone(),
            right: self.right.clone(),
            f: self.f.clone(),
            name: self.name,
            _phantom_data: self._phantom_data,
        }
    }
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    PairStrategy: Strategy<(K, K)>,
    S: System<K, V>,
    T: StrategicLocalOracle<K, V, PairStrategy, S> + Clone,
    U: StrategicLocalOracle<K, V, PairStrategy, S> + Clone,
> Clone for ComposeStrategic<K, V, PairStrategy, S, T, U>
{
    fn clone(&self) -> Self {
        Self {
            outer: self.outer.clone(),
            inner: self.inner.clone(),
            _phantom_data: self._phantom_data,
        }
    }
}

pub trait ToInverse<K: Eq + Copy, V: PartialOrd, PS: Strategy<(K, K)>, S: System<K, V>>:
    Sized + StrategicLocalOracle<K, V, PS, S>
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn inverse(self) -> InverseOracle<K, V, PS, S, Self> {
        InverseOracle::from(self)
    }
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    PS: Strategy<(K, K)>,
    S: System<K, V>,
    O: StrategicLocalOracle<K, V, PS, S>,
> ToInverse<K, V, PS, S> for O
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
}

#[derive(Default, Clone)]
pub struct InverseOracle<
    K: Eq + Copy,
    V: PartialOrd,
    PS: Strategy<(K, K)>,
    S: System<K, V>,
    O: StrategicLocalOracle<K, V, PS, S>,
> {
    oracle: O,
    _phantom_data: PhantomData<(K, V, S, PS)>,
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    PS: Strategy<(K, K)> + FromIterator<StrategyItem<(K, K)>>,
    S: System<K, V>,
    O: StrategicLocalOracle<K, V, PS, S>,
> StrategicLocalOracle<K, V, PS, S> for InverseOracle<K, V, PS, S, O>
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn get_strategy(&self, assignment: &HashMap<K, V>, strategy: &PS, system: &S) -> PS {
        let inner_strategy = self.oracle.get_strategy(assignment, strategy, system);
        let (min, max) = inner_strategy.into_iter().map(|s| s.0).fold(
            (StrategyWeight::Infinity, StrategyWeight::Num(0)),
            |(min, max), w| (cmp::min(min, w), cmp::max(max, w)),
        );
        inner_strategy
            .into_iter()
            .map(|StrategyItem(w, pair)| StrategyItem(max - w + min, pair))
            .collect()
    }
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    PS: Strategy<(K, K)>,
    S: System<K, V>,
    O: StrategicLocalOracle<K, V, PS, S>,
> From<O> for InverseOracle<K, V, PS, S, O>
{
    fn from(value: O) -> Self {
        Self {
            oracle: value,
            _phantom_data: PhantomData,
        }
    }
}

impl<
    K: Eq + Copy,
    V: PartialOrd,
    PS: Strategy<(K, K)>,
    S: System<K, V>,
    O: StrategicLocalOracle<K, V, PS, S> + Display,
> Display for InverseOracle<K, V, PS, S, O>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})⁻¹", self.oracle)
    }
}
