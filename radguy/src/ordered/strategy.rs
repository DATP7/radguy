use std::{
    cmp::{Ordering, Reverse},
    collections::{BinaryHeap, HashMap, HashSet},
    fmt::Display,
    hash::Hash,
};

use crate::System;

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum StrategyWeight {
    Infinity,
    Num(u64),
}

impl Ord for StrategyWeight {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Infinity, Self::Infinity) => Ordering::Equal,
            (Self::Infinity, _) => Ordering::Greater,
            (_, Self::Infinity) => Ordering::Less,
            (Self::Num(x), Self::Num(y)) => x.cmp(y),
        }
    }
}

impl PartialOrd for StrategyWeight {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for StrategyWeight {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Infinity => write!(f, "∞"),
            Self::Num(x) => write!(f, "{x}"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct StrategyItem<T>(pub StrategyWeight, pub T);

impl<T> StrategyItem<T> {
    pub const fn infinite(value: T) -> Self {
        Self(StrategyWeight::Infinity, value)
    }

    pub const fn reversed(self) -> Reverse<Self> {
        Reverse(self)
    }
}

impl<T> Ord for StrategyItem<T> {
    fn cmp(&self, Self(o, _): &Self) -> std::cmp::Ordering {
        let Self(s, _) = self;
        s.cmp(o)
    }
}
impl<T> PartialOrd for StrategyItem<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> PartialEq for StrategyItem<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for StrategyItem<T> {}

pub trait Strategy<T: Copy> {
    /// Extract the element in the strategy with the lowest weight
    ///
    /// Returns `None` of there are no more elements in the strategy
    // TODO: should we just have an iterator instead?
    fn extract_min(&mut self) -> Option<T>;
}

pub trait InitialStrategy<
    VarKey: Copy,
    VarValue: PartialOrd,
    OutStrategy: Strategy<(VarKey, VarKey)>,
>: System<VarKey, VarValue>
{
    /// Get a strategy where all variables are assigned to infinity
    fn get_initial_strategy(&self) -> OutStrategy;
}

pub trait SliceLeft<T: Eq, U: Copy, S: Strategy<U>>: Strategy<(T, U)>
where
    (T, U): Copy,
    Self: Sized,
{
    /// Get a strategy where all values are of the form `(left, x)`
    fn slice_left(self, left: T) -> S;
}

pub trait SliceRight<T: Copy, U: Eq, S: Strategy<T>>: Strategy<(T, U)>
where
    (T, U): Copy,
    Self: Sized,
{
    /// Get a strategy where all values are of the form `(x, right)`
    fn slice_right(self, right: U) -> S;
}

pub trait Intersect<T: Eq + Copy, Other = Self> {
    #[must_use]
    fn intersect(self, other: &Other) -> Self;
}

pub trait IntersectBy<T: Eq + Copy, Other: Strategy<T> = Self> {
    #[must_use]
    /// Intersect the domains of two strategies, using `f` to compute the new weight elements
    fn intersect_by(
        self,
        other: &Other,
        f: impl Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    ) -> Self;
}

pub trait Domain<T: Copy, S>: Strategy<T> {
    /// Get the set of elements that have a value in the strategy
    fn domain(self) -> S;
}

pub trait Singleton<T: Copy>: Strategy<T> {
    /// Return a new strategy where `x -> infinity`
    fn singleton(x: T) -> Self;
}

pub type StrategyHeap<T> = BinaryHeap<Reverse<StrategyItem<T>>>;

// TODO: should we just invert the comparison of `StrategyItem`s instead of spamming `Reverse`
// everywhere?
impl<T: Copy> Strategy<T> for StrategyHeap<T> {
    fn extract_min(&mut self) -> Option<T> {
        self.pop().map(|Reverse(StrategyItem(_, v))| v)
    }
}

impl<T: Eq + Copy + Hash> Intersect<T, HashSet<T>> for StrategyHeap<T> {
    fn intersect(self, other: &HashSet<T>) -> Self {
        self.into_iter()
            .filter(|Reverse(StrategyItem(_, v))| other.contains(v))
            .collect()
    }
}

impl<T: Eq + Copy + Hash> IntersectBy<T, Self> for StrategyHeap<T> {
    fn intersect_by(
        self,
        other: &Self,
        f: impl Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    ) -> Self {
        let other_map: HashMap<_, _> = other
            .iter()
            .map(|Reverse(StrategyItem(w, v))| (v, w))
            .collect();
        self.into_iter()
            .filter_map(|Reverse(StrategyItem(w_self, v))| {
                other_map
                    .get(&v)
                    .map(|&w_other| Reverse(StrategyItem(f(w_self, *w_other), v)))
            })
            .collect()
    }
}

impl<T: Eq, U: Copy> SliceLeft<T, U, StrategyHeap<U>> for StrategyHeap<(T, U)>
where
    (T, U): Copy,
{
    fn slice_left(self, left: T) -> StrategyHeap<U> {
        self.into_iter()
            .filter_map(|Reverse(StrategyItem(w, (t, u)))| {
                if t == left {
                    Some(Reverse(StrategyItem(w, u)))
                } else {
                    None
                }
            })
            .collect()
    }
}

impl<T: Copy, U: Eq> SliceRight<T, U, StrategyHeap<T>> for StrategyHeap<(T, U)>
where
    (T, U): Copy,
{
    fn slice_right(self, right: U) -> StrategyHeap<T> {
        self.into_iter()
            .filter_map(|Reverse(StrategyItem(w, (t, u)))| {
                if u == right {
                    Some(Reverse(StrategyItem(w, t)))
                } else {
                    None
                }
            })
            .collect()
    }
}

impl<T: Copy, S: FromIterator<T>> Domain<T, S> for StrategyHeap<T> {
    fn domain(self) -> S {
        self.into_iter()
            .map(|Reverse(StrategyItem(_, v))| v)
            .collect()
    }
}

impl<T: Copy> Singleton<T> for StrategyHeap<T> {
    fn singleton(x: T) -> Self {
        Self::from_iter([Reverse(StrategyItem(StrategyWeight::Infinity, x))])
    }
}
