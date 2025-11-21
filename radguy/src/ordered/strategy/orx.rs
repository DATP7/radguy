use crate::Intersect;
use std::fmt::Debug;
use std::{
    cmp::Reverse,
    collections::{HashMap, HashSet},
    hash::Hash,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use orx_priority_queue::{DaryHeapWithMap, NodeKeyRef, PriorityQueueDecKey};

use crate::ordered::strategy::{
    Domain, IntersectBy, LeftSliced, Length, ResetWeights, RightSliced, Singleton, SliceLeft,
    SliceRight, Strategy, StrategyItem, StrategyWeight,
};

#[derive(Clone, Debug)]
pub struct OrxStrategy<T: Clone, H: PriorityQueueDecKey<T, StrategyWeight>>(H, PhantomData<T>);

impl<T: Copy, H: PriorityQueueDecKey<T, StrategyWeight>> OrxStrategy<T, H> {
    pub fn iter(&self) -> impl Iterator<Item = StrategyItem<T>> {
        <&Self as IntoIterator>::into_iter(self)
    }
}

impl<T: Clone, H: PriorityQueueDecKey<T, StrategyWeight> + Default> Default for OrxStrategy<T, H> {
    fn default() -> Self {
        Self(Default::default(), PhantomData)
    }
}

impl<T: Clone, H: PriorityQueueDecKey<T, StrategyWeight>> Deref for OrxStrategy<T, H> {
    type Target = H;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: Clone, H: PriorityQueueDecKey<T, StrategyWeight>> DerefMut for OrxStrategy<T, H> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: Copy + Eq, H: PriorityQueueDecKey<T, StrategyWeight>> Strategy<T> for OrxStrategy<T, H> {
    fn extract_min(&mut self) -> Option<T> {
        self.0.pop().map(|(v, _)| v)
    }

    fn get_weight(&self, item: T) -> Option<StrategyWeight> {
        self.iter()
            .find(|StrategyItem(_, v)| *v == item)
            .map(|StrategyItem(weight, _)| weight)
    }
}

impl<T: Eq + Copy + Hash + Debug, H: PriorityQueueDecKey<T, StrategyWeight> + Debug>
    Intersect<HashSet<T>> for OrxStrategy<T, H>
{
    fn intersect(mut self, other: &HashSet<T>) -> Self {
        let to_remove: Vec<T> = self
            .0
            .iter()
            .filter_map(|x| {
                if other.contains(x.node()) {
                    None
                } else {
                    Some(*x.node())
                }
            })
            .collect();
        for v in to_remove {
            self.0.remove(&v);
        }
        self
    }
}

impl<T: Eq + Copy + Hash, H: PriorityQueueDecKey<T, StrategyWeight>> IntersectBy<T, Self>
    for OrxStrategy<T, H>
{
    fn intersect_by(
        mut self,
        other: &Self,
        f: impl Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    ) -> Self {
        let other_map: HashMap<_, _> = other.0.iter().map(|x| (*x.node(), *x.key())).collect();

        let items: Vec<(T, StrategyWeight)> =
            self.0.iter().map(|x| (*x.node(), *x.key())).collect();

        for (v, w) in items {
            if let Some(&w_other) = other_map.get(&v) {
                self.0.update_key(&v, f(w, w_other));
            } else {
                self.0.remove(&v);
            }
        }
        self
    }
}

impl<T: Copy + Eq + Hash, U: Copy + Eq + Hash, const D: usize> LeftSliced<T, U>
    for OrxStrategy<(T, U), DaryHeapWithMap<(T, U), StrategyWeight, D>>
{
    type SlicedLeft = OrxStrategy<U, DaryHeapWithMap<U, StrategyWeight, D>>;
}

impl<T: Copy + Eq + Hash, U: Copy + Eq + Hash, const D: usize> RightSliced<T, U>
    for OrxStrategy<(T, U), DaryHeapWithMap<(T, U), StrategyWeight, D>>
{
    type SlicedRight = OrxStrategy<T, DaryHeapWithMap<T, StrategyWeight, D>>;
}

impl<
    T: Copy + Eq + Hash,
    U: Copy + Eq + Hash,
    UH: PriorityQueueDecKey<U, StrategyWeight> + Default,
    PH: PriorityQueueDecKey<(T, U), StrategyWeight>,
> SliceLeft<T, U, OrxStrategy<U, UH>> for OrxStrategy<(T, U), PH>
where
    (T, U): Copy,
    Self: LeftSliced<T, U, SlicedLeft = OrxStrategy<U, UH>>,
{
    fn slice_left(self, left: T) -> OrxStrategy<U, UH> {
        // PERF: i would like to do this in-place, actually consuming the strategy
        let mut new = UH::default();
        for x in self.0.iter() {
            let (t, u) = x.node();
            if *t == left {
                new.push(*u, *x.key());
            }
        }
        OrxStrategy(new, PhantomData)
    }
}

impl<
    T: Copy + Eq + Hash,
    U: Copy + Eq + Hash,
    TH: PriorityQueueDecKey<T, StrategyWeight> + Default,
    PH: PriorityQueueDecKey<(T, U), StrategyWeight>,
> SliceRight<T, U, OrxStrategy<T, TH>> for OrxStrategy<(T, U), PH>
where
    (T, U): Copy,
    Self: RightSliced<T, U, SlicedRight = OrxStrategy<T, TH>>,
{
    fn slice_right(self, right: U) -> OrxStrategy<T, TH> {
        // PERF: i would like to do this in-place, actually consuming the strategy
        let mut new = TH::default();
        for x in self.0.iter() {
            let (t, u) = x.node();
            if *u == right {
                new.push(*t, *x.key());
            }
        }
        OrxStrategy(new, PhantomData)
    }
}

impl<T: Copy + Eq, S: FromIterator<T>, H: PriorityQueueDecKey<T, StrategyWeight>> Domain<T, S>
    for OrxStrategy<T, H>
{
    fn domain(self) -> S {
        self.0.iter().map(|x| *x.node()).collect()
    }
}

impl<T: Copy, H: PriorityQueueDecKey<T, StrategyWeight> + Default> Singleton<T>
    for OrxStrategy<T, H>
{
    fn singleton(x: T) -> Self {
        let mut s = Self::default();
        s.0.push(x, StrategyWeight::Infinity);
        s
    }
}

impl<T: Copy, H: PriorityQueueDecKey<T, StrategyWeight>> Length for OrxStrategy<T, H> {
    fn length(&self) -> usize {
        self.0.len()
    }
}

impl<T: Copy + Debug, H: PriorityQueueDecKey<T, StrategyWeight> + Debug> Extend<StrategyItem<T>>
    for OrxStrategy<T, H>
{
    fn extend<I: IntoIterator<Item = StrategyItem<T>>>(&mut self, iter: I) {
        for StrategyItem(w, v) in iter {
            self.0.push(v, w);
        }
    }
}

impl<T: Copy, H: PriorityQueueDecKey<T, StrategyWeight>> FromIterator<Reverse<StrategyItem<T>>>
    for OrxStrategy<T, H>
where
    Self: Default,
{
    fn from_iter<I: IntoIterator<Item = Reverse<StrategyItem<T>>>>(iter: I) -> Self {
        let mut new = Self::default();
        for Reverse(StrategyItem(w, v)) in iter {
            new.0.push(v, w);
        }
        new
    }
}

impl<T: Copy, H: PriorityQueueDecKey<T, StrategyWeight>> FromIterator<StrategyItem<T>>
    for OrxStrategy<T, H>
where
    Self: Default,
{
    fn from_iter<I: IntoIterator<Item = StrategyItem<T>>>(iter: I) -> Self {
        let mut new = Self::default();
        for StrategyItem(w, v) in iter {
            new.0.push(v, w);
        }
        new
    }
}

impl<T: Copy, H: PriorityQueueDecKey<T, StrategyWeight>> IntoIterator for OrxStrategy<T, H> {
    type Item = StrategyItem<T>;

    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        // PERF: avoid collecting into a vec. this currently isn't possible because none of the orx
        // priority queues have an `IntoIterator` implementation
        self.0
            .iter()
            .map(|x| StrategyItem(*x.key(), *x.node()))
            .collect::<Vec<_>>()
            .into_iter()
    }
}

impl<T: Copy, H: PriorityQueueDecKey<T, StrategyWeight>> IntoIterator for &OrxStrategy<T, H> {
    type Item = StrategyItem<T>;

    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        // PERF: avoid collecting into a vec. this currently isn't possible because none of the orx
        // priority queues have an `IntoIterator` implementation
        self.0.iter().map(|x| StrategyItem(*x.key(), *x.node()))
    }
}

impl<T: Clone, H: PriorityQueueDecKey<T, StrategyWeight>> ResetWeights for OrxStrategy<T, H> {
    fn reset_weights(&mut self) {
        let items: Vec<_> = self.iter().map(|x| x.node()).cloned().collect();

        for it in items {
            self.update_key(&it, StrategyWeight::Infinity);
        }
    }
}
