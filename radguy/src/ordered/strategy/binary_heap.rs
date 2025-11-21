use crate::{Intersect, ordered::strategy::ConstantStrategy};
use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap, HashSet},
    hash::Hash,
    ops::{Deref, DerefMut},
};

use crate::ordered::strategy::{
    Domain, IntersectBy, LeftSliced, Length, Retain, RightSliced, Singleton, SliceLeft, SliceRight,
    Strategy, StrategyItem, StrategyWeight,
};

#[derive(Default, Clone, Debug)]
pub struct BinaryHeapStrategy<T>(BinaryHeap<Reverse<StrategyItem<T>>>);

impl<T> BinaryHeapStrategy<T> {
    pub fn iter(&self) -> impl Iterator<Item = StrategyItem<T>> + '_
    where
        StrategyItem<T>: Copy,
    {
        self.into_iter()
    }
}

impl<T> Deref for BinaryHeapStrategy<T> {
    type Target = BinaryHeap<Reverse<StrategyItem<T>>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for BinaryHeapStrategy<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> FromIterator<StrategyItem<T>> for BinaryHeapStrategy<T> {
    fn from_iter<I: IntoIterator<Item = StrategyItem<T>>>(iter: I) -> Self {
        Self(iter.into_iter().map(Reverse).collect())
    }
}

impl<T> FromIterator<Reverse<StrategyItem<T>>> for BinaryHeapStrategy<T> {
    fn from_iter<I: IntoIterator<Item = Reverse<StrategyItem<T>>>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<T> IntoIterator for BinaryHeapStrategy<T> {
    type Item = StrategyItem<T>;
    type IntoIter = impl Iterator<Item = Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().map(|Reverse(i)| i)
    }
}

impl<T> IntoIterator for &BinaryHeapStrategy<T>
where
    StrategyItem<T>: Copy,
{
    type Item = StrategyItem<T>;
    type IntoIter = impl Iterator<Item = Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(|Reverse(i)| i).copied()
    }
}

impl<T: Copy> Strategy<T> for BinaryHeapStrategy<T> {
    fn extract_min(&mut self) -> Option<T> {
        self.pop().map(|Reverse(StrategyItem(_, v))| v)
    }
}

impl<T: Copy> ConstantStrategy<T> for BinaryHeapStrategy<T> {}

impl<T: Eq + Copy + Hash> Intersect<HashSet<T>> for BinaryHeapStrategy<T> {
    fn intersect(mut self, other: &HashSet<T>) -> Self {
        self.0
            .retain(|Reverse(StrategyItem(_, v))| other.contains(v));
        self
    }
}

impl<T: Eq + Copy + Hash> IntersectBy<T, Self> for BinaryHeapStrategy<T> {
    fn intersect_by(
        self,
        other: &Self,
        f: impl Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    ) -> Self {
        let other_map: HashMap<_, _> = other
            .0
            .iter()
            .map(|Reverse(StrategyItem(w, v))| (v, w))
            .collect();
        let heap = self
            .0
            .into_iter()
            .filter_map(|Reverse(StrategyItem(w_self, v))| {
                other_map
                    .get(&v)
                    .map(|&w_other| Reverse(StrategyItem(f(w_self, *w_other), v)))
            })
            .collect();
        Self(heap)
    }
}

impl<T, U: Copy> LeftSliced<T, U> for BinaryHeapStrategy<(T, U)>
where
    (T, U): Copy,
{
    type SlicedLeft = BinaryHeapStrategy<U>;
}

impl<T: Copy, U> RightSliced<T, U> for BinaryHeapStrategy<(T, U)>
where
    (T, U): Copy,
{
    type SlicedRight = BinaryHeapStrategy<T>;
}

impl<T: Eq, U: Copy> SliceLeft<T, U, BinaryHeapStrategy<U>> for BinaryHeapStrategy<(T, U)>
where
    (T, U): Copy,
{
    fn slice_left(self, left: T) -> BinaryHeapStrategy<U> {
        let heap = self
            .0
            .into_iter()
            .filter_map(|Reverse(StrategyItem(w, (t, u)))| {
                if t == left {
                    Some(Reverse(StrategyItem(w, u)))
                } else {
                    None
                }
            })
            .collect();
        BinaryHeapStrategy(heap)
    }
}

impl<T: Copy, U: Eq> SliceRight<T, U, BinaryHeapStrategy<T>> for BinaryHeapStrategy<(T, U)>
where
    (T, U): Copy,
{
    fn slice_right(self, right: U) -> BinaryHeapStrategy<T> {
        let heap = self
            .0
            .into_iter()
            .filter_map(|Reverse(StrategyItem(w, (t, u)))| {
                if u == right {
                    Some(Reverse(StrategyItem(w, t)))
                } else {
                    None
                }
            })
            .collect();
        BinaryHeapStrategy(heap)
    }
}

impl<T: Copy, S: FromIterator<T>> Domain<T, S> for BinaryHeapStrategy<T> {
    fn domain(self) -> S {
        self.0
            .into_iter()
            .map(|Reverse(StrategyItem(_, v))| v)
            .collect()
    }
}

impl<T: Copy> Singleton<T> for BinaryHeapStrategy<T> {
    fn singleton(x: T) -> Self {
        Self::from_iter([Reverse(StrategyItem(StrategyWeight::Infinity, x))])
    }
}

impl<T: Copy> Length for BinaryHeapStrategy<T> {
    fn length(&self) -> usize {
        self.len()
    }
}

impl<T: Copy> Retain<T> for BinaryHeapStrategy<T> {
    fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&StrategyItem<T>) -> bool,
    {
        self.0.retain(|Reverse(v)| f(v));
    }
}

impl<T: Copy> Extend<StrategyItem<T>> for BinaryHeapStrategy<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = StrategyItem<T>>,
    {
        self.0.extend(iter.into_iter().map(Reverse));
    }
}
