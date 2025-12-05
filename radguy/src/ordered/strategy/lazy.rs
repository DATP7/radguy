use crate::{
    ordered::strategy::{GetWeight, ResetWeights}, CopiedIter, Intersect, Union
};
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use crate::ordered::strategy::{
    Domain, IntersectBy, LeftSliced, Length, Retain, RightSliced, Singleton, SliceLeft, SliceRight,
    Strategy, StrategyItem, StrategyWeight, UnionWithBy,
};

/// A strategy that only builds the heap when the minimum item needs to be extracted
#[derive(Default, Clone, Debug)]
pub struct LazyHeap<T, H> {
    items: HashMap<T, StrategyWeight>,
    heap: Option<H>,
}

impl<T, H> LazyHeap<T, H> {
    fn items_mut(&mut self) -> &mut HashMap<T, StrategyWeight> {
        self.heap = None;
        &mut self.items
    }
    pub fn iter(&self) -> impl Iterator<Item = StrategyItem<T>>
    where
        T: Copy,
    {
        self.into_iter()
    }
}

impl<T: Copy + Eq, H: FromIterator<StrategyItem<T>> + Strategy<T>> Strategy<T> for LazyHeap<T, H> {
    fn extract_min(&mut self) -> Option<T> {
        self.heap
            .get_or_insert_with(|| {
                self.items
                    .iter()
                    .map(|(v, w)| StrategyItem(*w, *v))
                    .collect()
            })
            .extract_min()
    }
}

impl<T: Eq + Hash, H> GetWeight<T> for LazyHeap<T, H> {
    fn get_weight(&self, item: T) -> Option<StrategyWeight> {
        self.items.get(&item).copied()
    }
}

impl<T: Hash + Eq, H: FromIterator<StrategyItem<T>>> FromIterator<StrategyItem<T>>
    for LazyHeap<T, H>
{
    fn from_iter<I: IntoIterator<Item = StrategyItem<T>>>(iter: I) -> Self {
        Self {
            items: iter.into_iter().map(|StrategyItem(w, v)| (v, w)).collect(),
            heap: None,
        }
    }
}

impl<T, H> IntoIterator for LazyHeap<T, H> {
    type Item = StrategyItem<T>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.into_iter().map(|(v, w)| StrategyItem(w, v))
    }
}

impl<T: Copy, H> IntoIterator for &LazyHeap<T, H> {
    type Item = StrategyItem<T>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.items.iter().map(|(v, w)| StrategyItem(*w, *v))
    }
}

impl<T: Hash + Eq, H> Intersect<HashSet<T>> for LazyHeap<T, H> {
    fn intersect(mut self, other: &HashSet<T>) -> Self {
        self.items_mut().retain(|v, _| other.contains(v));
        self
    }
}
impl<T: Hash + Eq + Copy, H: FromIterator<StrategyItem<T>> + Strategy<T>> IntersectBy<T>
    for LazyHeap<T, H>
{
    fn intersect_by(
        mut self,
        other: &Self,
        f: impl Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    ) -> Self {
        self.items_mut().retain(|v, w| {
            other.items.get(v).is_some_and(|w_other| {
                *w = f(*w, *w_other);
                true
            })
        });
        self
    }
}

impl<T: Eq + Hash, H> Union for LazyHeap<T, H> {
    fn union(mut self, other: Self) -> Self {
        self.items_mut().extend(other.items);
        self
    }
}

impl<T: Eq + Hash + Copy, H: FromIterator<StrategyItem<T>> + Strategy<T>> UnionWithBy<T, Self>
    for LazyHeap<T, H>
{
    fn union_with_by(
        &mut self,
        mut other: Self,
        f: impl Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    ) {
        let mut to_add = Vec::new();
        self.items_mut().retain(|v, w| {
            other.items.remove(v).is_none_or(|w_other| {
                to_add.push(StrategyItem(f(*w, w_other), *v));
                false
            })
        });
        self.extend(
            to_add
                .into_iter()
                .chain(other.items.iter().map(|(v, w)| StrategyItem(*w, *v))),
        );
    }
}

impl<T: Hash + Eq, H> Singleton<T> for LazyHeap<T, H> {
    fn singleton(x: T) -> Self {
        Self {
            items: HashMap::from([(x, StrategyWeight::Infinity)]),
            heap: None,
        }
    }
}

impl<
    T: Hash + Eq + Copy,
    U: Eq + Copy,
    TH: FromIterator<StrategyItem<T>> + Strategy<T>,
    PH: FromIterator<StrategyItem<(T, U)>> + Strategy<(T, U)> + RightSliced<T, U, SlicedRight = TH>,
> RightSliced<T, U> for LazyHeap<(T, U), PH>
{
    type SlicedRight = LazyHeap<T, TH>;
}

impl<
    T: Hash + Eq + Copy,
    U: Eq + Copy,
    TH: FromIterator<StrategyItem<T>> + Strategy<T>,
    PH: FromIterator<StrategyItem<(T, U)>> + Strategy<(T, U)> + RightSliced<T, U, SlicedRight = TH>,
> SliceRight<T, U, LazyHeap<T, TH>> for LazyHeap<(T, U), PH>
{
    fn slice_right(&self, right: U) -> LazyHeap<T, TH> {
        let items = self
            .items
            .iter()
            .filter_map(|((t, u), w)| if *u == right { Some((*t, *w)) } else { None })
            .collect();
        LazyHeap { items, heap: None }
    }
}

impl<
    T: Hash + Eq + Copy,
    U: Eq + Copy,
    UH: FromIterator<StrategyItem<U>> + Strategy<U>,
    PH: FromIterator<StrategyItem<(T, U)>> + Strategy<(T, U)> + LeftSliced<T, U, SlicedLeft = UH>,
> LeftSliced<T, U> for LazyHeap<(T, U), PH>
{
    type SlicedLeft = LazyHeap<U, UH>;
}

impl<
    T: Hash + Eq + Copy,
    U: Hash + Eq + Copy,
    UH: FromIterator<StrategyItem<U>> + Strategy<U>,
    PH: FromIterator<StrategyItem<(T, U)>> + Strategy<(T, U)> + LeftSliced<T, U, SlicedLeft = UH>,
> SliceLeft<T, U, LazyHeap<U, UH>> for LazyHeap<(T, U), PH>
{
    fn slice_left(&self, left: T) -> LazyHeap<U, UH> {
        let items = self
            .items
            .iter()
            .filter_map(|((t, u), w)| if *t == left { Some((*u, *w)) } else { None })
            .collect();
        LazyHeap { items, heap: None }
    }
}

impl<T: Hash + Eq + Copy, H: FromIterator<StrategyItem<T>> + Strategy<T>, D: FromIterator<T>>
    Domain<T, D> for LazyHeap<T, H>
{
    fn domain(self) -> D {
        self.items.into_keys().collect()
    }
}

impl<T, H> Length for LazyHeap<T, H> {
    fn length(&self) -> usize {
        self.items.len()
    }
}

impl<T: Copy, H> Retain<T> for LazyHeap<T, H> {
    fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&StrategyItem<T>) -> bool,
    {
        self.items_mut().retain(|v, w| f(&StrategyItem(*w, *v)));
    }
}

impl<T: Hash + Eq, H> Extend<StrategyItem<T>> for LazyHeap<T, H> {
    fn extend<I: IntoIterator<Item = StrategyItem<T>>>(&mut self, iter: I) {
        self.items_mut()
            .extend(iter.into_iter().map(|StrategyItem(w, v)| (v, w)));
    }
}

impl<'a, T: Copy + 'a, H: 'a> CopiedIter<'a, StrategyItem<T>> for LazyHeap<T, H> {
    type IterCopied = impl Iterator<Item = StrategyItem<T>>;

    fn copied_iter(&'a self) -> Self::IterCopied {
        self.items.iter().map(|(v, w)| StrategyItem(*w, *v))
    }
}

impl<T, H> ResetWeights for LazyHeap<T, H> {
    fn reset_weights(&mut self) {
        for v in self.items_mut().values_mut() {
            *v = StrategyWeight::Infinity;
        }
    }
}
