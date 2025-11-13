use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
    ops::{Deref, DerefMut},
};

use crate::ordered::strategy::{
    Domain, Intersect, IntersectBy, Length, Retain, Singleton, SliceLeft, SliceRight, Strategy,
    StrategyItem, StrategyWeight,
};

#[derive(Default, Clone, Debug)]
pub struct HashMapStrategy<T>(HashMap<T, StrategyWeight>);

impl<T: Copy> HashMapStrategy<T> {
    pub fn iter(&self) -> impl Iterator<Item = StrategyItem<T>> + '_
    where
        StrategyItem<T>: Copy,
    {
        self.0.iter().map(|(v, w)| StrategyItem(*w, *v))
    }
}

impl<T> Deref for HashMapStrategy<T> {
    type Target = HashMap<T, StrategyWeight>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for HashMapStrategy<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: Eq + Hash> FromIterator<StrategyItem<T>> for HashMapStrategy<T> {
    fn from_iter<I: IntoIterator<Item = StrategyItem<T>>>(iter: I) -> Self {
        Self(iter.into_iter().map(|StrategyItem(w, v)| (v, w)).collect())
    }
}

impl<T> IntoIterator for HashMapStrategy<T> {
    type Item = StrategyItem<T>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().map(|(v, w)| StrategyItem(w, v))
    }
}

impl<T: Copy> IntoIterator for &HashMapStrategy<T> {
    type Item = StrategyItem<T>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(|(v, w)| StrategyItem(*w, *v))
    }
}

impl<T: Copy + Eq + Hash> Strategy<T> for HashMapStrategy<T> {
    fn extract_min(&mut self) -> Option<T> {
        let key = self.0.iter().min_by_key(|(_, w)| **w).map(|(v, _)| *v);
        if let Some(key) = key {
            self.0.remove(&key);
        }
        key
    }
}

impl<T: Eq + Copy + Hash> Intersect<T, HashSet<T>> for HashMapStrategy<T> {
    fn intersect(mut self, other: &HashSet<T>) -> Self {
        self.0.retain(|v, _| other.contains(v));
        self
    }
}

impl<T: Eq + Copy + Hash> IntersectBy<T, Self> for HashMapStrategy<T> {
    fn intersect_by(
        mut self,
        other: &Self,
        f: impl Fn(StrategyWeight, StrategyWeight) -> StrategyWeight,
    ) -> Self {
        self.0.retain(|v, w| {
            other.get(v).is_some_and(|w_other| {
                *w = f(*w, *w_other);
                true
            })
        });
        self
    }
}

impl<T: Eq + Hash, U: Copy + Eq + Hash> SliceLeft<T, U, HashMapStrategy<U>>
    for HashMapStrategy<(T, U)>
where
    (T, U): Copy,
{
    fn slice_left(self, left: T) -> HashMapStrategy<U> {
        let heap = self
            .0
            .into_iter()
            .filter_map(|((t, u), v)| if t == left { Some((u, v)) } else { None })
            .collect();
        HashMapStrategy(heap)
    }
}

impl<T: Copy + Hash + Eq, U: Eq + Hash> SliceRight<T, U, HashMapStrategy<T>>
    for HashMapStrategy<(T, U)>
where
    (T, U): Copy,
{
    fn slice_right(self, right: U) -> HashMapStrategy<T> {
        let heap = self
            .0
            .into_iter()
            .filter_map(|((t, u), v)| if u == right { Some((t, v)) } else { None })
            .collect();
        HashMapStrategy(heap)
    }
}

impl<T: Copy + Eq + Hash, S: FromIterator<T>> Domain<T, S> for HashMapStrategy<T> {
    fn domain(self) -> S {
        self.0.into_keys().collect()
    }
}

impl<T: Copy + Eq + Hash> Singleton<T> for HashMapStrategy<T> {
    fn singleton(x: T) -> Self {
        Self(HashMap::from_iter([(x, StrategyWeight::Infinity)]))
    }
}

impl<T: Copy> Length for HashMapStrategy<T> {
    fn length(&self) -> usize {
        self.len()
    }
}

impl<T: Copy> Retain<T> for HashMapStrategy<T> {
    fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&StrategyItem<T>) -> bool,
    {
        self.0.retain(|v, w| f(&StrategyItem(*w, *v)));
    }
}

impl<T: Copy + Eq + Hash> Extend<StrategyItem<T>> for HashMapStrategy<T> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = StrategyItem<T>>,
    {
        self.0
            .extend(iter.into_iter().map(|StrategyItem(w, v)| (v, w)));
    }
}

#[cfg(test)]
mod tests {
    use crate::ordered::strategy::{HashMapStrategy, Singleton, Strategy, StrategyWeight};

    #[test]
    fn extract_from_empty() {
        let mut s = HashMapStrategy::<usize>::default();
        assert_eq!(None, s.extract_min());
    }

    #[test]
    fn extract_single() {
        let mut s = HashMapStrategy::singleton(0);
        assert_eq!(Some(0), s.extract_min());
        assert_eq!(None, s.extract_min());
    }

    #[test]
    fn extract_from_number_infinity() {
        let mut s = HashMapStrategy::singleton(0);
        s.insert(1, StrategyWeight::Num(0));
        assert_eq!(Some(1), s.extract_min());
        assert_eq!(Some(0), s.extract_min());
        assert_eq!(None, s.extract_min());
    }

    #[test]
    fn extract_from_two_numbers() {
        let mut s = HashMapStrategy::default();
        s.insert(0, StrategyWeight::Num(10));
        s.insert(1, StrategyWeight::Num(0));
        assert_eq!(Some(1), s.extract_min());
        assert_eq!(Some(0), s.extract_min());
        assert_eq!(None, s.extract_min());
    }
}
