use itertools::iproduct;
use std::fmt::Debug;

use crate::oracle::LocalOracle;
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

pub mod bislotmap;
pub mod extension;
pub mod oracle;

pub trait Set<T> {
    #[must_use]
    fn intersect(&self, other: Self) -> Self;
    #[must_use]
    fn union(&self, other: Self) -> Self;
    #[must_use]
    fn without(&self, _other: &Self) -> Self;
    fn contains(&self, item: &T) -> bool;
    fn is_subset(&self, other: &Self) -> bool;
}

pub trait Cartesian<Rhs = Self> {
    type Output;
    /// Returns the Cartesian product of two sets.
    /// (a, b) for a in self, b in other.
    fn cartesian(&self, other: &Rhs) -> Self::Output;
}

pub trait IterSet: Set<Self::Item> {
    type Item;
    type Iter<'a>: Iterator<Item = &'a Self::Item>
    where
        Self: 'a;
    fn iter(&self) -> Self::Iter<'_>;
}

pub trait System<
    VarKey: Copy,
    VarValue: PartialOrd,
    PairSet: IterSet<Item = (VarKey, VarKey)>,
    VarSet: IterSet<Item = VarKey>,
>
{
    fn evaluate(&self, key: VarKey, assignment: &dyn Assignment<VarKey, VarValue>) -> VarValue;

    fn arguments(&self, key: VarKey) -> VarSet;
    fn variables(&self) -> VarSet;
    fn bottom_assignment(&self) -> impl Assignment<VarKey, VarValue>;
}

pub trait Assignment<K, V> {
    fn get(&self, key: &K) -> V;
    fn update(&mut self, key: K, value: V);
}

impl<T: Eq + Hash + Copy, S: ::std::hash::BuildHasher + Default> Set<T> for HashSet<T, S> {
    fn intersect(&self, other: Self) -> Self {
        self.intersection(&other).copied().collect()
    }

    fn union(&self, other: Self) -> Self {
        self.union(&other).copied().collect()
    }

    fn is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }

    fn contains(&self, item: &T) -> bool {
        self.contains(item)
    }

    fn without(&self, other: &Self) -> Self {
        self.difference(other).copied().collect()
    }
}

impl<T: Eq + Hash + Copy, S: ::std::hash::BuildHasher + Default> IterSet for HashSet<T, S> {
    type Item = T;
    type Iter<'a>
        = std::collections::hash_set::Iter<'a, T>
    where
        T: 'a,
        Self: 'a;

    fn iter(&self) -> Self::Iter<'_> {
        self.iter()
    }
}

impl<T: Eq + Hash + Copy, S: ::std::hash::BuildHasher> Cartesian for HashSet<T, S> {
    type Output = HashSet<(T, T)>;

    fn cartesian(&self, other: &Self) -> Self::Output {
        iproduct!(self.iter().copied(), other.iter().copied()).collect()
    }
}

impl<K: Hash + Eq, V: Bottom + Clone, S: std::hash::BuildHasher> Assignment<K, V>
    for HashMap<K, V, S>
{
    fn get(&self, key: &K) -> V {
        self.get(key).cloned().unwrap_or_else(V::bottom)
    }

    fn update(&mut self, key: K, value: V) {
        self.insert(key, value);
    }
}

pub fn kleene_local<
    K: Copy + Hash + Eq + Debug,
    V: Eq + PartialOrd,
    PS: IterSet<Item = (K, K)>,
    VS: IterSet<Item = K> + Cartesian<Output = PS> + FromIterator<K>,
    S: System<K, V, PS, VS>,
>(
    system: &S,
    target: K,
    oracle: &impl LocalOracle<K, V, PS, VS, S>,
) -> V {
    let mut assignment = system.bottom_assignment();
    let mut visited = std::iter::once(target).collect();
    let mut todo = local_dependencies(target, &visited, &assignment, oracle, system);
    let mut iter = todo.iter();
    while let Some(&x) = iter.next() {
        let evaluated = system.evaluate(x, &assignment);
        if assignment.get(&x) != evaluated || !system.arguments(x).is_subset(&visited) {
            assignment.update(x, evaluated);
            visited = visited.union(system.arguments(x));
            todo = local_dependencies(target, &visited, &assignment, oracle, system);
            iter = todo.iter();
        }
    }

    assignment.get(&target)
}

fn local_dependencies<
    K: Copy + Hash + Eq,
    V: PartialOrd,
    PS: IterSet<Item = (K, K)>,
    VS: IterSet<Item = K> + Cartesian<Output = PS>,
    S: System<K, V, PS, VS>,
>(
    variable: K,
    visited: &VS,
    assignment: &impl Assignment<K, V>,
    oracle: &impl LocalOracle<K, V, PS, VS, S>,
    system: &S,
) -> Vec<K> {
    let product = &system.variables().cartesian(&system.variables());
    let d = oracle.approximate_flow(visited, assignment, product, system);
    d.iter()
        .copied()
        .filter_map(|(x, y)| if y == variable { Some(x) } else { None })
        .filter(|x| visited.contains(x))
        .collect()
}

pub trait Maximal: PartialOrd {
    fn is_maximal(&self) -> bool;
}

impl Maximal for bool {
    fn is_maximal(&self) -> bool {
        *self
    }
}

pub trait Bottom: PartialOrd {
    fn bottom() -> Self;
}

impl Bottom for bool {
    fn bottom() -> Self {
        false
    }
}

#[cfg(test)]
mod tests {}
