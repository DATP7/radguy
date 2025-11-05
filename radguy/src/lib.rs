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
pub mod ordered;

pub trait Set<T> {
    fn contains(&self, item: &T) -> bool;
    fn insert(&mut self, item: T) -> bool;
}

pub trait Union<Other = Self> {
    #[must_use]
    fn union(self, other: Other) -> Self;
}

pub trait Intersect<Other = Self> {
    #[must_use]
    fn intersect(self, other: &Other) -> Self;
}

pub trait Without<Other = Self> {
    #[must_use]
    fn without(self, other: &Other) -> Self;
}

pub trait IsSubset<Other = Self> {
    fn is_subset(&self, other: &Other) -> bool;
}

pub trait Cartesian<Rhs = Self> {
    type Output;
    /// Returns the Cartesian product of two sets.
    /// (a, b) for a in self, b in other.
    fn cartesian(&self, other: &Rhs) -> Self::Output;
}

pub trait Diagonal {
    type Output;
    /// Returns the reflexive relation of elements on a set
    /// i.e. diagonal({x}) = {(x,x)}
    fn diagonal(&self) -> Self::Output;
}

pub trait Universe<S> {
    /// Returns a structure S containing all variables in the system
    #[must_use]
    fn universe(&self) -> S;
}

pub trait PairUniverse<S> {
    /// Returns the cartesian product of all the variables, $VV times VV$
    #[must_use]
    fn pair_universe(&self) -> S;
}

pub trait System<VarKey: Copy, VarValue: PartialOrd> {
    fn evaluate(&self, key: VarKey, assignment: &dyn Assignment<VarKey, VarValue>) -> VarValue;
    fn bottom_assignment(&self) -> impl Assignment<VarKey, VarValue>;
}

pub trait Arguments<VarKey, VarSet> {
    fn arguments(&self, key: VarKey) -> VarSet;
}

pub trait Assignment<K, V> {
    fn get(&self, key: &K) -> V;
    fn update(&mut self, key: K, value: V);
}

impl<T: Eq + Hash, S: ::std::hash::BuildHasher + Default> Set<T> for HashSet<T, S> {
    fn insert(&mut self, item: T) -> bool {
        Self::insert(self, item)
    }

    fn contains(&self, item: &T) -> bool {
        self.contains(item)
    }
}

impl<T: Eq + Hash, S: ::std::hash::BuildHasher + Default> Union<Self> for HashSet<T, S> {
    fn union(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<T: Eq + Hash + Copy, S: ::std::hash::BuildHasher + Default> Intersect<Self> for HashSet<T, S> {
    fn intersect(self, other: &Self) -> Self {
        self.intersection(other).copied().collect()
    }
}

impl<T: Eq + Hash, S: ::std::hash::BuildHasher + Default> IsSubset<Self> for HashSet<T, S> {
    fn is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<T: Eq + Hash + Copy, S: ::std::hash::BuildHasher + Default> Without<Self> for HashSet<T, S> {
    fn without(self, other: &Self) -> Self {
        self.difference(other).copied().collect()
    }
}

impl<T: Eq + Hash + Copy, S: ::std::hash::BuildHasher> Cartesian for HashSet<T, S> {
    type Output = HashSet<(T, T)>;

    fn cartesian(&self, other: &Self) -> Self::Output {
        iproduct!(self.iter().copied(), other.iter().copied()).collect()
    }
}

impl<T: Eq + Hash + Copy, S: ::std::hash::BuildHasher> Diagonal for HashSet<T, S> {
    type Output = HashSet<(T, T)>;

    fn diagonal(&self) -> Self::Output {
        self.iter().copied().map(|x| (x, x)).collect()
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
    PS,
    VS: Set<K> + Union + IsSubset + FromIterator<K>,
    S: System<K, V> + PairUniverse<PS> + Arguments<K, VS>,
>(
    system: &S,
    target: K,
    oracle: &impl LocalOracle<K, V, VS, PS, S>,
) -> V
where
    for<'a> &'a PS: IntoIterator<Item = &'a (K, K)>,
{
    let mut assignment = system.bottom_assignment();
    let mut visited = std::iter::once(target).collect();
    let mut rel = system.pair_universe();
    let mut todo = local_dependencies(target, &visited, &assignment, oracle, system, &mut rel);
    let mut iter = todo.iter();
    while let Some(&x) = iter.next() {
        let evaluated = system.evaluate(x, &assignment);
        if assignment.get(&x) != evaluated || !system.arguments(x).is_subset(&visited) {
            assignment.update(x, evaluated);
            visited = visited.union(system.arguments(x));
            todo = local_dependencies(target, &visited, &assignment, oracle, system, &mut rel);
            iter = todo.iter();
        }
    }

    assignment.get(&target)
}

fn local_dependencies<K: Hash + Copy + Eq, V: PartialOrd, VS: Set<K>, PS, S: System<K, V>>(
    variable: K,
    visited: &VS,
    assignment: &impl Assignment<K, V>,
    oracle: &impl LocalOracle<K, V, VS, PS, S>,
    system: &S,
    rel: &mut PS,
) -> Vec<K>
where
    for<'a> &'a PS: IntoIterator<Item = &'a (K, K)>,
{
    *rel = oracle.approximate_flow(visited, assignment, rel, system);
    rel.into_iter()
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
