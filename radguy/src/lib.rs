#![feature(impl_trait_in_assoc_type)]

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

/// System of equations
pub trait System<VarKey: Copy, VarValue: PartialOrd> {
    /// Evaluates a variable w.r.t. a given assignment, returning the new value
    fn evaluate(&self, key: VarKey, assignment: &HashMap<VarKey, VarValue>) -> VarValue;
    /// The bottom element of the systems domain.
    ///
    /// # Example
    /// `true` for boolean domains, `0` or infinity for numeric systems.
    fn bottom_assignment(&self) -> HashMap<VarKey, VarValue>;

    /// Locks the system s.t. no changes can be made to the set of visited or discovered variables.
    fn lock(&mut self);

    /// Unlocks the system after `self.lock()`, allowing changes to the set of visited and
    /// discovered variables.
    fn unlock(&mut self);

    /// The set of visited variables. These are the variables for which an evaluation function is
    /// known.
    fn visited(&self) -> HashSet<VarKey>;
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

pub trait Assignment<K, V> {
    fn get_assignment(&self, key: &K) -> V;
    fn update_assignment(&mut self, key: K, value: V);
}

pub trait Arguments<VarKey, VarSet> {
    fn arguments(&self, key: VarKey) -> VarSet;
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
    fn get_assignment(&self, key: &K) -> V {
        self.get(key).cloned().unwrap_or_else(V::bottom)
    }

    fn update_assignment(&mut self, key: K, value: V) {
        self.insert(key, value);
    }
}

#[expect(clippy::similar_names)]
pub fn kleene_local<
    K: Copy + Hash + Eq + Debug,
    V: Eq + PartialOrd + Bottom + Clone,
    PS: Debug + Union,
    S: System<K, V> + Arguments<K, HashSet<K>> + Universe<HashSet<K>>,
>(
    system: &mut S,
    target: K,
    oracle: &impl LocalOracle<K, V, PS, S>,
) -> V
where
    for<'a> &'a PS: IntoIterator<Item = &'a (K, K)>,
    HashSet<K>: Cartesian<Output = PS>,
{
    let mut assignment = system.bottom_assignment();
    let mut discovered = system.universe();
    let mut rel = discovered.cartesian(&discovered);
    // PERF: This should run the oracle instead of using the full universe
    let mut todo = local_dependencies(target, &discovered, &assignment, oracle, system, &mut rel);
    if todo.is_empty() {
        todo.push(target);
    }
    let mut iter = todo.iter();
    while let Some(&x) = iter.next() {
        let evaluated = system.evaluate(x, &assignment);
        let args = system.arguments(x);
        if assignment.get_assignment(&x) != evaluated || !args.is_subset(&discovered) {
            assignment.update_assignment(x, evaluated);
            // At this point `rel` is D x D with some elements pruned by oracles
            // We expand it with args to create (D u A) x (D u A), still with those elements
            // pruned, by unioning with the elements of the square below.
            // +-------------+-------+
            // | A x D       | A x A |
            // +-------------+-------+
            // | D x D (rel) | D x A |
            // +-------------+-------+
            let axa = args.cartesian(&args);
            let axd = args.cartesian(&discovered);
            let dxa = discovered.cartesian(&args);
            rel = rel.union(axa).union(axd).union(dxa);
            discovered = system.universe();
            todo = local_dependencies(target, &discovered, &assignment, oracle, system, &mut rel);
            iter = todo.iter();
        }
    }

    assignment.get_assignment(&target)
}

fn local_dependencies<K: Hash + Copy + Eq, V: PartialOrd, PS: Debug, S: System<K, V>>(
    variable: K,
    discovered: &HashSet<K>,
    assignment: &HashMap<K, V>,
    oracle: &impl LocalOracle<K, V, PS, S>,
    system: &mut S,
    rel: &mut PS,
) -> Vec<K>
where
    for<'a> &'a PS: IntoIterator<Item = &'a (K, K)>,
{
    system.lock();
    *rel = oracle.approximate_flow(assignment, rel, system);
    system.unlock();
    rel.into_iter()
        .copied()
        .filter_map(|(x, y)| if y == variable { Some(x) } else { None })
        .filter(|x| discovered.contains(x))
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
