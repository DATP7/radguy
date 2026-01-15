#![feature(impl_trait_in_assoc_type)]

use itertools::iproduct;
use std::fmt::Debug;

use crate::oracle::LocalOracle;
use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

pub mod arena;
pub mod extension;
pub mod oracle;
pub mod ordered;
pub mod set;

#[cfg(feature = "timeout")]
pub const KLEENE_TIMEOUT: chrono::TimeDelta = chrono::TimeDelta::minutes(2);

pub trait Extract<T> {
    /// Extracts an arbitrary element from the set and removes it.
    fn extract(&mut self) -> Option<T>;
}

pub trait Set<T> {
    fn contains(&self, item: &T) -> bool;
    fn insert(&mut self, item: T) -> bool;
    fn len(&self) -> usize;
    fn remove(&mut self, x: &T) -> bool;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

pub trait Union<Other = Self> {
    #[must_use]
    fn union(self, other: Other) -> Self;
}

pub trait UnionWith<Other = Self> {
    fn union_with(&mut self, other: Other);
}

pub trait Intersect<Other = Self> {
    #[must_use]
    fn intersect(self, other: &Other) -> Self;
}

pub trait IntersectWith<Other = Self> {
    fn intersect_with(&mut self, other: &Other);
}

pub trait Without<Other = Self> {
    #[must_use]
    fn without(self, other: &Other) -> Self;
}

pub trait DifferenceWith<Other = Self> {
    fn difference_with(&mut self, other: &Other);
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
pub trait System<VarKey, VarValue: PartialOrd> {
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
}

pub trait Visited<S> {
    /// The set of visited variables. These are the variables for which an evaluation function is
    /// known.
    fn visited(&self) -> S;
}

pub trait Universe<S> {
    /// Returns a structure S containing all discovered variables in the system
    #[must_use]
    fn universe(&self) -> S;
}

pub trait PairUniverse<S> {
    /// Returns the cartesian product of all the variables, $VV times VV$
    #[must_use]
    fn pair_universe(&self) -> S;
}

pub trait DependencyGraphSystem<VarKey, ReturnType> {
    /// Get hyperedges of a variable if expanded, otherwise None
    fn get_hyperedges(&self, key: VarKey) -> Option<Vec<Vec<ReturnType>>>;
}

// See `ordered::strategy::LeftSliced` for explanation of why we have `LeftSliced` and
// `RightSliced`
pub trait LeftSliced<T, U>: Set<(T, U)> {
    type SlicedLeft: Set<U>;
}

pub trait RightSliced<T, U>: Set<(T, U)> {
    type SlicedRight: Set<T>;
}

pub trait SliceLeft<T: Eq, U, S>: Set<(T, U)> + LeftSliced<T, U, SlicedLeft = S>
where
    Self: Sized,
{
    /// Get a set where all values are of the form `(left, x)`
    fn slice_left(&self, left: T) -> S;
}

pub trait SliceRight<T, U: Eq, S>: Set<(T, U)> + RightSliced<T, U, SlicedRight = S>
where
    Self: Sized,
{
    /// Get a set where all values are of the form `(x, right)`
    fn slice_right(&self, right: U) -> S;
}

pub trait FromRights<TS, U> {
    fn from_rights(it: impl IntoIterator<Item = (TS, U)>) -> Self;
}

pub trait FromLefts<T, US> {
    fn from_lefts(it: impl IntoIterator<Item = (T, US)>) -> Self;
}

pub trait CopiedIter<'a, T: Copy> {
    type IterCopied: Iterator<Item = T> + 'a;

    fn copied_iter(&'a self) -> Self::IterCopied;
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

    fn remove(&mut self, x: &T) -> bool {
        self.remove(x)
    }

    fn len(&self) -> usize {
        self.len()
    }

    fn is_empty(&self) -> bool {
        self.is_empty()
    }
}

impl<T: Eq + Hash, S: ::std::hash::BuildHasher + Default> Union<Self> for HashSet<T, S> {
    fn union(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<T: Eq + Hash, S: ::std::hash::BuildHasher + Default> UnionWith<Self> for HashSet<T, S> {
    fn union_with(&mut self, other: Self) {
        self.extend(other);
    }
}

impl<'a, T: Eq + Hash + Clone, S: ::std::hash::BuildHasher + Default> Union<&'a Self>
    for HashSet<T, S>
{
    fn union(mut self, other: &'a Self) -> Self {
        self.extend(other.iter().cloned());
        self
    }
}

impl<'a, T: Eq + Hash + Clone, S: ::std::hash::BuildHasher + Default> UnionWith<&'a Self>
    for HashSet<T, S>
{
    fn union_with(&mut self, other: &'a Self) {
        self.extend(other.iter().cloned());
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

impl<T: Eq + Hash + Copy, U: Eq + Hash + Copy, S: ::std::hash::BuildHasher + Default>
    LeftSliced<T, U> for HashSet<(T, U), S>
{
    type SlicedLeft = HashSet<U, S>;
}

impl<T: Eq + Hash + Copy, U: Eq + Hash + Copy, S: ::std::hash::BuildHasher + Default>
    RightSliced<T, U> for HashSet<(T, U), S>
{
    type SlicedRight = HashSet<T, S>;
}

impl<T: Eq + Hash + Copy, U: Eq + Hash + Copy, S: ::std::hash::BuildHasher + Default>
    SliceLeft<T, U, HashSet<U, S>> for HashSet<(T, U), S>
{
    fn slice_left(&self, left: T) -> HashSet<U, S> {
        self.iter()
            .filter_map(|(t, u)| if *t == left { Some(*u) } else { None })
            .collect()
    }
}

impl<T: Eq + Hash + Copy, U: Eq + Hash + Copy, S: ::std::hash::BuildHasher + Default>
    SliceRight<T, U, HashSet<T, S>> for HashSet<(T, U), S>
{
    fn slice_right(&self, right: U) -> HashSet<T, S> {
        self.iter()
            .filter_map(|(t, u)| if *u == right { Some(*t) } else { None })
            .collect()
    }
}

impl<
    T: Copy + Eq + Hash,
    U: Copy + Eq + Hash,
    TS: IntoIterator<Item = T>,
    S: ::std::hash::BuildHasher + Default,
> FromRights<TS, U> for HashSet<(T, U), S>
{
    fn from_rights(it: impl IntoIterator<Item = (TS, U)>) -> Self {
        it.into_iter()
            .flat_map(|(ts, u)| ts.into_iter().map(move |t| (t, u)))
            .collect()
    }
}

impl<
    T: Copy + Eq + Hash,
    U: Copy + Eq + Hash,
    US: IntoIterator<Item = U>,
    S: ::std::hash::BuildHasher + Default,
> FromLefts<T, US> for HashSet<(T, U), S>
{
    fn from_lefts(it: impl IntoIterator<Item = (T, US)>) -> Self {
        it.into_iter()
            .flat_map(|(t, us)| us.into_iter().map(move |u| (t, u)))
            .collect()
    }
}

impl<'a, T: Eq + Hash + Copy + 'static, S: ::std::hash::BuildHasher> CopiedIter<'a, T>
    for HashSet<T, S>
{
    type IterCopied = std::iter::Copied<std::collections::hash_set::Iter<'a, T>>;
    fn copied_iter(&'a self) -> Self::IterCopied {
        self.iter().copied()
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
    V: Eq + PartialOrd + Bottom + Clone + Debug,
    VS: Set<K>
        + Intersect
        + Extract<K>
        + Default
        + Debug
        + Cartesian<HashSet<K>, Output = PS>
        + Cartesian<Output = PS>
        + Union<HashSet<K>>
        + for<'a> CopiedIter<'a, K>,
    PS: Set<(K, K)> + Union + SliceRight<K, K, VS> + Union<HashSet<(K, K)>> + Debug,
    S: System<K, V> + PairUniverse<PS> + Arguments<K, HashSet<K>> + Universe<VS> + Visited<VS>,
>(
    system: &mut S,
    target: K,
    oracle: &impl LocalOracle<K, V, PS, S>,
) -> Option<(V, (u32, u32))>
where
    HashSet<K>: Cartesian<Output = HashSet<(K, K)>> + Cartesian<VS, Output = PS> + IsSubset<VS>,
{
    let mut assignment = system.bottom_assignment();
    let mut discovered = system.universe();
    let mut rel = discovered.cartesian(&discovered);
    let mut todo = local_dependencies(target, &assignment, oracle, system, &mut rel);

    let mut variable_iterations = 0;
    let mut oracle_iterations = 0;
    #[cfg(feature = "timeout")]
    let start_time = chrono::Utc::now();

    while let Some(x) = todo.extract() {
        debug_assert!(discovered.contains(&x), "discovered should contain {x:?}");
        variable_iterations += 1;
        let evaluated = system.evaluate(x, &assignment);
        let args = system.arguments(x);
        if assignment.get_assignment(&x) != evaluated || !IsSubset::is_subset(&args, &discovered) {
            #[cfg(feature = "timeout")]
            if (chrono::Utc::now() - start_time) >= KLEENE_TIMEOUT {
                return None;
            }
            oracle_iterations += 1;
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

            todo = local_dependencies(target, &assignment, oracle, system, &mut rel);
        }
    }

    Some((
        assignment.get_assignment(&target),
        (variable_iterations, oracle_iterations),
    ))
}

fn local_dependencies<
    K: Hash + Copy + Eq,
    V: PartialOrd,
    VS: Set<K> + Intersect + for<'a> CopiedIter<'a, K>,
    PS: Set<(K, K)> + SliceRight<K, K, VS> + Debug,
    S: System<K, V>,
>(
    variable: K,
    assignment: &HashMap<K, V>,
    oracle: &impl LocalOracle<K, V, PS, S>,
    system: &mut S,
    rel: &mut PS,
) -> VS
where
{
    system.lock();
    *rel = oracle.approximate_flow(assignment, rel, system);
    system.unlock();
    rel.slice_right(variable)
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

impl<T: Clone + Eq + Hash, S: ::std::hash::BuildHasher> Extract<T> for HashSet<T, S> {
    fn extract(&mut self) -> Option<T> {
        self.iter().next().cloned().map_or_else(
            || None,
            |value| {
                self.remove(&value);
                Some(value)
            },
        )
    }
}
