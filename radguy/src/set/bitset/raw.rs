use std::collections::HashSet;

use crate::{
    DifferenceWith, Intersect, IntersectWith, IsSubset, Set, Union, UnionOf, UnionWith, Without,
    arena::Key,
};

#[derive(Clone)]
pub struct RawBitSet<S> {
    pub(super) bitset: S,
}

pub trait SetMethods {
    /// Create a `RawBitSet` with `count` keys, all in the set
    fn full(count: usize) -> Self;
    fn clear(&mut self);
    /// Get the index of the last one in the set
    fn last_one(&self) -> usize;
}

impl<S> From<S> for RawBitSet<S> {
    fn from(value: S) -> Self {
        Self { bitset: value }
    }
}

impl<S> UnionOf for RawBitSet<S>
where
    Self: FromIterator<S>,
{
    fn union_of<T: IntoIterator<Item = Self>>(iter: T) -> Self {
        iter.into_iter().map(|b| b.bitset).collect()
    }
}

impl<S: Default> Default for RawBitSet<S> {
    fn default() -> Self {
        Self {
            bitset: S::default(),
        }
    }
}

impl<O, S> Union<O> for RawBitSet<S>
where
    Self: UnionWith<O>,
{
    fn union(mut self, other: O) -> Self {
        self.union_with(other);
        self
    }
}

impl<O, S> Intersect<O> for RawBitSet<S>
where
    Self: IntersectWith<O>,
{
    fn intersect(mut self, other: &O) -> Self {
        self.intersect_with(other);
        self
    }
}

impl<S, O> Without<O> for RawBitSet<S>
where
    Self: DifferenceWith<O>,
{
    fn without(mut self, other: &O) -> Self {
        self.difference_with(other);
        self
    }
}

impl<K: Key, S, H: ::std::hash::BuildHasher> IsSubset<RawBitSet<S>> for HashSet<K, H>
where
    RawBitSet<S>: Set<usize>,
{
    fn is_subset(&self, other: &RawBitSet<S>) -> bool {
        self.iter().all(|v| other.contains(&v.index()))
    }
}
