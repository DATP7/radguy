use std::{collections::HashSet, fmt::Debug};

use fixedbitset::FixedBitSet;

use crate::{
    CopiedIter, DifferenceWith, Intersect, IntersectWith, IsSubset, Set, Union, UnionWith, Without,
    arena::Key,
};

#[derive(Clone)]
pub struct RawBitSet<S> {
    bitset: S,
}

pub trait SetMethods {
    /// Create a `RawBitSet` with `count` keys, all in the set
    fn full(count: usize) -> Self;
    fn clear(&mut self);
    /// Get the index of the last one in the set
    fn last_one(&self) -> usize;
}

impl SetMethods for RawBitSet<FixedBitSet> {
    fn full(count: usize) -> Self {
        let iter = std::iter::repeat(usize::MAX);
        FixedBitSet::with_capacity_and_blocks(count, iter).into()
    }

    fn clear(&mut self) {
        self.bitset.clear();
    }

    fn last_one(&self) -> usize {
        self.bitset.maximum().unwrap_or(0)
    }
}

impl<S> From<S> for RawBitSet<S> {
    fn from(value: S) -> Self {
        Self { bitset: value }
    }
}

impl<S: FromIterator<usize>> FromIterator<usize> for RawBitSet<S> {
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        Self {
            bitset: S::from_iter(iter),
        }
    }
}

impl FromIterator<FixedBitSet> for RawBitSet<FixedBitSet> {
    fn from_iter<T: IntoIterator<Item = FixedBitSet>>(iter: T) -> Self {
        iter.into_iter().fold(Self::default(), Union::union)
    }
}

impl<S: Default> Default for RawBitSet<S> {
    fn default() -> Self {
        Self {
            bitset: S::default(),
        }
    }
}

impl Eq for RawBitSet<FixedBitSet> {}
impl PartialEq for RawBitSet<FixedBitSet> {
    fn eq(&self, other: &Self) -> bool {
        for i in 0..self.bitset.len().max(other.bitset.len()) {
            if self.bitset.contains(i) != other.bitset.contains(i) {
                return false;
            }
        }
        true
    }
}

impl Debug for RawBitSet<FixedBitSet> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawBitSet")
            .field("bitset", &format!("{:b}", self.bitset))
            .finish()
    }
}

impl Set<usize> for RawBitSet<FixedBitSet> {
    fn contains(&self, item: &usize) -> bool {
        self.bitset.contains(item.index())
    }

    fn insert(&mut self, item: usize) -> bool {
        let ret = self.bitset.contains(item.index());
        self.bitset.grow_and_insert(item.index());
        ret
    }

    fn len(&self) -> usize {
        self.bitset.count_ones(..)
    }

    fn is_empty(&self) -> bool {
        self.bitset.is_clear()
    }
}

impl Union for RawBitSet<FixedBitSet> {
    fn union(mut self, other: Self) -> Self {
        self.bitset.union_with(&other.bitset);
        self
    }
}

impl Union<FixedBitSet> for RawBitSet<FixedBitSet> {
    fn union(mut self, other: FixedBitSet) -> Self {
        self.union_with(other);
        self
    }
}

impl<'a> Union<&'a Self> for RawBitSet<FixedBitSet> {
    fn union(mut self, other: &'a Self) -> Self {
        self.bitset.union_with(&other.bitset);
        self
    }
}

impl UnionWith for RawBitSet<FixedBitSet> {
    fn union_with(&mut self, other: Self) {
        self.bitset.union_with(&other.bitset);
    }
}

impl UnionWith<FixedBitSet> for RawBitSet<FixedBitSet> {
    fn union_with(&mut self, other: FixedBitSet) {
        self.bitset.union_with(&other);
    }
}

impl<'a> UnionWith<&'a Self> for RawBitSet<FixedBitSet> {
    fn union_with(&mut self, other: &'a Self) {
        self.bitset.union_with(&other.bitset);
    }
}

impl<K: Key> UnionWith<HashSet<K>> for RawBitSet<FixedBitSet> {
    fn union_with(&mut self, other: HashSet<K>) {
        for i in other {
            self.bitset.grow_and_insert(i.index());
        }
    }
}

impl Union<HashSet<usize>> for RawBitSet<FixedBitSet> {
    fn union(mut self, other: HashSet<usize>) -> Self {
        self.union_with(other);
        self
    }
}

impl IntersectWith for RawBitSet<FixedBitSet> {
    fn intersect_with(&mut self, other: &Self) {
        self.bitset.intersect_with(&other.bitset);
        // `FixedBitSet` doesn't seem to truncate properly when intersecting, so we just do it manually
        if self.bitset.len() > other.bitset.len() {
            self.bitset.remove_range(other.bitset.len()..);
        }
    }
}

impl IntersectWith<HashSet<usize>> for RawBitSet<FixedBitSet> {
    fn intersect_with(&mut self, other: &HashSet<usize>) {
        let other: FixedBitSet = other.iter().copied().collect();
        self.bitset.intersect_with(&other);
    }
}

impl<O> Intersect<O> for RawBitSet<FixedBitSet>
where
    Self: IntersectWith<O>,
{
    fn intersect(mut self, other: &O) -> Self {
        self.intersect_with(other);
        self
    }
}

impl<K: Key, S: ::std::hash::BuildHasher> IsSubset<RawBitSet<FixedBitSet>> for HashSet<K, S> {
    fn is_subset(&self, other: &RawBitSet<FixedBitSet>) -> bool {
        self.iter().all(|v| other.contains(&v.index()))
    }
}

impl DifferenceWith for RawBitSet<FixedBitSet> {
    fn difference_with(&mut self, other: &Self) {
        self.bitset.difference_with(&other.bitset);
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

impl<'a> CopiedIter<'a, usize> for RawBitSet<FixedBitSet> {
    type IterCopied = impl Iterator<Item = usize>;

    fn copied_iter(&'a self) -> Self::IterCopied {
        // `FixedBitSet::ones` produces indexes for *every* bit set to one in its blocks, including
        // ones outside the length of the bitset.
        // For example, BitSet::full(3).bitset will have a length of 3, but hold a block of 64
        // bits, all set to 1, so `ones` will emit `0..64`.
        let len = self.bitset.len();
        self.bitset.ones().filter(move |i| *i < len)
    }
}

impl IntoIterator for RawBitSet<FixedBitSet> {
    type Item = usize;
    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        // `FixedBitSet::ones` produces indexes for *every* bit set to one in its blocks, including
        // ones outside the length of the bitset.
        // For example, BitSet::full(3).bitset will have a length of 3, but hold a block of 64
        // bits, all set to 1, so `ones` will emit `0..64`.
        let len = self.bitset.len();
        self.bitset.into_ones().filter(move |i| *i < len)
    }
}
