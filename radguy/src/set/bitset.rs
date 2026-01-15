mod fixed;
mod raw;
mod relation;

use std::{collections::HashSet, fmt::Debug, marker::PhantomData};

use fixedbitset::FixedBitSet;
pub use relation::{BitsetRelation, BitsetRelationOrder, DEFAULT_RELATION_ORDER};

use crate::{
    CopiedIter, Diagonal, DifferenceWith, Extract, Intersect, IntersectWith, Set, Union, UnionWith,
    Without, arena::Key,
};

use self::raw::RawBitSet;

use rand::Rng;

#[derive(Clone)]
pub struct BitSet<K, S = FixedBitSet> {
    bitset: RawBitSet<S>,
    _phantom_data: PhantomData<K>,
}

impl<K, S> BitSet<K, S> {
    #[must_use]
    pub fn new() -> Self
    where
        S: Default,
    {
        Self::default()
    }
}

impl<K: Key> Extract<K> for BitSet<K, FixedBitSet> {
    fn extract(&mut self) -> Option<K> {
        if self.is_empty() {
            return None;
        }
        let random_index = rand::rng().random_range(0..self.len());
        let removed = self
            .copied_iter()
            .nth(random_index)
            .expect("Should not be empty");
        self.bitset.remove(&removed.index());
        Some(removed)
    }
}

impl<K, S> Debug for BitSet<K, S>
where
    RawBitSet<S>: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BitSet")
            .field("bitset", &self.bitset)
            .finish()
    }
}

impl<K, S: Default> Default for BitSet<K, S> {
    fn default() -> Self {
        Self {
            bitset: RawBitSet::default(),
            _phantom_data: PhantomData,
        }
    }
}

impl<K, S> From<RawBitSet<S>> for BitSet<K, S> {
    fn from(value: RawBitSet<S>) -> Self {
        Self {
            bitset: value,
            _phantom_data: PhantomData,
        }
    }
}

impl<K, S> Eq for BitSet<K, S> where RawBitSet<S>: Eq {}
impl<K, S> PartialEq for BitSet<K, S>
where
    RawBitSet<S>: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.bitset == other.bitset
    }
}

impl<'a, K: Key, S: 'a> CopiedIter<'a, K> for BitSet<K, S>
where
    RawBitSet<S>: CopiedIter<'a, usize>,
{
    type IterCopied = impl Iterator<Item = K>;

    fn copied_iter(&'a self) -> Self::IterCopied {
        self.bitset.copied_iter().map(K::from)
    }
}

impl<K: Key, S> Set<K> for BitSet<K, S>
where
    RawBitSet<S>: Set<usize>,
{
    fn contains(&self, item: &K) -> bool {
        self.bitset.contains(&item.index())
    }

    fn insert(&mut self, item: K) -> bool {
        let ret = self.bitset.contains(&item.index());
        self.bitset.insert(item.index());
        ret
    }

    fn remove(&mut self, x: &K) -> bool {
        self.bitset.remove(&x.index())
    }

    fn len(&self) -> usize {
        self.bitset.len()
    }

    fn is_empty(&self) -> bool {
        self.bitset.is_empty()
    }
}

impl<K, S> Union for BitSet<K, S>
where
    RawBitSet<S>: UnionWith,
{
    fn union(mut self, other: Self) -> Self {
        self.bitset.union_with(other.bitset);
        self
    }
}

impl<'a, K: Key, S> Union<&'a Self> for BitSet<K, S>
where
    RawBitSet<S>: UnionWith<&'a RawBitSet<S>>,
{
    fn union(mut self, other: &'a Self) -> Self {
        self.bitset.union_with(&other.bitset);
        self
    }
}

impl<K, S> UnionWith for BitSet<K, S>
where
    RawBitSet<S>: UnionWith,
{
    fn union_with(&mut self, other: Self) {
        self.bitset.union_with(other.bitset);
    }
}

impl<'a, K, S> UnionWith<&'a Self> for BitSet<K, S>
where
    RawBitSet<S>: UnionWith<&'a RawBitSet<S>>,
{
    fn union_with(&mut self, other: &'a Self) {
        self.bitset.union_with(&other.bitset);
    }
}

impl<K, S> Union<HashSet<K>> for BitSet<K, S>
where
    RawBitSet<S>: UnionWith<HashSet<K>>,
{
    fn union(mut self, other: HashSet<K>) -> Self {
        self.bitset.union_with(other);
        self
    }
}

impl<K, S> Intersect for BitSet<K, S>
where
    RawBitSet<S>: IntersectWith,
{
    fn intersect(mut self, other: &Self) -> Self {
        self.bitset.intersect_with(&other.bitset);
        self
    }
}

impl<K: Key, S> Without for BitSet<K, S>
where
    RawBitSet<S>: DifferenceWith,
{
    fn without(mut self, other: &Self) -> Self {
        self.bitset.difference_with(&other.bitset);
        self
    }
}

impl<K, S, O> DifferenceWith<O> for BitSet<K, S>
where
    RawBitSet<S>: DifferenceWith<O>,
{
    fn difference_with(&mut self, other: &O) {
        self.bitset.difference_with(other);
    }
}
impl<K, S, O> Without<O> for BitSet<K, S>
where
    RawBitSet<S>: Without<O>,
{
    fn without(self, other: &O) -> Self {
        let bitset = self.bitset.without(other);
        Self::from(bitset)
    }
}

impl<K: Key, S> Diagonal for BitSet<K, S>
where
    BitsetRelation<K, K, S>: FromIterator<(K, K)>,
    Self: for<'a> CopiedIter<'a, K>,
{
    type Output = BitsetRelation<K, K, S>;

    fn diagonal(&self) -> Self::Output {
        self.copied_iter().map(|x| (x, x)).collect()
    }
}

impl<K: Key, S> IntoIterator for BitSet<K, S>
where
    RawBitSet<S>: IntoIterator<Item = usize>,
{
    type Item = K;

    type IntoIter = impl Iterator<Item = K>;

    fn into_iter(self) -> Self::IntoIter {
        self.bitset.into_iter().map(K::from)
    }
}

impl<K: Key, S> FromIterator<K> for BitSet<K, S>
where
    RawBitSet<S>: FromIterator<usize>,
{
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> Self {
        let bitset = iter.into_iter().map(|i| i.index()).collect();
        Self {
            bitset,
            _phantom_data: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Set, set::bitset::BitSet};

    #[test]
    fn from_iter() {
        let s: BitSet<_> = [0, 2, 3].into_iter().collect();
        let mut expected = BitSet::new();
        expected.insert(0);
        expected.insert(2);
        expected.insert(3);
        assert_eq!(expected, s);
    }

    #[test]
    fn from_iter_of_sets() {
        let a: BitSet<_> = [0, 1, 4].into_iter().collect();
        let b: BitSet<_> = [0, 3, 5].into_iter().collect();
        let c: BitSet<_> = BitSet::from([8]);
        let expected: BitSet<_> = [0, 1, 3, 4, 5, 8].into_iter().collect();
        assert_eq!(expected, [a, b, c].into_iter().flatten().collect());
    }
}
