use std::{collections::HashSet, marker::PhantomData};

use fixedbitset::FixedBitSet;

use crate::{
    Cartesian, Intersect, IntersectWith, IsSubset,
    arena::Key,
    set::bitset::{BitSet, BitsetRelation, DEFAULT_RELATION_ORDER, raw::RawBitSet},
};

impl<K> BitSet<K, FixedBitSet> {
    /// Create a `BitSet` with `count` keys, all in the set
    #[must_use]
    pub fn full(count: usize) -> Self {
        let iter = std::iter::repeat(usize::MAX);
        FixedBitSet::with_capacity_and_blocks(count, iter).into()
    }
}

impl<K> From<FixedBitSet> for BitSet<K, FixedBitSet> {
    fn from(value: FixedBitSet) -> Self {
        Self {
            bitset: RawBitSet::from(value),
            _phantom_data: PhantomData,
        }
    }
}

impl<K: Key> Intersect<HashSet<K>> for BitSet<K, FixedBitSet> {
    fn intersect(mut self, other: &HashSet<K>) -> Self {
        let other: RawBitSet<FixedBitSet> =
            other.iter().map(K::index).collect::<FixedBitSet>().into();
        self.bitset.intersect_with(&other);
        self
    }
}

impl<K: Key, S, H: ::std::hash::BuildHasher> IsSubset<BitSet<K, S>> for HashSet<K, H>
where
    Self: IsSubset<RawBitSet<S>>,
{
    fn is_subset(&self, other: &BitSet<K, S>) -> bool {
        IsSubset::<RawBitSet<S>>::is_subset(self, &other.bitset)
    }
}

impl<K: Key, O: Key> Cartesian<BitSet<O, FixedBitSet>> for BitSet<K, FixedBitSet> {
    type Output = BitsetRelation<K, O, FixedBitSet>;

    fn cartesian(&self, other: &BitSet<O, FixedBitSet>) -> Self::Output {
        // TODO: maybe provide some way to choose the order?
        BitsetRelation::new_from_cartesian_raw(&self.bitset, &other.bitset, DEFAULT_RELATION_ORDER)
    }
}

impl<K: Key, O: Key> Cartesian<HashSet<O>> for BitSet<K, FixedBitSet> {
    type Output = BitsetRelation<K, O, FixedBitSet>;

    fn cartesian(&self, other: &HashSet<O>) -> Self::Output {
        let rhs = other.iter().map(Key::index).collect();
        // TODO: maybe provide some way to choose the order?
        BitsetRelation::new_from_cartesian_raw(&self.bitset, &rhs, DEFAULT_RELATION_ORDER)
    }
}

impl<K: Key, O: Key, S: ::std::hash::BuildHasher> Cartesian<BitSet<O, FixedBitSet>>
    for HashSet<K, S>
{
    type Output = BitsetRelation<K, O, FixedBitSet>;

    fn cartesian(&self, other: &BitSet<O, FixedBitSet>) -> Self::Output {
        let lhs = self.iter().map(Key::index).collect();
        // TODO: maybe provide some way to choose the order?
        BitsetRelation::new_from_cartesian_raw(&lhs, &other.bitset, DEFAULT_RELATION_ORDER)
    }
}

impl<K: Key, const N: usize> From<[K; N]> for BitSet<K, FixedBitSet> {
    fn from(value: [K; N]) -> Self {
        let mut bitset = FixedBitSet::with_capacity(value.iter().map(K::index).max().unwrap_or(0));
        for v in value {
            bitset.grow_and_insert(v.index());
        }
        Self {
            bitset: bitset.into(),
            _phantom_data: PhantomData,
        }
    }
}
