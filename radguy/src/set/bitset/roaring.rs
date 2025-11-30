use std::{collections::HashSet, fmt::Debug};

use roaring::{MultiOps, RoaringBitmap};

use crate::{
    Cartesian, CopiedIter, DifferenceWith, IntersectWith, Set, UnionWith,
    arena::Key,
    set::bitset::{
        BitSet, BitsetRelation, DEFAULT_RELATION_ORDER,
        raw::{RawBitSet, SetMethods},
    },
};

/// Convenience function to cast usize to u32 with panicing
#[track_caller]
fn to_u32(i: usize) -> u32 {
    u32::try_from(i).expect("cannot cast value to u32")
}

/// Convenience function to cast usize to u32 with panicing
#[track_caller]
fn to_usize(i: u32) -> usize {
    usize::try_from(i).expect("cannot cast value to usize")
}

impl Set<usize> for RawBitSet<RoaringBitmap> {
    fn contains(&self, item: &usize) -> bool {
        self.bitset.contains(to_u32(*item))
    }

    fn insert(&mut self, item: usize) -> bool {
        // `RoaringBitmap::insert` returns whether the index was *absent* before inserting
        !self.bitset.insert(to_u32(item))
    }

    fn len(&self) -> usize {
        usize::try_from(self.bitset.len()).expect("cannot cast length to usize")
    }

    fn is_empty(&self) -> bool {
        self.bitset.is_empty()
    }
}

impl SetMethods for RawBitSet<RoaringBitmap> {
    fn full(count: usize) -> Self {
        let mut bitmap = RoaringBitmap::full();
        // `RoaringBitmap::full` gives a bitmap containing 2^32 values, which is a bit excessive,
        // so we just remove to give it the correct length
        bitmap.remove_range((to_u32(count))..);
        bitmap.into()
    }

    fn clear(&mut self) {
        self.bitset.clear();
    }

    fn last_one(&self) -> usize {
        to_usize(self.bitset.max().unwrap_or(0))
    }
}

impl Eq for RawBitSet<RoaringBitmap> {}
impl PartialEq for RawBitSet<RoaringBitmap> {
    fn eq(&self, other: &Self) -> bool {
        self.bitset == other.bitset
    }
}

impl Debug for RawBitSet<RoaringBitmap> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RawBitSet")
            .field("bitset", &self.bitset)
            .finish()
    }
}

impl FromIterator<RoaringBitmap> for RawBitSet<RoaringBitmap> {
    fn from_iter<T: IntoIterator<Item = RoaringBitmap>>(iter: T) -> Self {
        iter.into_iter().union().into()
    }
}

impl FromIterator<u32> for RawBitSet<RoaringBitmap> {
    fn from_iter<T: IntoIterator<Item = u32>>(iter: T) -> Self {
        iter.into_iter().collect::<RoaringBitmap>().into()
    }
}

impl FromIterator<usize> for RawBitSet<RoaringBitmap> {
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        iter.into_iter().map(to_u32).collect()
    }
}
impl<K: Key, O: Key> Cartesian<HashSet<O>> for BitSet<K, RoaringBitmap> {
    type Output = BitsetRelation<K, O, RoaringBitmap>;

    fn cartesian(&self, other: &HashSet<O>) -> Self::Output {
        let rhs = other.iter().map(Key::index).map(to_u32).collect();
        // TODO: maybe provide some way to choose the order?
        BitsetRelation::new_from_cartesian_raw(&self.bitset, &rhs, DEFAULT_RELATION_ORDER)
    }
}

impl<K: Key, O: Key, S: ::std::hash::BuildHasher> Cartesian<BitSet<O, RoaringBitmap>>
    for HashSet<K, S>
{
    type Output = BitsetRelation<K, O, RoaringBitmap>;

    fn cartesian(&self, other: &BitSet<O, RoaringBitmap>) -> Self::Output {
        let lhs = self.iter().map(Key::index).map(to_u32).collect();
        // TODO: maybe provide some way to choose the order?
        BitsetRelation::new_from_cartesian_raw(&lhs, &other.bitset, DEFAULT_RELATION_ORDER)
    }
}

impl<K: Key, const N: usize> From<[K; N]> for BitSet<K, RoaringBitmap> {
    fn from(value: [K; N]) -> Self {
        value
            .into_iter()
            .map(|i| to_u32(i.index()))
            .collect::<RawBitSet<_>>()
            .into()
    }
}

impl UnionWith for RawBitSet<RoaringBitmap> {
    fn union_with(&mut self, other: Self) {
        self.bitset |= other.bitset;
    }
}

impl UnionWith<RoaringBitmap> for RawBitSet<RoaringBitmap> {
    fn union_with(&mut self, other: RoaringBitmap) {
        self.bitset |= other;
    }
}

impl<'a> UnionWith<&'a Self> for RawBitSet<RoaringBitmap> {
    fn union_with(&mut self, other: &'a Self) {
        self.bitset |= &other.bitset;
    }
}

impl<K: Key> UnionWith<HashSet<K>> for RawBitSet<RoaringBitmap> {
    fn union_with(&mut self, other: HashSet<K>) {
        // PERF: the roaring docs says that it might be faster to sort `other` before extending
        self.bitset
            .extend(other.into_iter().map(|i| to_u32(i.index())));
    }
}

impl IntersectWith for RawBitSet<RoaringBitmap> {
    fn intersect_with(&mut self, other: &Self) {
        self.bitset &= &other.bitset;
    }
}

impl IntersectWith<RoaringBitmap> for RawBitSet<RoaringBitmap> {
    fn intersect_with(&mut self, other: &RoaringBitmap) {
        self.bitset &= other;
    }
}

impl<K: Key> IntersectWith<HashSet<K>> for RawBitSet<RoaringBitmap> {
    fn intersect_with(&mut self, other: &HashSet<K>) {
        let other: RoaringBitmap = other.iter().map(K::index).map(to_u32).collect();
        self.bitset &= other;
    }
}

impl DifferenceWith for RawBitSet<RoaringBitmap> {
    fn difference_with(&mut self, other: &Self) {
        self.bitset -= &other.bitset;
    }
}

impl<'a> CopiedIter<'a, usize> for RawBitSet<RoaringBitmap> {
    type IterCopied = impl Iterator<Item = usize>;

    fn copied_iter(&'a self) -> Self::IterCopied {
        self.bitset.iter().map(to_usize)
    }
}

impl IntoIterator for RawBitSet<RoaringBitmap> {
    type Item = usize;

    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.bitset.into_iter().map(to_usize)
    }
}

#[cfg(test)]
mod tests {
    use roaring::RoaringBitmap;

    use crate::{
        Cartesian, Intersect, Set, SliceRight, UnionWith,
        set::bitset::{BitSet, BitsetRelation},
    };

    #[test]
    fn from_rights_ordered() {
        let rights = [
            (BitSet::from([0, 2, 4]), 0),
            (BitSet::from([1, 2, 3]), 2),
            (BitSet::from([3, 4, 5]), 3),
        ];
        let expected: BitsetRelation<usize, usize, RoaringBitmap> = [
            (0, 0),
            (2, 0),
            (4, 0),
            (1, 2),
            (2, 2),
            (3, 2),
            (3, 3),
            (4, 3),
            (5, 3),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected, BitsetRelation::from_rights(rights));
    }

    #[test]
    fn from_rights_unordered() {
        let rights = [
            (BitSet::from([1, 2, 3]), 2),
            (BitSet::from([0, 2, 4]), 0),
            (BitSet::from([3, 4, 5]), 3),
        ];
        let expected: BitsetRelation<usize, usize, RoaringBitmap> = [
            (0, 0),
            (2, 0),
            (4, 0),
            (1, 2),
            (2, 2),
            (3, 2),
            (3, 3),
            (4, 3),
            (5, 3),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected, BitsetRelation::from_rights(rights));
    }
    #[test]
    fn from_rights_hole_at_start() {
        let rights = [
            (BitSet::from([1, 2, 3]), 2),
            (BitSet::from([0, 2, 4]), 3),
            (BitSet::from([3, 4, 5]), 5),
        ];
        let expected: BitsetRelation<usize, usize, RoaringBitmap> = [
            (0, 3),
            (2, 3),
            (4, 3),
            (1, 2),
            (2, 2),
            (3, 2),
            (3, 5),
            (4, 5),
            (5, 5),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected, BitsetRelation::from_rights(rights));
    }

    #[test]
    fn slice_right_right() {
        let rights = [
            (BitSet::<_, RoaringBitmap>::from([1, 2, 3]), 2),
            (BitSet::from([0, 2, 4]), 3),
            (BitSet::from([3, 4, 5]), 5),
        ];
        let expected = BitSet::from([3, 4, 5]);

        assert_eq!(expected, BitsetRelation::from_rights(rights).slice_right(5));
    }

    #[test]
    fn cartesian_self() {
        let set = BitSet::from([0, 1, 3]);
        let expected: BitsetRelation<_, _, RoaringBitmap> = [
            (0, 0),
            (0, 1),
            (0, 3),
            (1, 0),
            (1, 1),
            (1, 3),
            (3, 0),
            (3, 1),
            (3, 3),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected, set.cartesian(&set));
    }

    #[test]
    fn cartesian_uneven() {
        let a = BitSet::from([0, 1, 3]);
        let b = BitSet::from([1, 2]);
        let expected: BitsetRelation<_, _, RoaringBitmap> =
            [(0, 1), (0, 2), (1, 1), (1, 2), (3, 1), (3, 2)]
                .into_iter()
                .collect();
        assert_eq!(expected, a.cartesian(&b));
        let expected: BitsetRelation<_, _, RoaringBitmap> =
            [(1, 0), (2, 0), (1, 1), (2, 1), (1, 3), (2, 3)]
                .into_iter()
                .collect();
        assert_eq!(expected, b.cartesian(&a));
    }

    #[test]
    fn cartesian_full() {
        let s = BitSet::full(4);
        let expected: BitsetRelation<_, _, RoaringBitmap> = [
            (0, 0),
            (0, 1),
            (0, 2),
            (0, 3),
            (1, 0),
            (1, 1),
            (1, 2),
            (1, 3),
            (2, 0),
            (2, 1),
            (2, 2),
            (2, 3),
            (3, 0),
            (3, 1),
            (3, 2),
            (3, 3),
        ]
        .into_iter()
        .collect();
        assert_eq!(expected, s.cartesian(&s));
    }

    #[test]
    fn intersect_truncate_left() {
        let big: BitSet<usize, RoaringBitmap> = BitSet::full(5);
        let small: BitSet<usize, RoaringBitmap> = BitSet::full(2);
        assert_eq!(small, big.intersect(&small));
    }
    #[test]
    fn intersect_truncate_right() {
        let big: BitSet<usize, RoaringBitmap> = BitSet::full(5);
        let small: BitSet<usize, RoaringBitmap> = BitSet::full(2);
        assert_eq!(small, small.clone().intersect(&big));
    }

    #[test]
    fn intersect() {
        let a = BitSet::<_, RoaringBitmap>::from([0, 2, 3]);
        let b = BitSet::from([1, 2, 4]);
        let expected = BitSet::from([2]);
        assert_eq!(expected, a.clone().intersect(&b));
        assert_eq!(expected, b.intersect(&a));
    }

    #[test]
    fn union_with_grows() {
        let mut rel: BitsetRelation<usize, usize> = std::iter::once((0, 0)).collect();
        rel.union_with(
            [(0, 1), (1, 0)]
                .into_iter()
                .collect::<BitsetRelation<_, _>>(),
        );
        let expected = [(0, 0), (0, 1), (1, 0)].into_iter().collect();
        assert_eq!(rel, expected);
    }

    #[test]
    fn cartesian_empty() {
        let s: BitSet<usize, RoaringBitmap> = BitSet::new();
        assert!(s.cartesian(&s).is_empty());
        assert!(!s.cartesian(&s).contains(&(0, 0)));
    }

    #[test]
    fn cartesian_single() {
        let mut s: BitSet<usize, RoaringBitmap> = BitSet::new();
        s.insert(0);
        assert!(!s.cartesian(&s).is_empty());
        assert!(s.cartesian(&s).contains(&(0, 0)));
    }
}
