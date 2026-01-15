use std::{collections::HashSet, fmt::Debug, marker::PhantomData};

use fixedbitset::FixedBitSet;
use itertools::Itertools;

use crate::{
    CopiedIter, Extract, FromLefts, FromRights, Intersect, IntersectWith, LeftSliced, RightSliced,
    Set, SliceLeft, SliceRight, Union, UnionWith, Without,
    arena::Key,
    set::bitset::{BitSet, RawBitSet, raw::SetMethods},
};
// PERF: is `BitsetRelationOrder::LeftFirst` faster?
// i believe RightFirst will be faster because when we convert a relation to todo, we slice
// right, which for RightFirst is simply an array lookup
pub const DEFAULT_RELATION_ORDER: BitsetRelationOrder = BitsetRelationOrder::RightFirst;
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BitsetRelationOrder {
    LeftFirst,
    RightFirst,
}

impl BitsetRelationOrder {
    #[must_use]
    pub const fn inverse(self) -> Self {
        match self {
            Self::LeftFirst => Self::RightFirst,
            Self::RightFirst => Self::LeftFirst,
        }
    }
}

#[derive(Clone)]
pub struct BitsetRelation<T, U, S = FixedBitSet> {
    items: Vec<RawBitSet<S>>,
    order: BitsetRelationOrder,
    _phantom_data: PhantomData<(T, U)>,
}

impl<T, U, S> Default for BitsetRelation<T, U, S> {
    fn default() -> Self {
        Self::new(DEFAULT_RELATION_ORDER)
    }
}

impl<T, U, S> BitsetRelation<T, U, S> {
    #[must_use]
    pub const fn new(order: BitsetRelationOrder) -> Self {
        Self {
            items: Vec::new(),
            order,
            _phantom_data: PhantomData,
        }
    }

    #[must_use]
    pub const fn new_left() -> Self {
        Self::new(BitsetRelationOrder::LeftFirst)
    }

    #[must_use]
    pub const fn new_right() -> Self {
        Self::new(BitsetRelationOrder::RightFirst)
    }
}

impl<T: Key, U: Key, S: Default + Clone> BitsetRelation<T, U, S>
where
    RawBitSet<S>: Set<usize>,
{
    /// Insert a pair into the relation, returning whether the pair was already in the relation
    pub fn insert(&mut self, (l, r): (T, U)) -> bool {
        use BitsetRelationOrder as O;
        let (first, second) = match self.order {
            O::LeftFirst => (l.index(), r.index()),
            O::RightFirst => (r.index(), l.index()),
        };
        self.insert_ordered(first, second)
    }

    fn insert_ordered(&mut self, first: usize, second: usize) -> bool {
        if first >= self.items.len() {
            // PERF: it might be faster to so `S::with_capacity(second)`, but that requires a trait
            // that allows that
            self.items.resize(first + 1, RawBitSet::default());
        }
        self.items[first].insert(second)
    }

    /// Check whether a pair is contained in the relation, with out-of-bounds indeces being `false`
    #[must_use]
    pub fn get(&self, (l, r): (T, U)) -> bool {
        use BitsetRelationOrder as O;
        let (first, second) = match self.order {
            O::LeftFirst => (l.index(), r.index()),
            O::RightFirst => (r.index(), l.index()),
        };
        self.get_ordered(first, second)
    }

    #[must_use]
    pub fn from_rights(it: impl IntoIterator<Item = (BitSet<T, S>, U)>) -> Self {
        let items = Self::items_from_ordered(it.into_iter().map(|(s, u)| (u.index(), s.bitset)));
        Self {
            items,
            order: BitsetRelationOrder::RightFirst,
            _phantom_data: PhantomData,
        }
    }

    #[must_use]
    pub fn from_lefts(it: impl IntoIterator<Item = (T, BitSet<U, S>)>) -> Self {
        let items = Self::items_from_ordered(it.into_iter().map(|(t, s)| (t.index(), s.bitset)));
        Self {
            items,
            order: BitsetRelationOrder::LeftFirst,
            _phantom_data: PhantomData,
        }
    }

    fn items_from_ordered(
        it: impl IntoIterator<Item = (usize, RawBitSet<S>)>,
    ) -> Vec<RawBitSet<S>> {
        let it = it.into_iter();
        // PERF: we could maybe get a better size estimate?
        let mut items = Vec::with_capacity(it.size_hint().0);
        for (fst, set) in it {
            if fst >= items.len() {
                items.resize(fst + 1, RawBitSet::default());
            }
            items[fst] = set;
        }
        items
    }

    fn get_ordered(&self, first: usize, second: usize) -> bool {
        self.items.get(first).is_some_and(|s| s.contains(&second))
    }

    pub fn iter(&self) -> impl Iterator<Item = (T, U)>
    where
        RawBitSet<S>: for<'a> CopiedIter<'a, usize>,
    {
        use BitsetRelationOrder as O;
        self.items.iter().enumerate().flat_map(move |(first, s)| {
            s.copied_iter().map(move |second| match self.order {
                O::LeftFirst => (first.into(), second.into()),
                O::RightFirst => (second.into(), first.into()),
            })
        })
    }

    pub(self) fn transposed(&self) -> Self
    where
        RawBitSet<S>: for<'a> CopiedIter<'a, usize>,
    {
        let mut new = Self::new(self.order.inverse());
        for pair in self.iter() {
            new.insert(pair);
        }
        new
    }

    #[must_use]
    pub(super) fn new_from_cartesian_raw(
        left: &RawBitSet<S>,
        right: &RawBitSet<S>,
        order: BitsetRelationOrder,
    ) -> Self
    where
        RawBitSet<S>: SetMethods,
    {
        let (first, second) = match order {
            BitsetRelationOrder::LeftFirst => (left, right),
            BitsetRelationOrder::RightFirst => (right, left),
        };
        let items = Self::cartesian_items(first, second);
        Self {
            items,
            order,
            _phantom_data: PhantomData,
        }
    }

    #[must_use]
    fn cartesian_items(first: &RawBitSet<S>, second: &RawBitSet<S>) -> Vec<RawBitSet<S>>
    where
        RawBitSet<S>: SetMethods,
    {
        (0..=(first.last_one()))
            .map(|i| {
                if first.contains(&i) {
                    second.clone()
                } else {
                    // PERF: is it faster to do `FixedBitSet::with_capacity(second.len())`?
                    RawBitSet::default()
                }
            })
            .collect()
    }
}

impl<T, U, S> Debug for BitsetRelation<T, U, S>
where
    RawBitSet<S>: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BitsetRelation")
            .field("items", &self.items)
            .field("order", &self.order)
            .finish()
    }
}

impl<T: Key, U: Key, S> IntoIterator for BitsetRelation<T, U, S>
where
    RawBitSet<S>: IntoIterator<Item = usize>,
{
    type Item = (T, U);

    type IntoIter = impl Iterator<Item = (T, U)>;

    fn into_iter(self) -> Self::IntoIter {
        use BitsetRelationOrder as O;
        self.items
            .into_iter()
            .enumerate()
            .flat_map(move |(first, s)| {
                s.into_iter()
                    .map(move |second| match self.order {
                        O::LeftFirst => (first.into(), second.into()),
                        O::RightFirst => (second.into(), first.into()),
                    })
                    // PERF: remove this collect
                    .collect::<Vec<_>>()
            })
    }
}

impl<T: Key, U: Key, S: Default + Clone> IntoIterator for &BitsetRelation<T, U, S>
where
    RawBitSet<S>: Set<usize> + for<'a> CopiedIter<'a, usize>,
{
    type Item = (T, U);

    type IntoIter = impl Iterator<Item = (T, U)>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: Key, U: Key, S> Union for BitsetRelation<T, U, S>
where
    Self: UnionWith,
{
    fn union(mut self, other: Self) -> Self {
        self.union_with(other);
        self
    }
}

impl<T: Key, U: Key, S: Clone + Default + Into<RawBitSet<S>>> UnionWith for BitsetRelation<T, U, S>
where
    Self: for<'a> CopiedIter<'a, (T, U)>,
    RawBitSet<S>: Set<usize> + UnionWith,
{
    fn union_with(&mut self, other: Self) {
        if self.order == other.order {
            let len_diff = other.items.len().saturating_sub(self.items.len());
            self.items.reserve(len_diff);

            for (i, o) in other.items.into_iter().enumerate() {
                if self.items.len() <= i {
                    self.items.resize_with(i + 1, || S::default().into());
                }
                self.items[i].union_with(o);
            }
        } else {
            // PERF: is it faster to transpose `other` instead?
            for v in other.copied_iter() {
                self.insert(v);
            }
        }
    }
}

impl<T: Key, U: Key, S: Default + Clone> Union<HashSet<(T, U)>> for BitsetRelation<T, U, S>
where
    RawBitSet<S>: Set<usize>,
{
    fn union(mut self, other: HashSet<(T, U)>) -> Self {
        self.union_with(other);
        self
    }
}

impl<T: Key, U: Key, S: Default + Clone> UnionWith<HashSet<(T, U)>> for BitsetRelation<T, U, S>
where
    RawBitSet<S>: Set<usize>,
{
    fn union_with(&mut self, other: HashSet<(T, U)>) {
        for pair in other {
            self.insert(pair);
        }
    }
}

impl<T: Key, U: Key, S: Default + Clone> Set<(T, U)> for BitsetRelation<T, U, S>
where
    RawBitSet<S>: Set<usize>,
{
    fn contains(&self, item: &(T, U)) -> bool {
        self.get(*item)
    }

    fn insert(&mut self, item: (T, U)) -> bool {
        self.insert(item)
    }

    fn remove(&mut self, (l, r): &(T, U)) -> bool {
        match self.order {
            BitsetRelationOrder::LeftFirst => self
                .items
                .get_mut(l.index())
                .is_some_and(|b| b.remove(&r.index())),
            BitsetRelationOrder::RightFirst => self
                .items
                .get_mut(r.index())
                .is_some_and(|b| b.remove(&l.index())),
        }
    }

    fn len(&self) -> usize {
        self.items.iter().map(RawBitSet::len).sum()
    }

    fn is_empty(&self) -> bool {
        self.items.iter().all(RawBitSet::is_empty)
    }
}

impl<T: Key, U: Key, S> Intersect for BitsetRelation<T, U, S>
where
    RawBitSet<S>: Default
        + SetMethods
        + Set<usize>
        + IntersectWith
        + UnionWith
        + for<'a> CopiedIter<'a, usize>,
{
    fn intersect(mut self, other: &Self) -> Self {
        if self.order == other.order {
            let empty = RawBitSet::default();
            for (i, item) in self.items.iter_mut().enumerate() {
                let b = other.items.get(i).unwrap_or(&empty);
                item.intersect_with(b);
            }
        } else {
            let mut set = RawBitSet::default();
            for (i, item) in self.items.iter_mut().enumerate() {
                for j in other
                    .items
                    .get(i)
                    .map(CopiedIter::copied_iter)
                    .into_iter()
                    .flatten()
                {
                    set.insert(j);
                }
                item.intersect_with(&set);
                set.clear();
            }
        }
        self
    }
}

impl<T: Key, U: Key, S> Without for BitsetRelation<T, U, S>
where
    Self: Set<(T, U)> + for<'a> CopiedIter<'a, (T, U)>,
    RawBitSet<S>: Without + Default,
{
    fn without(mut self, other: &Self) -> Self {
        if self.order == other.order {
            for (s, o) in self.items.iter_mut().zip(other.items.iter()) {
                let s_old = std::mem::take(s);
                *s = s_old.without(o);
            }
        } else {
            for rmv in other.copied_iter() {
                self.remove(&rmv);
            }
        }
        self
    }
}

impl<T: Key, U: Key, S> RightSliced<T, U> for BitsetRelation<T, U, S>
where
    Self: Set<(T, U)>,
    RawBitSet<S>: Set<usize>,
{
    type SlicedRight = BitSet<T, S>;
}

impl<T: Key, U: Key, S> SliceRight<T, U, BitSet<T, S>> for BitsetRelation<T, U, S>
where
    Self: Set<(T, U)>,
    RawBitSet<S>: Set<usize> + Default + Clone + FromIterator<usize> + From<S>,
{
    fn slice_right(&self, right: U) -> BitSet<T, S> {
        let right_index = right.index();
        match self.order {
            BitsetRelationOrder::LeftFirst => self
                .items
                .iter()
                .enumerate()
                .filter_map(|(i, b)| {
                    if b.contains(&right_index) {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect::<RawBitSet<S>>()
                .into(),
            BitsetRelationOrder::RightFirst => self
                .items
                .get(right_index)
                .cloned()
                .unwrap_or_default()
                .into(),
        }
    }
}

impl<T: Key, U: Key, S> LeftSliced<T, U> for BitsetRelation<T, U, S>
where
    Self: Set<(T, U)>,
    RawBitSet<S>: Set<usize>,
{
    type SlicedLeft = BitSet<U, S>;
}

impl<T: Key, U: Key, S> SliceLeft<T, U, BitSet<U, S>> for BitsetRelation<T, U, S>
where
    Self: Set<(T, U)>,
    RawBitSet<S>: Set<usize> + Default + Clone + FromIterator<usize> + From<S>,
{
    fn slice_left(&self, left: T) -> BitSet<U, S> {
        let left_index = left.index();
        match self.order {
            BitsetRelationOrder::LeftFirst => self
                .items
                .get(left_index)
                .cloned()
                .unwrap_or_default()
                .into(),
            BitsetRelationOrder::RightFirst => self
                .items
                .iter()
                .enumerate()
                .filter_map(|(i, b)| {
                    if b.contains(&left_index) {
                        Some(i)
                    } else {
                        None
                    }
                })
                .collect::<RawBitSet<S>>()
                .into(),
        }
    }
}

impl<T: Key, U: Key, S: Clone + Default> Eq for BitsetRelation<T, U, S> where
    RawBitSet<S>: Set<usize> + for<'a> CopiedIter<'a, usize> + Eq
{
}

impl<T: Key, U: Key, S: Clone + Default> PartialEq for BitsetRelation<T, U, S>
where
    RawBitSet<S>: Set<usize> + PartialEq + for<'a> CopiedIter<'a, usize>,
{
    fn eq(&self, other: &Self) -> bool {
        use itertools::EitherOrBoth;

        if self.order == other.order {
            self.items
                .iter()
                .zip_longest(&other.items)
                .all(|x| match x {
                    EitherOrBoth::Both(l, r) => r == l,
                    EitherOrBoth::Left(s) | EitherOrBoth::Right(s) => s.is_empty(),
                })
        } else {
            self.eq(&other.transposed())
        }
    }
}

impl<T: Key, U: Key, S: Default + Clone> FromRights<BitSet<T, S>, U> for BitsetRelation<T, U, S>
where
    RawBitSet<S>: Set<usize>,
{
    fn from_rights(it: impl IntoIterator<Item = (BitSet<T, S>, U)>) -> Self {
        Self::from_rights(it)
    }
}

impl<T: Key, U: Key, S: Default + Clone> FromLefts<T, BitSet<U, S>> for BitsetRelation<T, U, S>
where
    RawBitSet<S>: Set<usize>,
{
    fn from_lefts(it: impl IntoIterator<Item = (T, BitSet<U, S>)>) -> Self {
        Self::from_lefts(it)
    }
}

impl<'a, T: Key, U: Key, S: 'a + Default + Clone> CopiedIter<'a, (T, U)> for BitsetRelation<T, U, S>
where
    RawBitSet<S>: Set<usize> + for<'i> CopiedIter<'i, usize>,
{
    type IterCopied = impl Iterator<Item = (T, U)>;

    fn copied_iter(&'a self) -> Self::IterCopied {
        self.iter()
    }
}

impl<T: Key, U: Key, S> FromIterator<(T, U)> for BitsetRelation<T, U, S>
where
    Self: Set<(T, U)>,
{
    fn from_iter<I: IntoIterator<Item = (T, U)>>(iter: I) -> Self {
        // PERF: there's probably a smarter way of doing this
        let mut rel = Self::default();
        for pair in iter {
            rel.insert(pair);
        }
        rel
    }
}

#[cfg(test)]
mod tests {
    use fixedbitset::FixedBitSet;

    use crate::{
        Cartesian, Intersect, SliceLeft, SliceRight, UnionWith, Without,
        set::bitset::{BitSet, BitsetRelation},
    };

    #[test]
    fn from_rights_ordered() {
        let rights = [
            (BitSet::from([0, 2, 4]), 0),
            (BitSet::from([1, 2, 3]), 2),
            (BitSet::from([3, 4, 5]), 3),
        ];
        let expected: BitsetRelation<usize, usize, FixedBitSet> = [
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
        let expected: BitsetRelation<usize, usize, FixedBitSet> = [
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
        let expected: BitsetRelation<usize, usize> = [
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
            (BitSet::from([1, 2, 3]), 2),
            (BitSet::from([0, 2, 4]), 3),
            (BitSet::from([3, 4, 5]), 5),
        ];
        let expected = BitSet::from([3, 4, 5]);

        assert_eq!(expected, BitsetRelation::from_rights(rights).slice_right(5));
    }

    #[test]
    fn slice_left_left() {
        let lefts = [
            (2, BitSet::from([1, 2, 3])),
            (3, BitSet::from([0, 2, 4])),
            (5, BitSet::from([3, 4, 5])),
        ];
        let expected = BitSet::from([3, 4, 5]);

        assert_eq!(expected, BitsetRelation::from_lefts(lefts).slice_left(5));
    }

    #[test]
    fn cartesian_self() {
        let set = BitSet::from([0, 1, 3]);
        let expected: BitsetRelation<_, _, FixedBitSet> = [
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
        let expected: BitsetRelation<_, _, FixedBitSet> =
            [(0, 1), (0, 2), (1, 1), (1, 2), (3, 1), (3, 2)]
                .into_iter()
                .collect();
        assert_eq!(expected, a.cartesian(&b));
        let expected: BitsetRelation<_, _, FixedBitSet> =
            [(1, 0), (2, 0), (1, 1), (2, 1), (1, 3), (2, 3)]
                .into_iter()
                .collect();
        assert_eq!(expected, b.cartesian(&a));
    }

    #[test]
    fn cartesian_full() {
        let s = BitSet::full(4);
        let expected: BitsetRelation<_, _, FixedBitSet> = [
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
        let big: BitSet<usize, FixedBitSet> = BitSet::full(5);
        let small: BitSet<usize, FixedBitSet> = BitSet::full(2);
        assert_eq!(small, big.intersect(&small));
    }
    #[test]
    fn intersect_truncate_right() {
        let big: BitSet<usize, FixedBitSet> = BitSet::full(5);
        let small: BitSet<usize, FixedBitSet> = BitSet::full(2);
        assert_eq!(small, small.clone().intersect(&big));
    }

    #[test]
    fn intersect() {
        let a = BitSet::from([0, 2, 3]);
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
    fn without_same_order() {
        let a: BitsetRelation<usize, usize> = [(0, 0), (1, 2), (4, 3)].into_iter().collect();
        let b: BitsetRelation<usize, usize> = [(1, 3), (4, 3)].into_iter().collect();
        let expected: BitsetRelation<usize, usize> = [(0, 0), (1, 2)].into_iter().collect();
        assert_eq!(a.without(&b), expected);
    }

    #[test]
    fn without_different_order() {
        let a: BitsetRelation<usize, usize> = [(0, 0), (1, 2), (4, 3)].into_iter().collect();
        let b = [(1, 3), (4, 3)]
            .into_iter()
            .collect::<BitsetRelation<_, _>>()
            .transposed();
        let expected: BitsetRelation<usize, usize> = [(0, 0), (1, 2)].into_iter().collect();
        assert_eq!(a.without(&b), expected);
    }
}
