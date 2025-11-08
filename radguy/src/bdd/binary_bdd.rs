use std::cell::RefCell;
use std::fs::File;
use std::thread::LocalKey;

use oxidd::{BooleanFunction, Manager, ManagerRef};

use oxidd::bdd::{BDDFunction, BDDManagerRef, new_manager};
use slotmap::{DefaultKey, SecondaryMap};

use crate::{Cartesian, Intersect, IsSubset, Set, Union, Without};

// Type alias makes it easy to replace with generic later. May not be possible.
type K = DefaultKey;
type LocalMap = &'static LocalKey<RefCell<SecondaryMap<K, u32>>>;

thread_local!(static BINARY_BDD_MANAGER_REF: RefCell<BDDManagerRef> = RefCell::new(new_manager(2048,1024,1)));
thread_local!(static BINARY_BDD_LEFT_MAP: RefCell<SecondaryMap<K, u32>> = RefCell::new(SecondaryMap::default()));
thread_local!(static BINARY_BDD_RIGHT_MAP: RefCell<SecondaryMap<K, u32>> = RefCell::new(SecondaryMap::default()));
thread_local!(static BINARY_BDD_NEXT_ID: RefCell<u32> = const { RefCell::new(0) });

/// This is only a macro because typing the function correctly was too painful
macro_rules! with_simple_manager_exclusive {
    ($f: expr) => {
        BINARY_BDD_MANAGER_REF
            .with(|manager_cell| manager_cell.borrow_mut().with_manager_exclusive($f))
    };
}

/// Creates an iterator of pairs `(index, is_set)` over the bits of `n`, starting from the least significant bit
// fn enumerate_bits(n: u32) -> impl IntoIterator<Item = (u32, bool)> {
fn enumerate_bits(n: u32) -> impl Iterator<Item = (u32, bool)> {
    let msb = msb_index(n);

    (0..=msb).map(move |i| (i, ((n >> i) & 1) == 1))
}

/// Gets the index of the most significant bit
///
/// # Examples
///
/// ```rust
/// assert_eq!(msb_index(0), 0);
/// assert_eq!(msb_index(1), 0);
/// assert_eq!(msb_index(2), 1);
/// assert_eq!(msb_index(255), 8);
/// ```
const fn msb_index(n: u32) -> u32 {
    if n == 0 { 0 } else { 31 - n.leading_zeros() }
}

/// Binarily compressed BDD
///
/// In `BinaryhBDD` each system variable is represented as the interpretation of the binary string
/// representation of that variable's id. I.e. the inclusion of the 6th variable is represented by
/// `110` being an interpretation of the bdd
pub struct BDDRelation {
    bdd: BDDFunction,
    bit_size: u32,
}

impl BDDRelation {
    fn next_id() -> u32 {
        BINARY_BDD_NEXT_ID.with(|u_ref| {
            let mut u = u_ref.borrow_mut();
            *u += 1;
            *u - 1
        })
    }

    fn current_id_size() -> u32 {
        BINARY_BDD_NEXT_ID.with(|u_ref| msb_index(*u_ref.borrow()) + 1)
    }

    fn singleton(map: LocalMap, key: K) -> Self {
        let n = Self::get_id(map, key);

        let mut bdd = with_simple_manager_exclusive!(|manager| BDDFunction::t(manager));

        for (i, bit) in enumerate_bits(n) {
            let var = with_simple_manager_exclusive!(
                |manager| BDDFunction::var(manager, i).expect("oom")
            );
            bdd = if bit {
                bdd.and(&var).expect("oom")
            } else {
                bdd.and(&var.not().expect("oom")).expect("oom")
            };
        }

        let bits = msb_index(n) + 1;
        Self {
            bdd,
            bit_size: bits,
        }
    }

    fn left_singleton(key: K) -> Self {
        Self::singleton(&BINARY_BDD_LEFT_MAP, key)
    }

    fn right_singleton(key: K) -> Self {
        Self::singleton(&BINARY_BDD_RIGHT_MAP, key)
    }

    fn get_id(map: LocalMap, key: K) -> u32 {
        let n = map.with(|map_ref| {
            *map_ref
                .borrow_mut()
                .entry(key)
                .expect("Key should still exist")
                .or_insert_with(Self::next_id)
        });

        // If this requires a new bit, create a new variable
        // Since we only increment id in this function, we do not need to check how many bits
        if n == 0 || (n > 1 && n.is_power_of_two()) {
            with_simple_manager_exclusive!(|manager| manager.add_vars(1));
        }

        n
    }

    fn get_left_id(key: K) -> u32 {
        Self::get_id(&BINARY_BDD_LEFT_MAP, key)
    }

    fn get_right_id(key: K) -> u32 {
        Self::get_id(&BINARY_BDD_RIGHT_MAP, key)
    }

    /// Resize relation to fit ids which require `size` bits
    fn fit_size(&mut self, size: u32) {
        if size > self.bit_size {
            self.bdd = self.bdd.upsize(self.bit_size, size);
        }
    }

    fn contains_left(&self, item: K) -> bool {
        let id = Self::get_left_id(item);
        // TODO: Consider how this interacts with Self::t(). Should that return true instead?
        if msb_index(id) + 1 > self.bit_size {
            return false;
        }

        self.bdd.eval(enumerate_bits(id))
    }

    fn union_mut(&mut self, mut other: Self) {
        self.fit_size(other.bit_size);
        other.fit_size(self.bit_size);
        self.bdd = self.bdd.or(&other.bdd).expect("oom");
    }

    pub fn dump(&self) {
        let _ = with_simple_manager_exclusive!(|manager| {
            oxidd_dump::dot::dump_all(
                File::create("./bdd.dot").expect("wtf"),
                manager,
                [(&self.bdd, "BDD")],
            )
        });
    }

    #[must_use]
    pub fn f() -> Self {
        let bdd = with_simple_manager_exclusive!(|manager| BDDFunction::f(manager));
        let bits = Self::current_id_size();
        Self {
            bdd,
            bit_size: bits,
        }
    }

    #[must_use]
    pub fn t() -> Self {
        let bdd = with_simple_manager_exclusive!(|manager| BDDFunction::t(manager));
        let bits = Self::current_id_size();
        Self {
            bdd,
            bit_size: bits,
        }
    }
}

impl Default for BDDRelation {
    fn default() -> Self {
        Self::f()
    }
}

impl Union for BDDRelation {
    fn union(mut self, other: Self) -> Self {
        self.union_mut(other);
        self
    }
}

impl Intersect for BDDRelation {
    fn intersect(mut self, other: &Self) -> Self {
        self.fit_size(other.bit_size);
        self.bdd = self
            .bdd
            .and(&other.bdd.upsize(other.bit_size, self.bit_size))
            .expect("oom");
        self
    }
}

impl IsSubset for BDDRelation {
    fn is_subset(&self, other: &Self) -> bool {
        self.bdd <= other.bdd
    }
}

impl Without for BDDRelation {
    fn without(mut self, other: &Self) -> Self {
        self.fit_size(other.bit_size);
        self.bdd = self
            .bdd
            .and(
                &other
                    .bdd
                    .upsize(other.bit_size, self.bit_size)
                    .not()
                    .expect("oom"),
            )
            .expect("oom");
        self
    }
}

pub struct BDDSet {
    rel: BDDRelation,
}

impl BDDSet {
    #[must_use]
    pub fn f() -> Self {
        let rel = BDDRelation::f();
        Self { rel }
    }

    #[must_use]
    pub fn t() -> Self {
        let rel = BDDRelation::t();
        Self { rel }
    }
}

impl Set<K> for BDDSet {
    fn contains(&self, item: &K) -> bool {
        self.rel.contains_left(*item)
    }

    fn insert(&mut self, item: K) -> bool {
        if self.contains(&item) {
            return false;
        }
        self.rel.union_mut(BDDRelation::left_singleton(item));
        true
    }
}

impl Default for BDDSet {
    fn default() -> Self {
        Self::f()
    }
}

impl Union for BDDSet {
    fn union(mut self, other: Self) -> Self {
        self.rel.union_mut(other.rel);
        self
    }
}

impl Intersect for BDDSet {
    fn intersect(mut self, other: &Self) -> Self {
        self.rel = self.rel.intersect(&other.rel);
        self
    }
}

impl IsSubset for BDDSet {
    fn is_subset(&self, other: &Self) -> bool {
        self.rel.is_subset(&other.rel)
    }
}

impl Without for BDDSet {
    fn without(mut self, other: &Self) -> Self {
        self.rel = self.rel.without(&other.rel);
        self
    }
}

impl<T> Cartesian<T> for BDDSet
where
    for<'a> &'a T: IntoIterator<Item = &'a K>,
{
    type Output = BDDRelation;

    fn cartesian(mut self, other: &T) -> Self::Output {
        let rhs = other
            .into_iter()
            .map(|key| BDDRelation::right_singleton(*key))
            .reduce(BDDRelation::union);

        if let Some(rhs) = rhs {
            self.rel.union_mut(rhs);
        }

        self.rel
    }
}

trait Upsize {
    fn upsize(&self, from: u32, to: u32) -> Self;
}

impl Upsize for BDDFunction {
    fn upsize(&self, from: u32, to: u32) -> Self {
        // PERF: Is this costly? I assume it is free since manager handles duplicates, and in
        // any case not most costly than an `and` or `or` invocation.
        let mut bdd = self.clone();

        if from >= to {
            return bdd;
        }

        for i in from..to {
            let var =
                with_simple_manager_exclusive!(|manager| { Self::var(manager, i).expect("oom") });
            bdd = bdd.and(&var.not().expect("oom")).expect("oom");
        }

        bdd
    }
}

impl FromIterator<K> for BDDSet {
    fn from_iter<T: IntoIterator<Item = K>>(iter: T) -> Self {
        let rel = iter
            .into_iter()
            .map(BDDRelation::left_singleton)
            .reduce(BDDRelation::union)
            .unwrap_or_else(BDDRelation::f);
        Self { rel }
    }
}

impl<'a> FromIterator<&'a K> for BDDSet {
    fn from_iter<T: IntoIterator<Item = &'a K>>(iter: T) -> Self {
        iter.into_iter().copied().collect()
    }
}

#[cfg(test)]
mod test {
    use slotmap::SlotMap;

    use super::*;

    #[test]
    fn next_id_increments() {
        let mut prev = BDDRelation::next_id();
        for id in (0..10).map(|_| BDDRelation::next_id()) {
            assert_eq!(prev + 1, id);
            prev = id;
        }
    }

    #[test]
    fn enumerate_bits_enumerates_bits() {
        assert_eq!(enumerate_bits(0).count(), 1);
        assert_eq!(enumerate_bits(1).count(), 1);
        assert_eq!(enumerate_bits(2).count(), 2);
        assert_eq!(enumerate_bits(255).count(), 8);

        assert_eq!(
            enumerate_bits(0).next().expect("should be some"),
            (0, false)
        );
    }

    #[test]
    fn bddrelation_singleton_only_contains_one_key() {
        let mut proxy_map = SlotMap::<DefaultKey, u32>::default();
        let key1 = proxy_map.insert(0);
        let key2 = proxy_map.insert(1);

        let rel = BDDRelation::left_singleton(key1);

        assert!(rel.contains_left(key1), "BDDRelation should contain key1");
        assert!(
            !rel.contains_left(key2),
            "BDDRelation should not contain key2"
        );
    }

    #[test]
    fn bddset_from_iter() {
        let mut proxy_map = SlotMap::<DefaultKey, u32>::default();
        let k1 = proxy_map.insert(0);
        let k2 = proxy_map.insert(1);
        let k3 = proxy_map.insert(2);

        let set: BDDSet = [&k1, &k2, &k3].into_iter().collect();

        assert!(set.contains(&k1));
        assert!(set.contains(&k2));
        assert!(set.contains(&k3));
    }

    #[test]
    fn bddset_intersection() {
        let mut proxy_map = SlotMap::<DefaultKey, u32>::default();
        let k1 = proxy_map.insert(0);
        let k2 = proxy_map.insert(1);
        let k3 = proxy_map.insert(2);

        // let set12: BDDSet = [&k1, &k2].into_iter().collect();
        // let set23: BDDSet = [&k2, &k3].into_iter().collect();
        let mut set12 = BDDSet::f();
        set12.insert(k1);
        set12.insert(k2);
        assert!(set12.contains(&k1));
        assert!(set12.contains(&k2));
        assert!(!set12.contains(&k3));

        let mut set23 = BDDSet::f();
        set23.insert(k2);
        set23.insert(k3);
        assert!(!set23.contains(&k1));
        assert!(set23.contains(&k2));
        assert!(set23.contains(&k3));

        let set2 = set12.intersect(&set23);

        assert!(!set2.contains(&k1));
        assert!(set2.contains(&k2));
        assert!(!set2.contains(&k3));
    }

    #[test]
    fn bddset_contains_inserted_keys() {
        let mut proxy_map = SlotMap::<DefaultKey, u32>::default();
        let key1 = proxy_map.insert(0);
        let key2 = proxy_map.insert(1);

        let mut set = BDDSet::f();

        assert!(!set.contains(&key1), "BDDSet should not contain key1");
        assert!(!set.contains(&key2), "BDDSet should not contain key2");

        set.insert(key1);
        assert!(set.contains(&key1), "BDDSet should contain key1");
        assert!(!set.contains(&key2), "BDDSet should not contain key2");

        set.insert(key2);
        assert!(set.contains(&key1), "BDDSet should contain key1");
        assert!(set.contains(&key2), "BDDSet should contain key2");
    }
}
