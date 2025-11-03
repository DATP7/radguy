use std::cell::RefCell;

use oxidd::{BooleanFunction, Manager, ManagerRef};

use oxidd::bdd::{BDDFunction, BDDManagerRef, new_manager};
use slotmap::{DefaultKey, SecondaryMap};

use crate::{Cartesian, Diagonal, Intersect, IsSubset, Set, Union, Without};

// Type alias makes it easy to replace with generic later. May not be possible.
type K = DefaultKey;

thread_local!(static SIMPLE_BDD_MANAGER_REF: RefCell<BDDManagerRef> = RefCell::new(new_manager(2048,1024,1)));
thread_local!(static SIMPLE_BDD_KEY_MAP: RefCell<SecondaryMap<K, u32>> = RefCell::new(SecondaryMap::default()));

/// This is only a macro because typing the function correctly was too painful
macro_rules! with_simple_manager_exclusive {
    ($f: expr) => {
        SIMPLE_BDD_MANAGER_REF
            .with(|manager_cell| manager_cell.borrow_mut().with_manager_exclusive($f))
    };
}

/// Simple BDD Set
///
/// In `SimpleBDD` each variable represents a corresponding variable or pair in the system
/// TODO: How the hell do we store elements? BDDs work only with integers, so we may need to change
/// all slotmap code? We cannot store a map in the BDD structure, as we would then have to union
/// different maps, so if we map then a global map is needed. Manager is also required to be global
/// or we need some factory abstraction, but that is probably what manager does
pub struct SimpleBDDSet {
    bdd: BDDFunction,
}

impl SimpleBDDSet {
    fn insert_var(key: K, var: u32) -> Option<u32> {
        SIMPLE_BDD_KEY_MAP.with(|map_cell| map_cell.borrow_mut().insert(key, var))
    }

    fn get_var(key: K) -> Option<u32> {
        SIMPLE_BDD_KEY_MAP.with(|map_cell| map_cell.borrow().get(key).copied())
    }

    #[must_use]
    pub fn f() -> Self {
        let bdd = with_simple_manager_exclusive!(|manager| BDDFunction::f(manager));
        Self { bdd }
    }

    #[must_use]
    pub fn t() -> Self {
        let bdd = with_simple_manager_exclusive!(|manager| BDDFunction::t(manager));
        Self { bdd }
    }
}

impl Default for SimpleBDDSet {
    fn default() -> Self {
        Self::f()
    }
}

impl Set<K> for SimpleBDDSet {
    fn contains(&self, item: &K) -> bool {
        Self::get_var(*item).map_or_else(
            || self.bdd.eval(std::iter::empty()),
            |var| self.bdd.eval(std::iter::once((var, true))),
        )
    }

    fn insert(&mut self, item: K) -> bool {
        // PERF: If the return value is never used, check how much removing this would improve
        // performance.
        if self.contains(&item) {
            return false;
        }

        let (i, var) = with_simple_manager_exclusive!(|manager| {
            manager
                .add_vars(1)
                .map(|i| (i, BDDFunction::var(manager, i)))
                .next()
                .expect("That's it bois, we're committing warcrimes")
        });
        Self::insert_var(item, i);
        self.bdd = self.bdd.or(&var.expect("oom")).expect("oom");
        true
    }
}

impl Union for SimpleBDDSet {
    fn union(self, other: Self) -> Self {
        Self {
            bdd: self.bdd.or(&other.bdd).expect("oom"),
        }
    }
}
impl Intersect for SimpleBDDSet {
    fn intersect(self, other: &Self) -> Self {
        Self {
            bdd: self.bdd.and(&other.bdd).expect("oom"),
        }
    }
}
impl Without for SimpleBDDSet {
    fn without(self, other: &Self) -> Self {
        Self {
            // PERF: Does this increase the size of the bdd?
            bdd: self.bdd.and(&other.bdd.not().expect("oom")).expect("oom"),
        }
    }
}
impl IsSubset for SimpleBDDSet {
    fn is_subset(&self, other: &Self) -> bool {
        self.bdd <= other.bdd
    }
}
impl Cartesian for SimpleBDDSet {
    type Output = Self;

    fn cartesian(&self, other: &Self) -> Self::Output {
        todo!()
    }
}
impl Diagonal for SimpleBDDSet {
    type Output = Self;

    fn diagonal(&self) -> Self::Output {
        todo!()
    }
}

/// Binarily compressed BDD
///
/// In `BinaryhBDD` each system variable is represented as the interpretation of the binary string
/// representation of that variable's id. I.e. the inclusion of the 6th variable is represented by
/// `110` being an interpretation of the bdd
pub struct BinaryBDDSet {}

#[cfg(test)]
mod test {

    use slotmap::SlotMap;

    use super::*;

    #[allow(unused_macros)]
    macro_rules! dbg_map {
        () => {
            SIMPLE_BDD_KEY_MAP.with(|map_cell| {
                dbg!(map_cell.borrow());
            });
        };
    }

    #[test]
    fn simple_bdd_map_contains_added_key() {
        let mut proxy_map = SlotMap::default();
        let var = 3;
        let key = proxy_map.insert(var);
        SimpleBDDSet::insert_var(key, var);
        let new_var = SimpleBDDSet::get_var(key);
        assert_eq!(Some(var), new_var);
    }

    #[test]
    fn simple_bdd_map_contains_keys_in_bdd() {
        let mut proxy_map = SlotMap::default();
        let key = proxy_map.insert(3);
        let mut bdd = SimpleBDDSet::default();
        bdd.insert(key);
        let var = SimpleBDDSet::get_var(key);
        assert_ne!(var, None);
    }

    #[test]
    fn simple_bbd_t_contains_all_variables() {
        let mut proxy_map = SlotMap::default();
        let real_key = proxy_map.insert(3);
        let fake_key = DefaultKey::default();
        let bdd = SimpleBDDSet::t();

        // Keys created with default cannot be used to insert into secondary maps. Thus even if
        // this key had been used in an insert call, nothing would happen.

        assert!(
            bdd.contains(&fake_key),
            "SimpleBDDSet should contain keys that do not exist"
        );
        assert!(
            bdd.contains(&real_key),
            "SimpleBDDSet should contain keys that have not been inserted"
        );
    }
}
