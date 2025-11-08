use std::cell::RefCell;
use std::collections::HashSet;
use std::thread::LocalKey;

use oxidd::{BooleanFunction, Manager, ManagerRef};

use oxidd::bdd::{BDDFunction, BDDManagerRef, new_manager};
use slotmap::{DefaultKey, SecondaryMap};

use crate::{Cartesian, Intersect, IsSubset, Set, Union, Without};

// Type alias makes it easy to replace with generic later. May not be possible.
type K = DefaultKey;

thread_local!(static SIMPLE_BDD_MANAGER_REF: RefCell<BDDManagerRef> = RefCell::new(new_manager(2048,1024,1)));
thread_local!(static SIMPLE_BDD_LEFT_MAP: RefCell<SecondaryMap<K, u32>> = RefCell::new(SecondaryMap::default()));
thread_local!(static SIMPLE_BDD_RIGHT_MAP: RefCell<SecondaryMap<K, u32>> = RefCell::new(SecondaryMap::default()));

// enum BDDMap {
//     Var,
//     Term,
// }

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
pub struct BDDRelation {
    bdd: BDDFunction,
    // map_type: BDDMap,
}

impl BDDRelation {
    fn singleton(map: &'static LocalKey<RefCell<SecondaryMap<K, u32>>>, key: K) -> BDDFunction {
        let i = map.with(|map_ref| {
            *map_ref
                .borrow_mut()
                .entry(key)
                .expect("Key should still exist")
                .or_insert_with(|| {
                    with_simple_manager_exclusive!(|manager| manager
                        .add_vars(1)
                        .next()
                        .expect("That's it bois, we're committing warcrimes"))
                })
        });

        with_simple_manager_exclusive!(|manager| BDDFunction::var(manager, i)).expect("oom")
    }

    fn left_singleton(key: K) -> BDDFunction {
        Self::singleton(&SIMPLE_BDD_LEFT_MAP, key)
    }

    fn right_singleton(key: K) -> BDDFunction {
        Self::singleton(&SIMPLE_BDD_RIGHT_MAP, key)
    }

    fn get_left(key: K) -> Option<u32> {
        SIMPLE_BDD_LEFT_MAP.with(|map_cell| map_cell.borrow().get(key).copied())
    }

    fn get_right(key: K) -> Option<u32> {
        SIMPLE_BDD_RIGHT_MAP.with(|map_cell| map_cell.borrow().get(key).copied())
    }

    fn contains_left(&self, item: K) -> bool {
        dbg!(Self::get_left(item)).map_or_else(
            || dbg!(self.bdd.eval(std::iter::empty())),
            |var| self.bdd.eval(std::iter::once((var, true))),
        )
    }

    fn contains_right(&self, item: K) -> bool {
        Self::get_right(item).map_or_else(
            || self.bdd.eval(std::iter::empty()),
            |var| self.bdd.eval(std::iter::once((var, true))),
        )
    }

    fn union_mut(&mut self, other: &BDDFunction) {
        self.bdd = self.bdd.or(other).expect("oom");
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

    #[must_use]
    pub fn diagonal(visited: &HashSet<DefaultKey>) -> Self {
        let bdd = visited
            .iter()
            .map(|k| {
                let lhs = Self::left_singleton(*k);
                let rhs = Self::right_singleton(*k);
                lhs.and(&rhs).expect("oom")
            })
            .reduce(|set, pair| set.or(&pair).expect("oom"))
            .expect("visited should be non-empty");
        Self { bdd }
    }
}

impl Default for BDDRelation {
    fn default() -> Self {
        Self::f()
    }
}

impl Union for BDDRelation {
    fn union(self, other: Self) -> Self {
        Self {
            bdd: self.bdd.or(&other.bdd).expect("oom"),
        }
    }
}

impl Union<BDDFunction> for BDDRelation {
    fn union(self, other: BDDFunction) -> Self {
        Self {
            bdd: self.bdd.or(&other).expect("oom"),
        }
    }
}

impl Intersect for BDDRelation {
    fn intersect(self, other: &Self) -> Self {
        Self {
            bdd: self.bdd.and(&other.bdd).expect("oom"),
        }
    }
}

impl Without for BDDRelation {
    fn without(self, other: &Self) -> Self {
        Self {
            // PERF: Does this increase the size of the bdd?
            bdd: self.bdd.and(&other.bdd.not().expect("oom")).expect("oom"),
        }
    }
}

impl IsSubset for BDDRelation {
    fn is_subset(&self, other: &Self) -> bool {
        self.bdd <= other.bdd
    }
}

#[derive(Default)]
pub struct BDDSet {
    rel: BDDRelation,
}

impl BDDSet {
    #[must_use]
    pub fn t() -> Self {
        Self {
            rel: BDDRelation::t(),
        }
    }
    #[must_use]
    pub fn f() -> Self {
        Self {
            rel: BDDRelation::f(),
        }
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
        self.rel.union_mut(&BDDRelation::left_singleton(item));
        true
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
            .reduce(|rel, var| rel.or(&var).expect("oom"));

        if let Some(rhs) = rhs {
            self.rel.bdd = self.rel.bdd.and(&rhs).expect("oom");
        }
        self.rel
    }
}

#[cfg(test)]
mod test {

    use slotmap::SlotMap;

    use super::*;

    #[allow(unused_macros)]
    macro_rules! dbg_map {
        () => {
            SIMPLE_BDD_LEFT_MAP.with(|map_cell| {
                dbg!(map_cell.borrow());
            });
        };
    }

    #[test]
    #[ignore = "deprecated"]
    fn are_bdds_dumb() {
        let manager_ref = new_manager(2048, 1024, 1);
        let empty = manager_ref.with_manager_exclusive(|manager| BDDFunction::f(manager));
        let (i, var) = manager_ref.with_manager_exclusive(|manager| {
            manager
                .add_vars(2)
                .map(|i| (i, BDDFunction::var(manager, i)))
                .next()
                .expect("warcrimes")
        });

        let var = var.expect("oom");
        let res = empty.or(&var).expect("oom");

        assert!(!empty.eval(std::iter::empty()));
        assert!(!var.eval(std::iter::once((1, false))));
        assert!(!var.eval(std::iter::empty()));
        assert!(res.eval(std::iter::once((i, true))));
        assert!(!res.eval(std::iter::empty()));
    }

    #[test]
    #[ignore = "deprecated"]
    fn simple_bdd_map_contains_only_inserted_keys() {
        let mut proxy_map = SlotMap::default();
        let in_key = proxy_map.insert(3);
        let out_key = proxy_map.insert(6);
        let mut set = BDDSet::f();

        assert!(!set.contains(&out_key), "in_key should not be in set early");
        assert!(
            !set.contains(&out_key),
            "out_key should not be in set early"
        );

        set.insert(in_key);
        let var = BDDRelation::get_left(out_key);
        assert_eq!(var, None, "out_key should not be in global map");
        let var = BDDRelation::get_left(in_key);
        assert_ne!(var, None, "in_key should be in global map");

        assert!(set.contains(&in_key), "in_key should be in set late");
        assert!(!set.contains(&out_key), "out_key should not be in set late");
    }

    #[test]
    #[ignore = "deprecated"]
    fn simple_bbd_t_contains_all_variables() {
        let mut proxy_map = SlotMap::default();
        let real_key = proxy_map.insert(3);
        let fake_key = DefaultKey::default();
        let bdd = BDDSet::t();

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
