use crate::Assignment;
use crate::{
    Arguments, Bottom, Cartesian, Diagonal, Intersect, Maximal, PairUniverse, System, Union,
    Universe, Without,
};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::{collections::HashSet, hash::Hash, marker::PhantomData};

pub trait LocalOracle<K: Hash + Eq + Copy, V: PartialOrd, PS, S: System<K, V>> {
    fn approximate_flow(&self, assignment: &HashMap<K, V>, possible: &PS, system: &S) -> PS;

    #[must_use]
    fn then<O: LocalOracle<K, V, PS, S>>(self, other: O) -> ComposeLocal<K, V, PS, S, O, Self>
    where
        Self: std::marker::Sized,
    {
        ComposeLocal {
            outer: other,
            inner: self,
            _phantom_data: PhantomData,
        }
    }

    #[must_use]
    fn and<O: LocalOracle<K, V, PS, S>>(self, other: O) -> IntersectLocal<K, V, PS, S, O, Self>
    where
        Self: std::marker::Sized,
        PS: Intersect,
    {
        IntersectLocal {
            left: other,
            right: self,
            _phantom_data: PhantomData,
        }
    }
}

#[derive(Default, Clone)]
pub struct LocalMaxR<U>(PhantomData<U>);

impl<
    K: Hash + Eq + Copy + Debug,
    V: Maximal,
    PS: FromIterator<(K, K)> + Union + Union<HashSet<(K, K)>>,
    S: System<K, V> + Universe<U>,
    U: Cartesian<Output = PS> + Without<HashSet<K>>,
> LocalOracle<K, V, PS, S> for LocalMaxR<U>
where
    for<'a> &'a U: IntoIterator<Item = &'a K>,
{
    fn approximate_flow(&self, assignment: &HashMap<K, V>, _possible: &PS, system: &S) -> PS {
        let visited = system.visited();
        let unvisited = system.universe().without(&visited);
        let universe = system.universe();
        let unvisited_dep = universe.cartesian(&unvisited);
        let self_dep = visited.diagonal();

        let max_dep: PS = visited
            .iter()
            .flat_map(|&y| {
                if system.evaluate(y, assignment).is_maximal() {
                    std::iter::empty().collect::<Vec<_>>()
                } else {
                    universe.into_iter().map(|&x| (x, y)).collect()
                }
            })
            .collect();

        unvisited_dep.union(self_dep).union(max_dep)
    }
}

impl<U> Display for LocalMaxR<U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LocalMaxR")
    }
}

#[derive(Default, Clone)]
pub struct SMax;

impl Display for SMax {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SMax")
    }
}

// TODO: Make this more general than HashSet
impl<
    K: Hash + Eq + Copy + Debug,
    V: Maximal + Bottom + Clone,
    S: System<K, V> + PairUniverse<HashSet<(K, K)>>,
> LocalOracle<K, V, HashSet<(K, K)>, S> for SMax
{
    fn approximate_flow(
        &self,
        assignment: &HashMap<K, V>,
        possible: &HashSet<(K, K)>,
        _system: &S,
    ) -> HashSet<(K, K)> {
        // TODO: currently it's actually faster to just iterate over `system.pair_universe` with
        // the ordered algorithm, because we construct the initial strategy each time.
        // this (hopefully) isn't the case when we start reusing the relation
        possible
            .iter()
            .filter(|(x, y)| {
                !assignment.get_assignment(x).is_maximal()
                    && !assignment.get_assignment(y).is_maximal()
            })
            .copied()
            .collect::<HashSet<_>>()
    }
}

pub struct ComposeLocal<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S>,
    U: LocalOracle<K, V, PairSet, S>,
> {
    outer: T,
    inner: U,
    _phantom_data: PhantomData<(K, V, PairSet, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S>,
    U: LocalOracle<K, V, PairSet, S>,
> LocalOracle<K, V, PairSet, S> for ComposeLocal<K, V, PairSet, S, T, U>
{
    fn approximate_flow(
        &self,
        assignment: &HashMap<K, V>,
        possible: &PairSet,
        system: &S,
    ) -> PairSet {
        let Self { outer, inner, .. } = self;
        outer.approximate_flow(
            assignment,
            &inner.approximate_flow(assignment, possible, system),
            system,
        )
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S> + Display,
    U: LocalOracle<K, V, PairSet, S> + Display,
> Display for ComposeLocal<K, V, PairSet, S, T, U>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ∘ {})", self.outer, self.inner)
    }
}

pub struct IntersectLocal<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S>,
    U: LocalOracle<K, V, PairSet, S>,
> {
    left: T,
    right: U,
    _phantom_data: PhantomData<(K, V, PairSet, S)>,
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet: Intersect,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S>,
    U: LocalOracle<K, V, PairSet, S>,
> LocalOracle<K, V, PairSet, S> for IntersectLocal<K, V, PairSet, S, T, U>
{
    fn approximate_flow(
        &self,
        assignment: &HashMap<K, V>,
        possible: &PairSet,
        system: &S,
    ) -> PairSet {
        let Self { left, right, .. } = self;
        let left = left.approximate_flow(assignment, possible, system);
        let right = right.approximate_flow(assignment, possible, system);
        left.intersect(&right)
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S> + Display,
    U: LocalOracle<K, V, PairSet, S> + Display,
> Display for IntersectLocal<K, V, PairSet, S, T, U>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} ∩ {})", self.left, self.right)
    }
}

// We need to manually implement `Clone` for these oracles, because the derive macro requires that
// all type parameters of the type implement `Clone`, meaning that `S` needs to implement clone,
// even though it isn't part of the actual struct
impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S> + Clone,
    U: LocalOracle<K, V, PairSet, S> + Clone,
> Clone for ComposeLocal<K, V, PairSet, S, T, U>
{
    fn clone(&self) -> Self {
        Self {
            outer: self.outer.clone(),
            inner: self.inner.clone(),
            _phantom_data: self._phantom_data,
        }
    }
}

impl<
    K: Hash + Eq + Copy,
    V: PartialOrd,
    PairSet,
    S: System<K, V>,
    T: LocalOracle<K, V, PairSet, S> + Clone,
    U: LocalOracle<K, V, PairSet, S> + Clone,
> Clone for IntersectLocal<K, V, PairSet, S, T, U>
{
    fn clone(&self) -> Self {
        Self {
            left: self.left.clone(),
            right: self.right.clone(),
            _phantom_data: self._phantom_data,
        }
    }
}

#[derive(Clone, Default)]
pub struct TrivialOracle;

impl<K: Hash + Eq + Copy, V: Maximal, PairSet, S: System<K, V> + PairUniverse<PairSet>>
    LocalOracle<K, V, PairSet, S> for TrivialOracle
{
    fn approximate_flow(
        &self,
        _assignment: &HashMap<K, V>,
        _possible: &PairSet,
        system: &S,
    ) -> PairSet {
        system.pair_universe()
    }
}

impl Display for TrivialOracle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Trivial")
    }
}

#[derive(Default, Clone, Debug)]
pub struct ArgumentsOracle<VarKey: Eq + Copy + Hash> {
    successors: RefCell<HashMap<VarKey, HashSet<VarKey>>>,
    ancestors: RefCell<HashMap<VarKey, HashSet<VarKey>>>,
    previous_visited: RefCell<HashSet<VarKey>>,
    relation_cache: RefCell<HashSet<(VarKey, VarKey)>>,
}

impl<K: Eq + Copy + Hash + Debug> ArgumentsOracle<K> {
    fn get_updated_closure<S: Arguments<K, HashSet<K>>>(
        &self,
        visited: &HashSet<K>,
        system: &S,
    ) -> HashSet<(K, K)> {
        let mut successors = self.successors.borrow_mut();
        let mut ancestors = self.ancestors.borrow_mut();
        let mut previous_visited = self.previous_visited.borrow_mut();

        if previous_visited.len() == visited.len() {
            return self.relation_cache.borrow().clone();
        }

        let new_variables: Vec<_> = visited.difference(&previous_visited).copied().collect();
        let mut updated_ancestors = HashSet::new();

        let mut to_add = HashSet::new();
        for &variable in &new_variables {
            let args = system.arguments(variable);
            let var_ancestors = ancestors
                .entry(variable)
                .or_insert_with(|| HashSet::from([variable]))
                .clone();

            let new_successors: Vec<_> = args
                .iter()
                .copied()
                .flat_map(|a| {
                    successors
                        .entry(a)
                        .or_insert_with(|| HashSet::from([a]))
                        .clone()
                })
                .chain([variable])
                .collect();

            let var_successors = successors.entry(variable).or_default();

            var_successors.extend(new_successors);

            // Clone and shadow since we look at the entry again later and don't want to reference
            // the same object
            let var_successors = var_successors.clone();

            // each new variable has its parent's ancestors as ancestors, and itself
            for &succ in &var_successors {
                ancestors
                    .entry(succ)
                    .or_default()
                    .extend(var_ancestors.iter().copied().chain([succ]));
            }

            for &ancestor in &var_ancestors {
                if ancestor == variable {
                    continue;
                }
                // TODO: we don't actually need to update the weight of `ancestor` if extending its
                // successors added nothing
                successors
                    .get_mut(&ancestor)
                    .expect("ancestor must have successors")
                    .extend(&var_successors);
            }

            // TODO: this is probably very inefficient
            for &arg in successors
                .get(&variable)
                .expect("variable should have successors")
            {
                to_add.extend(
                    ancestors
                        .get(&arg)
                        .expect("argument should have ancestors")
                        .iter()
                        .copied()
                        .map(|anc| (arg, anc)),
                );
            }

            updated_ancestors.extend(var_ancestors.iter().copied());
        }
        let mut relation = self.relation_cache.borrow_mut();

        // TODO: this could probably be more efficient if we could have keys into the heap
        // remove all ancestors that could have been updated by `variable`, and reinsert them
        // with the new weight
        relation.retain(|(x, y)| {
            if updated_ancestors.contains(x) || to_add.contains(&(*x, *y)) {
                to_add.insert((*x, *y));
                false
            } else {
                true
            }
        });
        relation.extend(to_add);

        // PERF: maybe collect to smallvec
        previous_visited.extend(new_variables);

        relation.clone()
    }
}

// TODO: Make this generic on set/strategy implementation
impl<K: Eq + Copy + Hash + Debug, V: PartialOrd, S: System<K, V> + Arguments<K, HashSet<K>>>
    LocalOracle<K, V, HashSet<(K, K)>, S> for ArgumentsOracle<K>
{
    fn approximate_flow(
        &self,
        _assignment: &HashMap<K, V>,
        _relation: &HashSet<(K, K)>,
        system: &S,
    ) -> HashSet<(K, K)> {
        let visited = system.visited();
        self.get_updated_closure(&visited, system)
    }
}

impl<VarKey: Eq + Copy + Hash> Display for ArgumentsOracle<VarKey> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Args")
    }
}

#[derive(Default)]
pub struct IdentityOracle;

impl<K: Hash + Eq + Copy, V: Maximal, PairSet: Clone, S: System<K, V> + PairUniverse<PairSet>>
    LocalOracle<K, V, PairSet, S> for IdentityOracle
{
    fn approximate_flow(
        &self,
        _assignment: &HashMap<K, V>,
        possible: &PairSet,
        _system: &S,
    ) -> PairSet {
        possible.clone()
    }
}

impl Display for IdentityOracle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Identity")
    }
}

/// This test module is copy paste from [`StrategicArgumentsOracle`], with weights removed
#[cfg(test)]
mod tests {
    mod arguments {
        use std::collections::HashSet;

        use slotmap::{DefaultKey, SlotMap};

        use crate::{Arguments, oracle::ArgumentsOracle};

        #[derive(Default, Debug)]
        struct MockSystem {
            variables: SlotMap<DefaultKey, HashSet<DefaultKey>>,
        }

        impl MockSystem {
            fn add_variable(&mut self) -> DefaultKey {
                self.variables.insert(HashSet::new())
            }

            fn set_arguments(&mut self, variable: DefaultKey, arguments: HashSet<DefaultKey>) {
                *self
                    .variables
                    .get_mut(variable)
                    .expect("variable should be defined") = arguments;
            }
        }

        impl Arguments<DefaultKey, HashSet<DefaultKey>> for MockSystem {
            fn arguments(&self, key: DefaultKey) -> HashSet<DefaultKey> {
                self.variables
                    .get(key)
                    .expect("variable must have arguments")
                    .clone()
            }
        }

        macro_rules! system_def {
            ($($name:ident = {$($dep:ident),* $(,)?};)*) => {
                {
                    let mut system = MockSystem::default();
                    $(
                        let $name = system.add_variable();
                    )*
                    $(
                        system.set_arguments($name, HashSet::from([$($dep,)*]));
                    )*
                    (system, [$($name,)*])
                }
            };
        }

        macro_rules! test_arguments {
            ($(
                $test_name:ident: {
                    with {$(
                        $var_name:ident = {$($dep:ident),* $(,)?};
                    )*};
                    $(
                        $(
                        visit {$($visited_var:ident),* $(,)?} => {$(($l:ident, $r:ident)),* $(,)?};
                        )+
                        reset;
                    )*
                };
            )*) => {
                $(
                    #[test]
                    fn $test_name() {
                        let (system, [$($var_name,)*]) = system_def! {$(
                            $var_name = {$($dep,)*};
                        )*};
                        $(
                        let oracle = ArgumentsOracle::default();
                        assert!(
                            oracle.relation_cache.borrow().is_empty(),
                            "strategy should start empty"
                        );

                        let mut visited = HashSet::new();
                        let mut visit_seq = Vec::new();
                        $(
                            visited.extend(HashSet::from([$($visited_var,)*]));
                            visit_seq.push(stringify!($($visited_var),*));
                            let expected = HashSet::from([$(($l, $r),)*]);
                            let got = oracle.get_updated_closure(&visited, &system);

                            assert_eq!(
                                expected,
                                got,
                                "wrong strategy when visiting {{{}}}. sequence: {visit_seq:#?} state: {oracle:#?}", stringify!($($visited_var),*)
                            );
                        )+
                        )*
                    }
                )*
            };
        }

        test_arguments! {
            single_variable: {
                with {
                    x = {};
                };
                visit {x} => {(x, x)};
                reset;
            };
            direct_cycle: {
                with {
                    x = {x};
                };
                visit {x} => {(x, x)};
                reset;
            };
            chain: {
                with {
                    x = {y};
                    y = {z};
                    z = {};
                };
                visit {x} => {(x, x), (y, x), (y, y)};
                visit {y} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                visit {z} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
                visit {z} => {(z, z)};
                visit {y} => {(z, z), (y, y), (z, y)};
                visit {x} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
                visit {x} => {(x, x), (y, x), (y, y)};
                visit {z} => {(x, x), (y, x), (y, y), (z, z)};
                visit {y} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
                visit {x, z} => {(x, x), (y, x), (y, y), (z, z)};
                visit {y} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
                visit {z, y} => {(z, z), (y, y), (z, y)};
                visit {x} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
                visit {y, x} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                visit {z} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
            };
            multiple_arguments: {
                with {
                    x = {y, z};
                    y = {};
                    z = {};
                };
                visit {x} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                visit {y} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                visit {z} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                reset;
                visit {x} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                visit {y, z} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                reset;
                visit {x, y} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                visit {z} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                reset;
            };
            existing_children: {
                with {
                    x = {y, z};
                    y = {z};
                    z = {};
                };
                visit {x} => {(x, x), (y, x), (z, x), (y, y), (z, z)};
                visit {y} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                visit {z} => {(x, x), (y, x), (z, x), (y, y), (z, y), (z, z)};
                reset;
            };
            four_cycle: {
                with {
                    x = {y};
                    y = {z};
                    z = {w};
                    w = {x};
                };
                visit {x} => {(x, x), (y, y), (y, x)};
                visit {y} => {(x, x), (y, y), (y, x), (z, z), (z, y), (z, x)};
                visit {z} => {(x, x), (y, y), (y, x), (z, z), (z, y), (z, x), (w, w), (w, x), (w, y), (w, z)};
                visit {w} => {
                    (x, x), (x, y), (x, z), (x, w),
                    (y, x), (y, y), (y, z), (y, w),
                    (z, x), (z, y), (z, z), (z, w),
                    (w, x), (w, y), (w, z), (w, w),
                };
                reset;
                visit {x} => {(x, x), (y, y), (y, x)};
                visit {z} => {(x, x), (y, y), (y, x), (z, z), (w, z), (w, w)};
                visit {y} => {
                    (x, x),
                    (y, x), (y, y),
                    (z, x), (z, y), (z, z),
                    (w, x), (w, y), (w, z), (w, w),
                };
                visit {w} => {
                    (x, x), (x, y), (x, z), (x, w),
                    (y, x), (y, y), (y, z), (y, w),
                    (z, x), (z, y), (z, z), (z, w),
                    (w, x), (w, y), (w, z), (w, w),
                };
                reset;
            };
            four_cycle_with_center: {
                with {
                    x = {y};
                    y = {z, u};
                    z = {w, u};
                    w = {x};
                    u = {x, w};
                };
                visit {x} => {(x, x), (y, y), (y, x)};
                visit {y} => {
                    (x, x),
                    (y, x), (y, y),
                    (z, x), (z, y), (z, z),
                    (u, x), (u, y), (u, u)
                };
                visit {u} => {
                    (x, x), (x, y),              (x, u),
                    (y, x), (y, y),              (y, u),
                    (z, x), (z, y), (z, z), (z, u),
                    (u, x), (u, y),              (u, u),
                    (w, x), (w, y),              (w, u), (w, w),
                };
                visit {w} => {
                    (x, x), (x, y),              (x, u), (x, w),
                    (y, x), (y, y),              (y, u), (y, w),
                    (z, x), (z, y), (z, z), (z, u), (z, w),
                    (u, x), (u, y),              (u, u), (u, w),
                    (w, x), (w, y),              (w, u), (w, w),
                };
                visit {z} => {
                    (x, x), (x, y), (x, z), (x, u), (x, w),
                    (y, x), (y, y), (y, z), (y, u), (y, w),
                    (z, x), (z, y), (z, z), (z, u), (z, w),
                    (u, x), (u, y), (u, z), (u, u), (u, w),
                    (w, x), (w, y), (w, z), (w, u), (w, w),
                };
                reset;
            };
            discover_into_existing_chain: {
                with {
                    a = {b, d};
                    b = {c};
                    c = {};
                    d = {e};
                    e = {b};
                };
                visit {a} => {(a, a), (b, a), (b, b), (d, a), (d, d)};
                visit {b} => {(a, a), (b, a), (b, b), (c, c), (c, b), (c, a), (d, a), (d, d)};
                visit {c} => {(a, a), (b, a), (b, b), (c, c), (c, b), (c, a), (d, a), (d, d)};
                visit {d} => {(a, a), (b, a), (b, b), (c, c), (c, b), (c, a), (d, a), (d, d), (e, a), (e, d), (e, e)};
                visit {e} => {
                    (a, a),
                    (b, a), (b, b),              (b, d), (b, e),
                    (c, a), (c, b), (c, c), (c, d), (c, e),
                    (d, a),                           (d, d),
                    (e, a),                           (e, d), (e, e),
                };
                reset;
            };
            ancestors_updated: {
                with {
                    a = {b, c};
                    b = {d, e};
                    c = {d};
                    d = {e};
                    e = {f};
                    f = {};
                };
                visit {a} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                };
                visit {b} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                    (d, a), (d, b),              (d, d),
                    (e, a), (e, b),                           (e, e),
                };
                visit {c} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                    (d, a), (d, b), (d, c), (d, d),
                    (e, a), (e, b),                           (e, e),
                };
                visit {d} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                    (d, a), (d, b), (d, c), (d, d),
                    (e, a), (e, b), (e, c), (e, d), (e, e),
                };
                visit {e} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                    (d, a), (d, b), (d, c), (d, d),
                    (e, a), (e, b), (e, c), (e, d), (e, e),
                    (f, a), (f, b), (f, c), (f, d), (f, e), (f, f),
                };
                visit {f} => {
                    (a, a),
                    (b, a), (b, b),
                    (c, a),              (c, c),
                    (d, a), (d, b), (d, c), (d, d),
                    (e, a), (e, b), (e, c), (e, d), (e, e),
                    (f, a), (f, b), (f, c), (f, d), (f, e), (f, f),
                };
                reset;
            };
        }
    }
}
