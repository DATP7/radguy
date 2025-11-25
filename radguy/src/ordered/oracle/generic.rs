//! Generally applicable oracles

use std::{
    cell::RefCell,
    cmp::min,
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
};

use orx_priority_queue::PriorityQueueDecKey;
use slotmap::{Key, SecondaryMap};

use crate::{
    Arguments, DependencyGraphSystem, System, Universe,
    ordered::{
        StrategicLocalOracle,
        strategy::{
            Length, OrxStrategy, Retain, SliceRight, Strategy, StrategyItem, StrategyWeight,
        },
    },
};

#[derive(Default, Clone, Debug)]
pub struct SiblingsOracle<VS>(PhantomData<VS>);

impl<
    K: Eq + Copy + Hash + Key,
    V: PartialOrd,
    VS: Strategy<K> + Length,
    PS: Strategy<(K, K)> + SliceRight<K, K, VS> + FromIterator<StrategyItem<(K, K)>> + Clone,
    S: System<K, V> + DependencyGraphSystem<K, K>,
> StrategicLocalOracle<K, V, PS, S> for SiblingsOracle<VS>
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn get_strategy(
        &self,
        _visited: &HashSet<K>,
        _assignment: &HashMap<K, V>,
        strategy: &PS,
        system: &S,
    ) -> PS {
        strategy
            .into_iter()
            .map(|StrategyItem(weight, (x, y))| {
                let Some(hyper_edges) = system.get_hyperedges(y) else {
                    return StrategyItem(weight, (x, y));
                };

                StrategyItem(
                    weight
                        + hyper_edges
                            .into_iter()
                            .filter(|siblings| siblings.contains(&x))
                            .map(|siblings| {
                                siblings
                                    .into_iter()
                                    .map(|sibling| {
                                        strategy
                                            .get_weight((sibling, y))
                                            .unwrap_or(StrategyWeight::Infinity)
                                    })
                                    .sum()
                            })
                            .min()
                            .unwrap_or(StrategyWeight::Infinity),
                    (x, y),
                )
            })
            .collect()
    }
}

impl<VS> Display for SiblingsOracle<VS> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Siblings")
    }
}

#[derive(Default, Clone, Debug)]
pub struct CountOracle<VS>(PhantomData<VS>);

impl<
    K: Eq + Copy + Hash,
    V: PartialOrd,
    VS: Strategy<K> + Length,
    PS: Strategy<(K, K)> + SliceRight<K, K, VS> + FromIterator<StrategyItem<(K, K)>> + Clone + Debug,
    S: System<K, V>,
> StrategicLocalOracle<K, V, PS, S> for CountOracle<VS>
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn get_strategy(&self, _assignment: &HashMap<K, V>, strategy: &PS, _system: &S) -> PS {
        let mut lens = HashMap::<K, u64>::new();
        strategy
            .into_iter()
            .map(|StrategyItem(_, (x, y))| {
                StrategyItem(
                    StrategyWeight::Num(
                        *lens
                            .entry(x)
                            .or_insert_with(|| strategy.clone().slice_right(x).length() as u64),
                    ),
                    (x, y),
                )
            })
            .collect()
    }
}

impl<VS> Display for CountOracle<VS> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Count")
    }
}

#[derive(Clone, Default)]
pub struct InverseCountOracle<VS>(PhantomData<VS>);

impl<
    K: Eq + Copy + Hash,
    V: PartialOrd,
    VS: Strategy<K> + Length,
    PS: Strategy<(K, K)> + SliceRight<K, K, VS> + FromIterator<StrategyItem<(K, K)>> + Clone,
    S: System<K, V>,
> StrategicLocalOracle<K, V, PS, S> for InverseCountOracle<VS>
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn get_strategy(&self, _assignment: &HashMap<K, V>, strategy: &PS, _system: &S) -> PS {
        let mut lens = HashMap::<K, u64>::new();
        strategy
            .into_iter()
            .map(|StrategyItem(_, (x, y))| {
                StrategyItem(
                    StrategyWeight::Num(*lens.entry(x).or_insert_with(|| {
                        u64::MAX - (strategy.clone().slice_right(x).length() as u64)
                    })),
                    (x, y),
                )
            })
            .collect()
    }
}

impl<VS> Display for InverseCountOracle<VS> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Count⁻¹")
    }
}

#[derive(Default, Clone, Debug)]
pub struct StrategicArgumentsOracle<VarKey: Eq + Copy + Hash, PS: Strategy<(VarKey, VarKey)>> {
    successors: RefCell<HashMap<VarKey, HashSet<VarKey>>>,
    ancestors: RefCell<HashMap<VarKey, HashSet<VarKey>>>,
    previous_visited: RefCell<HashSet<VarKey>>,
    strategy_cache: RefCell<PS>,
}

impl<
    K: Eq + Copy + Hash + Debug,
    PS: Strategy<(K, K)> + Extend<StrategyItem<(K, K)>> + Retain<(K, K)> + Clone,
> StrategicArgumentsOracle<K, PS>
{
    fn get_updated_closure_generic<S: Arguments<K, HashSet<K>>>(
        &self,
        visited: &HashSet<K>,
        system: &S,
    ) -> PS {
        let mut successors = self.successors.borrow_mut();
        let mut ancestors = self.ancestors.borrow_mut();
        let mut previous_visited = self.previous_visited.borrow_mut();

        if previous_visited.len() == visited.len() {
            return self.strategy_cache.borrow().clone();
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
        let mut strategy = self.strategy_cache.borrow_mut();

        // TODO: this could probably be more efficient if we could have keys into the heap
        // remove all ancestors that could have been updated by `variable`, and reinsert them
        // with the new weight
        strategy.retain(|StrategyItem(_, (x, y))| {
            if updated_ancestors.contains(x) || to_add.contains(&(*x, *y)) {
                to_add.insert((*x, *y));
                false
            } else {
                true
            }
        });
        strategy.extend(to_add.into_iter().map(|(x, y)| {
            StrategyItem(
                StrategyWeight::Num(successors.get(&x).map_or(1, HashSet::len) as u64),
                (x, y),
            )
        }));

        // PERF: maybe collect to smallvec
        previous_visited.extend(new_variables);

        strategy.clone()
    }
}

impl<K: Eq + Copy + Hash + Debug, H: PriorityQueueDecKey<(K, K), StrategyWeight> + Clone + Debug>
    StrategicArgumentsOracle<K, OrxStrategy<(K, K), H>>
{
    fn get_updated_closure_orx<S: Arguments<K, HashSet<K>>>(
        &self,
        visited: &HashSet<K>,
        system: &S,
    ) -> OrxStrategy<(K, K), H> {
        let mut successors = self.successors.borrow_mut();
        let mut ancestors = self.ancestors.borrow_mut();
        let mut previous_visited = self.previous_visited.borrow_mut();

        if previous_visited.len() == visited.len() {
            return self.strategy_cache.borrow().clone();
        }

        let new_variables: Vec<_> = visited.difference(&previous_visited).copied().collect();
        let mut updated_ancestors = HashSet::new();

        let mut to_update = HashSet::new();
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
                to_update.extend(
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
        let mut strategy = self.strategy_cache.borrow_mut();

        to_update.extend(
            strategy
                .iter()
                .map(|StrategyItem(_, v)| v)
                .filter(|(x, _)| updated_ancestors.contains(x)),
        );

        for (x, y) in to_update {
            strategy.update_key_or_push(
                &(x, y),
                StrategyWeight::Num(successors.get(&x).map_or(1, HashSet::len) as u64),
            );
        }

        previous_visited.extend(new_variables);

        strategy.clone()
    }
}

// TODO: Make this generic on set/strategy implementation
impl<
    K: Eq + Copy + Hash + Debug,
    V: PartialOrd,
    PS: Strategy<(K, K)> + Retain<(K, K)> + Extend<StrategyItem<(K, K)>> + Clone,
    S: System<K, V> + Arguments<K, HashSet<K>>,
> StrategicLocalOracle<K, V, PS, S> for StrategicArgumentsOracle<K, PS>
{
    fn get_strategy(&self, _assignment: &HashMap<K, V>, _strategy: &PS, system: &S) -> PS {
        let visited = system.visited();
        self.get_updated_closure_generic(&visited, system)
    }
}

// TODO: Make this generic on set/strategy implementation
impl<
    K: Eq + Copy + Hash + Debug,
    V: PartialOrd,
    H: PriorityQueueDecKey<(K, K), StrategyWeight> + Clone + Debug,
    S: System<K, V> + Arguments<K, HashSet<K>>,
> StrategicLocalOracle<K, V, OrxStrategy<(K, K), H>, S>
    for StrategicArgumentsOracle<K, OrxStrategy<(K, K), H>>
{
    fn get_strategy(
        &self,
        _assignment: &HashMap<K, V>,
        _strategy: &OrxStrategy<(K, K), H>,
        system: &S,
    ) -> OrxStrategy<(K, K), H> {
        let visited = system.visited();
        self.get_updated_closure_orx(&visited, system)
    }
}

impl<VarKey: Eq + Copy + Hash, PS: Strategy<(VarKey, VarKey)>> Display
    for StrategicArgumentsOracle<VarKey, PS>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Args_c")
    }
}

#[derive(Default, Clone, Debug)]
pub struct StrategicHeightOracle {
    transitive_weights: bool,
}
#[expect(clippy::similar_names)]
impl StrategicHeightOracle {
    fn get_updated_weights<
        K: Eq + Copy + Hash + Debug + Key,
        S: Arguments<K, HashSet<K>> + Universe<HashSet<K>>,
        PS: Strategy<(K, K)>
            + Default
            + Extend<StrategyItem<(K, K)>>
            + FromIterator<StrategyItem<(K, K)>>,
    >(
        &self,
        visited: &HashSet<K>,
        system: &S,
        relation: &PS,
    ) -> PS
    where
        for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
    {
        let variables = system.universe();

        let weightmap: HashMap<_, _> = relation
            .into_iter()
            .map(|StrategyItem(weight, (x, y))| ((x, y), weight))
            .collect();

        let mut graph = SecondaryMap::new();
        for &i in &variables {
            let mut inner = SecondaryMap::new();
            for &j in &variables {
                if let Some(weight) = weightmap.get(&(i, j))
                    && (i == j || (visited.contains(&j) && system.arguments(j).contains(&i)))
                {
                    inner.insert(j, *weight);
                }
            }
            graph.insert(i, inner);
        }

        let loop_counter = if self.transitive_weights { 2 } else { 1 };
        for _ in 1..=loop_counter {
            for &k in &variables {
                let k_map = graph
                    .get(k)
                    .expect("All variables should be mapped")
                    // TODO: Refcell or cow remove this clone
                    .clone();
                for &i in &variables {
                    let i_map = graph.get_mut(i).expect("All variables should be mapped");
                    for &j in &variables {
                        let dist_ij = i_map.get(j);
                        let dist_ik = i_map.get(k);
                        let dist_kj = k_map.get(j);
                        let graph_weight = weightmap.get(&(i, j));
                        if let Some(dist_ik) = dist_ik
                            && let Some(dist_kj) = dist_kj
                            && let Some(graph_weight) = graph_weight
                        {
                            let val = if self.transitive_weights {
                                dist_ij.map_or_else(
                                    || min(*graph_weight, *dist_ik + *dist_kj),
                                    |dist_ij| {
                                        min(*graph_weight, min(*dist_ij, *dist_ik + *dist_kj))
                                    },
                                )
                            } else {
                                dist_ij.map_or_else(
                                    || *dist_ik + *dist_kj,
                                    |dist_ij| min(*dist_ij, *dist_ik + *dist_kj),
                                )
                            };
                            i_map.insert(j, val);
                        }
                    }
                }
            }
        }

        let mut vec = Vec::new();
        for &i in &variables {
            for &j in &variables {
                let val = graph.get(i).expect("All variables should be mapped").get(j);
                if let Some(val) = val
                    && weightmap.contains_key(&(i, j))
                {
                    vec.insert(0, StrategyItem(*val, (i, j)));
                }
            }
        }

        PS::from_iter(vec)
    }
}

impl<
    K: Eq + Copy + Hash + Debug + Key,
    V: PartialOrd,
    S: System<K, V> + Arguments<K, HashSet<K>> + Universe<HashSet<K>>,
    PS: Strategy<(K, K)> + Default + Extend<StrategyItem<(K, K)>> + FromIterator<StrategyItem<(K, K)>>,
> StrategicLocalOracle<K, V, PS, S> for StrategicHeightOracle
where
    for<'a> &'a PS: IntoIterator<Item = StrategyItem<(K, K)>>,
{
    fn get_strategy(&self, _assignment: &HashMap<K, V>, strategy: &PS, system: &S) -> PS {
        let visited = system.visited();
        self.get_updated_weights(&visited, system, strategy)
    }
}

impl StrategicHeightOracle {
    /// Makes the oracle consider the weights of pairs (y, x) in the relation where y is not an argument of x. Will be slower than the simple function
    #[must_use]
    pub const fn transitive() -> Self {
        Self {
            transitive_weights: true,
        }
    }
    /// Makes the oracle only consider the weights of pairs (y, x) in the relation if y is an argument of x. Will be faster than the transitive function
    #[must_use]
    pub const fn simple() -> Self {
        Self {
            transitive_weights: false,
        }
    }
}

impl Display for StrategicHeightOracle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "height_c")
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        Arguments, Universe,
        ordered::{
            oracle::StrategicArgumentsOracle,
            strategy::{BinaryHeapStrategy, Domain, StrategyItem, StrategyWeight},
        },
    };
    use std::collections::{HashMap, HashSet};
    use std::fmt::Debug;

    use slotmap::{DefaultKey, SlotMap};
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

    impl Universe<HashSet<DefaultKey>> for MockSystem {
        fn universe(&self) -> HashSet<DefaultKey> {
            self.variables.keys().collect()
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
    mod arguments {
        use super::*;

        macro_rules! test_arguments {
            ($(
                $test_name:ident: {
                    with {$(
                        $var_name:ident = {$($dep:ident),* $(,)?};
                    )*};
                    $(
                        $(
                        visit {$($visited_var:ident),* $(,)?} => {$(($l:ident, $r:ident) -> $w:literal),* $(,)?};
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
                        let oracle = StrategicArgumentsOracle::<_, BinaryHeapStrategy<_>>::default();
                        assert!(
                            oracle.strategy_cache.borrow().is_empty(),
                            "strategy should start empty"
                        );

                        let mut visited = HashSet::new();
                        let mut visit_seq = Vec::new();
                        $(
                            visited.extend(HashSet::from([$($visited_var,)*]));
                            visit_seq.push(stringify!($($visited_var),*));
                            let expected = BinaryHeapStrategy::from_iter([$(StrategyItem(StrategyWeight::Num($w), ($l, $r)),)*]);
                            let got = oracle.get_updated_closure_generic(&visited, &system);

                            let expected_domain: HashSet<_> = expected.clone().domain();
                            let got_domain: HashSet<_> = got.clone().domain();

                            for v in &got_domain {
                                assert!(expected_domain.contains(&v), "got domain contains {v:?} but shouldn't. sequence: {visit_seq:?}");
                            }
                            for v in &expected_domain {
                                assert!(got_domain.contains(&v), "got domain does not contain {v:?}. sequence: {visit_seq:#?}");
                            }
                            assert_eq!(expected_domain, got.clone().domain(),
                                "wrong domain when visiting {{{}}}. sequence: {visit_seq:#?} state: {oracle:#?}", stringify!($($visited_var),*)
                            );
                            let got_map = got
                                    .into_iter()
                                    .map(|StrategyItem(w, (x, y))| ((x, y), w))
                                    .collect::<HashMap<_, _>>();
                            for StrategyItem(w, v) in expected.iter() {
                                let w_got = got_map.get(&v).expect(&*format!("{v:?} does not exist in got"));
                                assert_eq!(w, *w_got, "wrong weight for {v:?}");
                            }

                            assert_eq!(
                                expected.into_iter().map(|StrategyItem(w, (x, y))| ((x, y), w)).collect::<HashMap<_, _>>(),
                                got_map,
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
                visit {x} => {(x, x) -> 1};
                reset;
            };
            direct_cycle: {
                with {
                    x = {x};
                };
                visit {x} => {(x, x) -> 1};
                reset;
            };
            chain: {
                with {
                    x = {y};
                    y = {z};
                    z = {};
                };
                visit {x} => {(x, x) -> 2, (y, x) -> 1, (y, y) -> 1};
                visit {y} => {(x, x) -> 3, (y, x) -> 2, (z, x) -> 1, (y, y) -> 2, (z, y) -> 1, (z, z) -> 1};
                visit {z} => {(x, x) -> 3, (y, x) -> 2, (z, x) -> 1, (y, y) -> 2, (z, y) -> 1, (z, z) -> 1};
                reset;
                visit {z} => {(z, z) -> 1};
                visit {y} => {(z, z) -> 1, (y, y) -> 2, (z, y) -> 1};
                visit {x} => {(x, x) -> 3, (y, x) -> 2, (z, x) -> 1, (y, y) -> 2, (z, y) -> 1, (z, z) -> 1};
                reset;
                visit {x} => {(x, x) -> 2, (y, x) -> 1, (y, y) -> 1};
                visit {z} => {(x, x) -> 2, (y, x) -> 1, (y, y) -> 1, (z, z) -> 1};
                visit {y} => {(x, x) -> 3, (y, x) -> 2, (z, x) -> 1, (y, y) -> 2, (z, y) -> 1, (z, z) -> 1};
                reset;
                visit {x, z} => {(x, x) -> 2, (y, x) -> 1, (y, y) -> 1, (z, z) -> 1};
                visit {y} => {(x, x) -> 3, (y, x) -> 2, (z, x) -> 1, (y, y) -> 2, (z, y) -> 1, (z, z) -> 1};
                reset;
                visit {z, y} => {(z, z) -> 1, (y, y) -> 2, (z, y) -> 1};
                visit {x} => {(x, x) -> 3, (y, x) -> 2, (z, x) -> 1, (y, y) -> 2, (z, y) -> 1, (z, z) -> 1};
                reset;
                visit {y, x} => {(x, x) -> 3, (y, x) -> 2, (z, x) -> 1, (y, y) -> 2, (z, y) -> 1, (z, z) -> 1};
                visit {z} => {(x, x) -> 3, (y, x) -> 2, (z, x) -> 1, (y, y) -> 2, (z, y) -> 1, (z, z) -> 1};
                reset;
            };
            multiple_arguments: {
                with {
                    x = {y, z};
                    y = {};
                    z = {};
                };
                visit {x} => {(x, x) -> 3, (y, x) -> 1, (z, x) -> 1, (y, y) -> 1, (z, z) -> 1};
                visit {y} => {(x, x) -> 3, (y, x) -> 1, (z, x) -> 1, (y, y) -> 1, (z, z) -> 1};
                visit {z} => {(x, x) -> 3, (y, x) -> 1, (z, x) -> 1, (y, y) -> 1, (z, z) -> 1};
                reset;
                visit {x} => {(x, x) -> 3, (y, x) -> 1, (z, x) -> 1, (y, y) -> 1, (z, z) -> 1};
                visit {y, z} => {(x, x) -> 3, (y, x) -> 1, (z, x) -> 1, (y, y) -> 1, (z, z) -> 1};
                reset;
                visit {x, y} => {(x, x) -> 3, (y, x) -> 1, (z, x) -> 1, (y, y) -> 1, (z, z) -> 1};
                visit {z} => {(x, x) -> 3, (y, x) -> 1, (z, x) -> 1, (y, y) -> 1, (z, z) -> 1};
                reset;
            };
            existing_children: {
                with {
                    x = {y, z};
                    y = {z};
                    z = {};
                };
                visit {x} => {(x, x) -> 3, (y, x) -> 1, (z, x) -> 1, (y, y) -> 1, (z, z) -> 1};
                visit {y} => {(x, x) -> 3, (y, x) -> 2, (z, x) -> 1, (y, y) -> 2, (z, y) -> 1, (z, z) -> 1};
                visit {z} => {(x, x) -> 3, (y, x) -> 2, (z, x) -> 1, (y, y) -> 2, (z, y) -> 1, (z, z) -> 1};
                reset;
            };
            four_cycle: {
                with {
                    x = {y};
                    y = {z};
                    z = {w};
                    w = {x};
                };
                visit {x} => {(x, x) -> 2, (y, y) -> 1, (y, x) -> 1};
                visit {y} => {(x, x) -> 3, (y, y) -> 2, (y, x) -> 2, (z, z) -> 1, (z, y) -> 1, (z, x) -> 1};
                visit {z} => {(x, x) -> 4, (y, y) -> 3, (y, x) -> 3, (z, z) -> 2, (z, y) -> 2, (z, x) -> 2, (w, w) -> 1, (w, x) -> 1, (w, y) -> 1, (w, z) -> 1};
                visit {w} => {
                    (x, x) -> 4, (x, y) -> 4, (x, z) -> 4, (x, w) -> 4,
                    (y, x) -> 4, (y, y) -> 4, (y, z) -> 4, (y, w) -> 4,
                    (z, x) -> 4, (z, y) -> 4, (z, z) -> 4, (z, w) -> 4,
                    (w, x) -> 4, (w, y) -> 4, (w, z) -> 4, (w, w) -> 4,
                };
                reset;
                visit {x} => {(x, x) -> 2, (y, y) -> 1, (y, x) -> 1};
                visit {z} => {(x, x) -> 2, (y, y) -> 1, (y, x) -> 1, (z, z) -> 2, (w, z) -> 1, (w, w) -> 1};
                visit {y} => {
                    (x, x) -> 4,
                    (y, x) -> 3, (y, y) -> 3,
                    (z, x) -> 2, (z, y) -> 2, (z, z) -> 2,
                    (w, x) -> 1, (w, y) -> 1, (w, z) -> 1, (w, w) -> 1,
                };
                visit {w} => {
                    (x, x) -> 4, (x, y) -> 4, (x, z) -> 4, (x, w) -> 4,
                    (y, x) -> 4, (y, y) -> 4, (y, z) -> 4, (y, w) -> 4,
                    (z, x) -> 4, (z, y) -> 4, (z, z) -> 4, (z, w) -> 4,
                    (w, x) -> 4, (w, y) -> 4, (w, z) -> 4, (w, w) -> 4,
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
                visit {x} => {(x, x) -> 2, (y, y) -> 1, (y, x) -> 1};
                visit {y} => {
                    (x, x) -> 4,
                    (y, x) -> 3, (y, y) -> 3,
                    (z, x) -> 1, (z, y) -> 1, (z, z) -> 1,
                    (u, x) -> 1, (u, y) -> 1, (u, u) -> 1
                };
                visit {u} => {
                    (x, x) -> 5, (x, y) -> 5,              (x, u) -> 5,
                    (y, x) -> 5, (y, y) -> 5,              (y, u) -> 5,
                    (z, x) -> 1, (z, y) -> 1, (z, z) -> 1, (z, u) -> 1,
                    (u, x) -> 5, (u, y) -> 5,              (u, u) -> 5,
                    (w, x) -> 1, (w, y) -> 1,              (w, u) -> 1, (w, w) -> 1,
                };
                visit {w} => {
                    (x, x) -> 5, (x, y) -> 5,              (x, u) -> 5, (x, w) -> 5,
                    (y, x) -> 5, (y, y) -> 5,              (y, u) -> 5, (y, w) -> 5,
                    (z, x) -> 1, (z, y) -> 1, (z, z) -> 1, (z, u) -> 1, (z, w) -> 1,
                    (u, x) -> 5, (u, y) -> 5,              (u, u) -> 5, (u, w) -> 5,
                    (w, x) -> 5, (w, y) -> 5,              (w, u) -> 5, (w, w) -> 5,
                };
                visit {z} => {
                    (x, x) -> 5, (x, y) -> 5, (x, z) -> 5, (x, u) -> 5, (x, w) -> 5,
                    (y, x) -> 5, (y, y) -> 5, (y, z) -> 5, (y, u) -> 5, (y, w) -> 5,
                    (z, x) -> 5, (z, y) -> 5, (z, z) -> 5, (z, u) -> 5, (z, w) -> 5,
                    (u, x) -> 5, (u, y) -> 5, (u, z) -> 5, (u, u) -> 5, (u, w) -> 5,
                    (w, x) -> 5, (w, y) -> 5, (w, z) -> 5, (w, u) -> 5, (w, w) -> 5,
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
                visit {a} => {(a, a) -> 3, (b, a) -> 1, (b, b) -> 1, (d, a) -> 1, (d, d) -> 1};
                visit {b} => {(a, a) -> 4, (b, a) -> 2, (b, b) -> 2, (c, c) -> 1, (c, b) -> 1, (c, a) -> 1, (d, a) -> 1, (d, d) -> 1};
                visit {c} => {(a, a) -> 4, (b, a) -> 2, (b, b) -> 2, (c, c) -> 1, (c, b) -> 1, (c, a) -> 1, (d, a) -> 1, (d, d) -> 1};
                visit {d} => {(a, a) -> 5, (b, a) -> 2, (b, b) -> 2, (c, c) -> 1, (c, b) -> 1, (c, a) -> 1, (d, a) -> 2, (d, d) -> 2, (e, a) -> 1, (e, d) -> 1, (e, e) -> 1};
                visit {e} => {
                    (a, a) -> 5,
                    (b, a) -> 2, (b, b) -> 2,              (b, d) -> 2, (b, e) -> 2,
                    (c, a) -> 1, (c, b) -> 1, (c, c) -> 1, (c, d) -> 1, (c, e) -> 1,
                    (d, a) -> 4,                           (d, d) -> 4,
                    (e, a) -> 3,                           (e, d) -> 3, (e, e) -> 3,
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
                    (a, a) -> 3,
                    (b, a) -> 1, (b, b) -> 1,
                    (c, a) -> 1,              (c, c) -> 1,
                };
                visit {b} => {
                    (a, a) -> 5,
                    (b, a) -> 3, (b, b) -> 3,
                    (c, a) -> 1,              (c, c) -> 1,
                    (d, a) -> 1, (d, b) -> 1,              (d, d) -> 1,
                    (e, a) -> 1, (e, b) -> 1,                           (e, e) -> 1,
                };
                visit {c} => {
                    (a, a) -> 5,
                    (b, a) -> 3, (b, b) -> 3,
                    (c, a) -> 2,              (c, c) -> 2,
                    (d, a) -> 1, (d, b) -> 1, (d, c) -> 1, (d, d) -> 1,
                    (e, a) -> 1, (e, b) -> 1,                           (e, e) -> 1,
                };
                visit {d} => {
                    (a, a) -> 5,
                    (b, a) -> 3, (b, b) -> 3,
                    (c, a) -> 3,              (c, c) -> 3,
                    (d, a) -> 2, (d, b) -> 2, (d, c) -> 2, (d, d) -> 2,
                    (e, a) -> 1, (e, b) -> 1, (e, c) -> 1, (e, d) -> 1, (e, e) -> 1,
                };
                visit {e} => {
                    (a, a) -> 6,
                    (b, a) -> 4, (b, b) -> 4,
                    (c, a) -> 4,              (c, c) -> 4,
                    (d, a) -> 3, (d, b) -> 3, (d, c) -> 3, (d, d) -> 3,
                    (e, a) -> 2, (e, b) -> 2, (e, c) -> 2, (e, d) -> 2, (e, e) -> 2,
                    (f, a) -> 1, (f, b) -> 1, (f, c) -> 1, (f, d) -> 1, (f, e) -> 1, (f, f) -> 1,
                };
                visit {f} => {
                    (a, a) -> 6,
                    (b, a) -> 4, (b, b) -> 4,
                    (c, a) -> 4,              (c, c) -> 4,
                    (d, a) -> 3, (d, b) -> 3, (d, c) -> 3, (d, d) -> 3,
                    (e, a) -> 2, (e, b) -> 2, (e, c) -> 2, (e, d) -> 2, (e, e) -> 2,
                    (f, a) -> 1, (f, b) -> 1, (f, c) -> 1, (f, d) -> 1, (f, e) -> 1, (f, f) -> 1,
                };
                reset;
            };
        }
    }
    mod height {
        use super::*;
        use crate::ordered::oracle::StrategicHeightOracle;

        macro_rules! create_oracle {
            (transitive) => {
                StrategicHeightOracle::transitive()
            };
            (simple) => {
                StrategicHeightOracle::simple()
            };
        }

        macro_rules! create_strategyitem {
            (($left:ident, $right:ident) -> inf) => {
                StrategyItem(StrategyWeight::Infinity, ($left, $right))
            };
            (($left:ident, $right:ident) -> $weight:literal) => {
                StrategyItem(StrategyWeight::Num($weight), ($left, $right))
            };
        }

        macro_rules! test_height {
            ($(
                $test_name:ident: {
                    oracle {
                        $transitive:tt
                    } with {$(
                        $var_name:ident = {$($dep:ident),* $(,)?};
                    )*} in {$(
                        ($left:ident, $right:ident) -> $weight:tt),* $(,)?
                    } expects {
                        $(($l:ident, $r:ident) -> $w:tt),* $(,)?
                    }
                };
            )*) => {
                $(
                    #[test]
                    #[allow(unused_variables)]
                    fn $test_name() {
                        for _ in 1..100 {
                            let (system, [$($var_name,)*]) = system_def! {$(
                                $var_name = {$($dep,)*};
                            )*};
                            let visited = HashSet::from_iter([$($var_name,)*]);

                            let relation = BinaryHeapStrategy::from_iter([$(create_strategyitem!{($left, $right) -> $weight},)*]);

                            let expected = BinaryHeapStrategy::from_iter([$(create_strategyitem!{($l, $r) -> $w},)*]);
                            let oracle = create_oracle!{$transitive};
                            let got = StrategicHeightOracle::get_updated_weights(&oracle, &visited, &system, &relation);

                            let expected_domain: HashSet<_> = expected.clone().domain();
                            let got_domain: HashSet<_> = got.clone().domain();

                            for v in &got_domain {
                                assert!(expected_domain.contains(v), "got domain contains {v:?} but shouldn't.");
                            }
                            for v in &expected_domain {
                                assert!(got_domain.contains(v), "got domain does not contain {v:?}");
                            }
                            assert_eq!(expected_domain, got.clone().domain(),
                                "wrong domain"
                            );
                            let got_map = got
                                    .into_iter()
                                    .map(|StrategyItem(w, (x, y))| ((x, y), w))
                                    .collect::<HashMap<_, _>>();
                            for StrategyItem(w, v) in expected.iter() {
                                let w_got = got_map.get(&v).expect(&*format!("{v:?} does not exist in got"));
                                assert_eq!(w, *w_got, "wrong weight for {v:?}");
                            }

                            assert_eq!(
                                expected.into_iter().map(|StrategyItem(w, (x, y))| ((x, y), w)).collect::<HashMap<_, _>>(),
                                got_map,
                                "wrong strategy"
                            );
                        }
                    }
                )*
            };
        }

        test_height! {
            single_variable_transitive: {
                oracle {
                    transitive
                } with {
                    x = {};
                } in {
                    (x, x) -> 0,
                } expects {
                    (x, x) -> 0,
                }
            };
            single_variable_simple: {
                oracle {
                    simple
                } with {
                    x = {};
                } in {
                    (x, x) -> 0,
                } expects {
                    (x, x) -> 0,
                }
            };
            chain_2_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1,
                }
            };
            chain_2_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1,
                }
            };
            chain_3_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {z};
                    z = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (y, x) -> 1, (z, x) -> 2, (z, y) -> 5,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (y, x) -> 1, (z, x) -> 2, (z, y) -> 5,
                }
            };
            chain_3_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {z};
                    z = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (y, x) -> 1, (z, x) -> 2, (z, y) -> 5,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (y, x) -> 1, (z, x) -> 6, (z, y) -> 5,
                }
            };
            chain_4_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {z};
                    z = {k};
                    k = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (k, k) -> 0, (y, x) -> 5, (z, x) -> 2, (k, x) -> 10, (z, y) -> 5, (k, y) -> 5, (k, z) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (k, k) -> 0, (y, x) -> 5, (z, x) -> 2, (k, x) -> 3, (z, y) -> 5, (k, y) -> 5, (k, z) -> 1,
                }
            };
            chain_4_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {z};
                    z = {k};
                    k = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (k, k) -> 0, (y, x) -> 5, (z, x) -> 2, (k, x) -> 10, (z, y) -> 5, (k, y) -> 5, (k, z) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (k, k) -> 0, (y, x) -> 5, (z, x) -> 10, (k, x) -> 11, (z, y) -> 5, (k, y) -> 6, (k, z) -> 1,
                }
            };
            chain_5_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {z};
                    z = {k};
                    k = {i};
                    i = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (k, k) -> 0, (i, i) -> 0, (y, x) -> 5, (z, x) -> 2, (k, x) -> 10, (i, x) -> 20, (z, y) -> 5, (k, y) -> 5, (i, y) -> 10, (k, z) -> 1, (i, z) -> 10, (i, k) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (k, k) -> 0, (i, i) -> 0, (y, x) -> 5, (z, x) -> 2, (k, x) -> 3, (i, x) -> 4, (z, y) -> 5, (k, y) -> 5, (i, y) -> 6, (k, z) -> 1, (i, z) -> 2, (i, k) -> 1,
                }
            };
            chain_5_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {z};
                    z = {k};
                    k = {i};
                    i = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (k, k) -> 0, (i, i) -> 0, (y, x) -> 5, (z, x) -> 2, (k, x) -> 10, (i, x) -> 20, (z, y) -> 5, (k, y) -> 5, (i, y) -> 10, (k, z) -> 1, (i, z) -> 10, (i, k) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (k, k) -> 0, (i, i) -> 0, (y, x) -> 5, (z, x) -> 10, (k, x) -> 11, (i, x) -> 12, (z, y) -> 5, (k, y) -> 6, (i, y) -> 7, (k, z) -> 1, (i, z) -> 2, (i, k) -> 1,
                }
            };
            bad_edge_transitive: {
                oracle {
                    transitive
                } with {
                    x = {z, y};
                    y = {};
                    z = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (z, x) -> 1, (y, x) -> 1, (y, z) -> 2,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (z, x) -> 1, (y, x) -> 1,
                }
            };
            bad_edge_simple: {
                oracle {
                    simple
                } with {
                    x = {z, y};
                    y = {};
                    z = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (z, x) -> 1, (y, x) -> 1, (y, z) -> 2,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (z, x) -> 1, (y, x) -> 1,
                }
            };
            bad_edge_circular_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (x, y) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1,
                }
            };
            bad_edge_circular_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (x, y) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1,
                }
            };
            edge_removed_in_relation_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y, z};
                    y = {};
                    z = {};
                } in {
                    (x, x) -> 0 , (y, y) -> 0, (y, x) ->1,
                } expects {
                    (x, x) -> 0 , (y, y) -> 0, (y, x) ->1,
                }
            };
            edge_removed_in_relation_simple: {
                oracle {
                    simple
                } with {
                    x = {y, z};
                    y = {};
                    z = {};
                } in {
                    (x, x) -> 0 , (y, y) -> 0, (y, x) ->1,
                } expects {
                    (x, x) -> 0 , (y, y) -> 0, (y, x) ->1,
                }
            };
            circular_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {x};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (x, y) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (x, y) -> 1,
                }
            };
            circular_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {x};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (x, y) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (x, y) -> 1,
                }
            };
            circular_2_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {x};
                } in {
                    (x, x) -> 5, (y, y) -> 5, (y, x) -> 1, (x, y) -> 1,
                } expects {
                    (x, x) -> 2, (y, y) -> 2, (y, x) -> 1, (x, y) -> 1,
                }
            };
            circular_2_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {x};
                } in {
                    (x, x) -> 5, (y, y) -> 5, (y, x) -> 1, (x, y) -> 1,
                } expects {
                    (x, x) -> 2, (y, y) -> 2, (y, x) -> 1, (x, y) -> 1,
                }
            };
            infinite_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> inf,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> inf,
                }
            };
            infinite_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> inf,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> inf,
                }
            };
            infinite_2_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {z};
                    z = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (y, x) -> 1, (z, x) -> inf, (z, y) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (y, x) -> 1, (z, x) -> 2, (z, y) -> 1,
                }
            };
            infinite_2_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {z};
                    z = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (y, x) -> 1, (z, x) -> inf, (z, y) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (z, z) -> 0, (y, x) -> 1, (z, x) -> 2, (z, y) -> 1,
                }
            };
            circular_infinite_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {x};
                } in {
                    (x, x) -> inf, (y, y) -> inf, (y, x) -> 1, (x, y) -> 1,
                } expects {
                    (x, x) -> 2, (y, y) -> 2, (y, x) -> 1, (x, y) -> 1,
                }
            };
            circular_infinite_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {x};
                } in {
                    (x, x) -> inf, (y, y) -> inf, (y, x) -> 1, (x, y) -> 1,
                } expects {
                    (x, x) -> 2, (y, y) -> 2, (y, x) -> 1, (x, y) -> 1,
                }
            };
            circular_infinite_2_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y};
                    y = {x};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> inf, (x, y) -> inf,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> inf, (x, y) -> inf,
                }
            };
            circular_infinite_2_simple: {
                oracle {
                    simple
                } with {
                    x = {y};
                    y = {x};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> inf, (x, y) -> inf,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> inf, (x, y) -> inf,
                }
            };
            relation_skipping_arg_1_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y, z};
                    y = {x};
                    z = {k};
                    k = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (k, x) -> 2,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1,
                }
            };
            relation_skipping_arg_1_simple: {
                oracle {
                    simple
                } with {
                    x = {y, z};
                    y = {x};
                    z = {k};
                    k = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (k, x) -> 2,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1,
                }
            };
            relation_skipping_arg_2_transitive: {
                oracle {
                    transitive
                } with {
                    x = {y, z};
                    y = {x};
                    z = {k};
                    k = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (k, x) -> 2, (k, z) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (k, z) -> 1,
                }
            };
            relation_skipping_arg_2_simple: {
                oracle {
                    simple
                } with {
                    x = {y, z};
                    y = {x};
                    z = {k};
                    k = {};
                } in {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (k, x) -> 2, (k, z) -> 1,
                } expects {
                    (x, x) -> 0, (y, y) -> 0, (y, x) -> 1, (k, z) -> 1,
                }
            };
            /*
            template: {
                oracle {

                } with {

                } in {

                } expects {

                }
            };
            */
        }
    }
}
