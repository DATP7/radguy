use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    hash::Hash,
    marker::PhantomData,
};

use radguy::DependencyGraphSystem;
use radguy::{Arguments, Assignment, PairUniverse, System, Universe, extension::TermSystem};
use slotmap::Key;

use crate::systems::{
    bool::{BoolSystem, BoolSystemImpl, BoolTerm},
    ccs::ast::Action,
    ccs::transition_system::TransitionSystem,
};

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum FlatProcess<'a, K: Key> {
    Nil,
    Named(&'a str),
    ActionPrefix {
        action: Action<'a>,
        process: K,
    },
    Restriction {
        process: K,
        // PERF: Make this Rc or borrowed so we don't clone as much
        restrictions: BTreeSet<&'a str>,
    },
    Relabelling {
        process: K,
        // PERF: Make this Rc or borrowed so we don't clone as much
        labels: BTreeMap<&'a str, &'a str>,
    },
    Sum(K, K),
    Compose(K, K),
}

#[derive(Default, Debug)]
pub struct BisimulationSystem<
    'a,
    ProcKey: Key,
    VarKey: Key,
    TermKey: Key,
    T: TransitionSystem<'a, ProcKey>,
> {
    bool_system: RefCell<BoolSystemImpl<VarKey, TermKey, (ProcKey, ProcKey)>>,
    transition_system: T,
    _lifetime: PhantomData<&'a ()>,
    locked: bool,
    hyper_edge_cache: RefCell<HashMap<VarKey, Vec<Vec<VarKey>>>>,
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    pub fn new(transition_generator: T) -> Self {
        Self {
            bool_system: RefCell::default(),
            transition_system: transition_generator,
            _lifetime: PhantomData,
            locked: false,
            hyper_edge_cache: RefCell::default(),
        }
    }

    pub fn print_definitions(&self) {
        self.bool_system.borrow().print_definitions();
    }

    pub fn specify_comparison(&mut self, left_process: &str, right_process: &str) -> VarKey {
        let left_key = *self
            .transition_system
            .lookup_process_key(left_process)
            .expect("s must be defined");
        let right_key = *self
            .transition_system
            .lookup_process_key(right_process)
            .expect("t must be defined");

        self.bool_system
            .borrow_mut()
            .names
            .get_or_insert_key((left_key, right_key))
    }

    fn expand(&self, var_key: VarKey) {
        debug_assert!(
            !self.locked,
            "A variable was expanded while the system was locked"
        );
        let (left_key, right_key) = *self.bool_system.borrow().names.get_value(var_key);

        if left_key == right_key {
            let term_key = self
                .bool_system
                .borrow_mut()
                .terms
                .get_or_insert_key(BoolTerm::False);

            self.bool_system
                .borrow_mut()
                .definitions
                .insert(var_key, term_key);

            return;
        }

        let left_transitions = self.transition_system.get_transitions(left_key);
        let right_transitions = self.transition_system.get_transitions(right_key);

        let left_actions = left_transitions.keys().copied().collect::<HashSet<_>>();
        let right_actions = right_transitions.keys().copied().collect::<HashSet<_>>();

        let empty_set = HashSet::new();

        // If avalible actions for the two processes do not match they are trivilay non bisimilar
        if left_actions != right_actions {
            let term_key = self
                .bool_system
                .borrow_mut()
                .terms
                .get_or_insert_key(BoolTerm::True);

            self.bool_system
                .borrow_mut()
                .definitions
                .insert(var_key, term_key);

            return;
        }

        let term_key = self.construct_disjunction(left_actions.into_iter().flat_map(|action| {
            let left_processes = left_transitions.get(&action).unwrap_or(&empty_set);
            let right_processes = right_transitions.get(&action).unwrap_or(&empty_set);

            // TODO: Move condition logic into new function on self. Then we can just chain
            // flatmaps
            let bisimulation_left_condition =
                self.construct_disjunction(left_processes.iter().map(|left_process| {
                    self.construct_conjunction(right_processes.iter().map(|right_process| {
                        let left_process_var_key = self
                            .bool_system
                            .borrow_mut()
                            .names
                            .get_or_insert_key((*left_process, *right_process));
                        let bool_term = BoolTerm::Variable(left_process_var_key);
                        self.bool_system
                            .borrow_mut()
                            .terms
                            .get_or_insert_key(bool_term)
                    }))
                }));

            let bisimulation_right_condition =
                self.construct_disjunction(right_processes.iter().map(|right_process| {
                    self.construct_conjunction(left_processes.iter().map(|left_process| {
                        let right_process_var_key = self
                            .bool_system
                            .borrow_mut()
                            .names
                            .get_or_insert_key((*left_process, *right_process));
                        let bool_term = BoolTerm::Variable(right_process_var_key);
                        self.bool_system
                            .borrow_mut()
                            .terms
                            .get_or_insert_key(bool_term)
                    }))
                }));

            [bisimulation_left_condition, bisimulation_right_condition]
        }));

        self.bool_system
            .borrow_mut()
            .definitions
            .insert(var_key, term_key);
    }

    fn construct_conjunction(&self, elements: impl Iterator<Item = TermKey>) -> TermKey {
        let elements = elements.collect();
        self.bool_system
            .borrow_mut()
            .terms
            .get_or_insert_key(BoolTerm::And(elements))
    }

    fn construct_disjunction(&self, elements: impl Iterator<Item = TermKey>) -> TermKey {
        let elements = elements.collect();
        self.bool_system
            .borrow_mut()
            .terms
            .get_or_insert_key(BoolTerm::Or(elements))
    }

    fn ensure_variable_defined(&self, variable: VarKey) {
        let term_key = {
            let sys = self.bool_system.borrow();
            sys.definitions.get(variable).copied()
        };

        if term_key.is_none() {
            self.expand(variable);
        }
    }
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    System<VarKey, bool> for BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    fn evaluate(&self, var_key: VarKey, assignment: &HashMap<VarKey, bool>) -> bool {
        self.ensure_variable_defined(var_key);
        self.bool_system.borrow().evaluate(var_key, assignment)
    }

    fn bottom_assignment(&self) -> HashMap<VarKey, bool> {
        HashMap::new()
    }

    fn lock(&mut self) {
        self.locked = true;
    }

    fn unlock(&mut self) {
        self.locked = false;
    }

    fn visited(&self) -> HashSet<VarKey> {
        self.bool_system.borrow().visited()
    }
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    Arguments<VarKey, HashSet<VarKey>> for BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    fn arguments(&self, var_key: VarKey) -> HashSet<VarKey> {
        let term_key = self.bool_system.borrow().definitions.get(var_key).copied();

        if term_key.is_none() {
            self.expand(var_key);
        }

        self.bool_system.borrow().arguments(var_key)
    }
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    Universe<HashSet<VarKey>> for BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    fn universe(&self) -> HashSet<VarKey> {
        self.bool_system.borrow().names.keys().collect()
    }
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    PairUniverse<HashSet<(VarKey, VarKey)>>
    for BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    fn pair_universe(&self) -> HashSet<(VarKey, VarKey)> {
        self.bool_system.borrow().pair_universe()
    }
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    TermSystem<VarKey, bool, TermKey> for BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        self.ensure_variable_defined(variable);
        self.bool_system.borrow().definition(variable)
    }
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    BoolSystem<VarKey, TermKey, (ProcKey, ProcKey)>
    for BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    fn get_term(&self, term_key: TermKey) -> BoolTerm<VarKey, TermKey> {
        self.bool_system.borrow().get_term(term_key)
    }

    fn evaluate_term(&self, term_key: TermKey, assignment: &dyn Assignment<VarKey, bool>) -> bool {
        self.bool_system
            .borrow()
            .evaluate_term(term_key, assignment)
    }
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    DependencyGraphSystem<VarKey, VarKey> for BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    fn get_hyperedges(&self, key: VarKey) -> Option<Vec<Vec<VarKey>>> {
        if let Some(hyperedge) = self.hyper_edge_cache.borrow().get(&key) {
            return Some(hyperedge.clone());
        }

        let term_key = *self.bool_system.borrow().definitions.get(key)?;

        let term = self.get_term(term_key);

        let hyperedge: Vec<Vec<VarKey>> = match term {
            BoolTerm::Or(items) => items
                .into_iter()
                .flat_map(|item| match self.get_term(item) {
                    BoolTerm::Or(items) => {
                        items.into_iter().map(|item| match self.get_term(item) {
                            BoolTerm::And(items) => items
                                .into_iter()
                                .map(|item| match self.get_term(item) {
                                    BoolTerm::Variable(var_key) => var_key,
                                    _ => unreachable!(
                                        "Variable not defined as a collection of hyperedge!"
                                    ),
                                })
                                .collect(),
                            _ => unreachable!("Variable not defined as a collection of hyperedge!"),
                        })
                    }
                    _ => unreachable!("Variable not defined as a collection of hyperedge!"),
                })
                .collect(),
            _ => unreachable!("Variable not defined as a collection of hyperedge!"),
        };

        self.hyper_edge_cache
            .borrow_mut()
            .insert(key, hyperedge.clone());

        Some(hyperedge)
    }
}
