use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    hash::Hash,
    marker::PhantomData,
};

use itertools::iproduct;
use radguy::{Arguments, Assignment, PairUniverse, System, Universe};
use slotmap::Key;

use crate::systems::{
    bool::{BoolSystem, BoolTerm},
    ccs::{ast::Action, transition_system::TransitionSystem},
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
    bool_system: RefCell<BoolSystem<VarKey, TermKey, (ProcKey, ProcKey)>>,
    transition_system: T,
    _lifetime: PhantomData<&'a ()>,
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    pub fn new(transition_generator: T) -> Self {
        Self {
            bool_system: RefCell::default(),
            transition_system: transition_generator,
            _lifetime: PhantomData,
        }
    }

    pub fn print_definitions(&self) {
        self.bool_system.borrow().print_definitions();
    }

    fn generate_next_variables(
        &self,
        left_key: ProcKey,
        right_key: ProcKey,
    ) -> HashSet<(ProcKey, ProcKey)> {
        let left_transitions = self.transition_system.get_transitions(left_key);
        let right_transitions = self.transition_system.get_transitions(right_key);

        // PERF: Different set structure
        let mut local_pairs = HashSet::<(ProcKey, ProcKey)>::new();

        // Dummy set placed here to allocate once. unwrap_or_else cannot return a borrowed value
        let empty_set = HashSet::new();
        for (action, left_processes) in left_transitions {
            let right_processes = right_transitions.get(&action).unwrap_or(&empty_set);
            let combinations: HashSet<(ProcKey, ProcKey)> =
                iproduct!(left_processes.into_iter(), right_processes.iter().copied())
                    .filter(|val| !self.bool_system.borrow().names.contains_value(val))
                    .collect();

            local_pairs.extend(combinations);
        }

        local_pairs
    }

    fn load_variables(&mut self, left_key: ProcKey, right_key: ProcKey) {
        if self
            .bool_system
            .borrow_mut()
            .names
            .contains_value(&(left_key, right_key))
        {
            return;
        }

        let local_variables = self.generate_next_variables(left_key, right_key);

        for (left_key, right_key) in local_variables {
            self.bool_system
                .borrow_mut()
                .names
                .get_or_insert_key((left_key, right_key));
            self.load_variables(left_key, right_key);
        }
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

        self.load_variables(left_key, right_key);

        self.bool_system
            .borrow_mut()
            .names
            .get_or_insert_key((left_key, right_key))
    }

    fn expand(&self, (left_key, right_key): &(ProcKey, ProcKey)) {
        let var_key = self
            .bool_system
            .borrow_mut()
            .names
            .get_or_insert_key((*left_key, *right_key));

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

        let left_transitions = self.transition_system.get_transitions(*left_key);
        let right_transitions = self.transition_system.get_transitions(*right_key);

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

    fn construct_conjunction(&self, mut elements: impl Iterator<Item = TermKey>) -> TermKey {
        let Some(left_term_key) = elements.next() else {
            return self
                .bool_system
                .borrow_mut()
                .terms
                .get_or_insert_key(BoolTerm::True);
        };

        let right_term_key = self.construct_conjunction(elements);

        self.bool_system
            .borrow_mut()
            .terms
            .get_or_insert_key(BoolTerm::And(left_term_key, right_term_key))
    }

    // TODO: this is repeditive
    fn construct_disjunction(&self, mut elements: impl Iterator<Item = TermKey>) -> TermKey {
        let Some(left_term_key) = elements.next() else {
            return self
                .bool_system
                .borrow_mut()
                .terms
                .get_or_insert_key(BoolTerm::False);
        };

        let right_term_key = self.construct_disjunction(elements);

        self.bool_system
            .borrow_mut()
            .terms
            .get_or_insert_key(BoolTerm::Or(left_term_key, right_term_key))
    }
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    System<VarKey, bool> for BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    fn evaluate(&self, var_key: VarKey, assignment: &dyn Assignment<VarKey, bool>) -> bool {
        let term_key = {
            let sys = self.bool_system.borrow();
            sys.definitions.get(var_key).copied()
        };

        if term_key.is_none() {
            let pair = {
                let sys = self.bool_system.borrow();
                *sys.names.get_value(var_key)
            };
            self.expand(&pair);
        }

        self.bool_system.borrow().evaluate(var_key, assignment)
    }

    fn bottom_assignment(&self) -> impl Assignment<VarKey, bool> {
        HashMap::new()
    }
}

impl<'a, ProcKey: Key, VarKey: Key, TermKey: Key, T: TransitionSystem<'a, ProcKey>>
    Arguments<VarKey, HashSet<VarKey>> for BisimulationSystem<'a, ProcKey, VarKey, TermKey, T>
{
    fn arguments(&self, var_key: VarKey) -> HashSet<VarKey> {
        let term_key = {
            let sys = self.bool_system.borrow();
            sys.definitions.get(var_key).copied()
        };

        if term_key.is_none() {
            self.expand(self.bool_system.borrow().names.get_value(var_key));
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
