use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    hash::Hash,
};

use itertools::iproduct;
use radguy::{Assignment, System, bislotmap::BiSlotMap};
use slotmap::{DefaultKey, Key};

use crate::systems::{
    bool::{BoolSystem, BoolTerm},
    ccs::ast::{Action, Binding, Process},
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
pub struct StrongBisimulationSystem<'a> {
    bool_system: RefCell<BoolSystem<DefaultKey, DefaultKey, (DefaultKey, DefaultKey)>>,
    process_names: HashMap<&'a str, DefaultKey>,
    process_bindings: RefCell<BiSlotMap<DefaultKey, FlatProcess<'a, DefaultKey>>>,
}

impl<'a> StrongBisimulationSystem<'a> {
    pub fn print_definitions(&self) {
        self.bool_system.borrow().print_definitions();
    }

    fn generate_next_variables(
        &self,
        left_key: DefaultKey,
        right_key: DefaultKey,
    ) -> HashSet<(DefaultKey, DefaultKey)> {
        let left_transitions = self.get_transitions(left_key);
        let right_transitions = self.get_transitions(right_key);

        let mut local_pairs = HashSet::<(DefaultKey, DefaultKey)>::new();

        // Dummy set placed here to allocate once. unwrap_or_else cannot return a borrowed value
        let empty_set = HashSet::new();
        for (action, left_processes) in left_transitions {
            let right_processes = right_transitions.get(&action).unwrap_or(&empty_set);
            let combinations: HashSet<(DefaultKey, DefaultKey)> =
                iproduct!(left_processes.into_iter(), right_processes.iter().copied())
                    .filter(|val| !self.bool_system.borrow().names.contains_value(val))
                    .collect();

            local_pairs.extend(combinations);
        }

        local_pairs
    }

    fn load_variables(&mut self, left_key: DefaultKey, right_key: DefaultKey) {
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

    /// TODO: this can and probably should be cached (CAAL does it)
    fn get_transitions(&self, process_key: DefaultKey) -> HashMap<Action<'a>, HashSet<DefaultKey>> {
        let process = self
            .process_bindings
            .borrow_mut()
            .get_value(process_key)
            .clone();

        // Dummy set placed here to allocate once. unwrap_or_else cannot return a borrowed value
        let empty_set = HashSet::new();

        match process {
            FlatProcess::Nil => HashMap::new(),
            FlatProcess::Named(name) => self.get_transitions(
                *self
                    .process_names
                    .get(name)
                    .expect("name should be defined"),
            ),
            FlatProcess::ActionPrefix { action, process } => {
                HashMap::from([(action, HashSet::from([process]))])
            }
            FlatProcess::Restriction {
                process,
                restrictions,
            } => self
                .get_transitions(process)
                .into_iter()
                .filter(|(action, _)| match action {
                    Action::Label { name, .. } => !restrictions.contains(name),
                    Action::Tau => true,
                })
                .collect(),
            FlatProcess::Relabelling { process, labels } => self
                .get_transitions(process)
                .into_iter()
                .map(|(action, process)| match action {
                    Action::Label {
                        name,
                        is_complement,
                    } => (
                        Action::Label {
                            name: labels.get(name).unwrap_or(&name),
                            is_complement,
                        },
                        process,
                    ),
                    Action::Tau => (action, process),
                })
                .collect(),
            FlatProcess::Sum(left, right) => {
                let left_transitions = self.get_transitions(left);
                let right_transitions = self.get_transitions(right);
                left_transitions
                    .keys()
                    .chain(right_transitions.keys())
                    .copied()
                    .map(|action| {
                        (
                            action,
                            left_transitions
                                .get(&action)
                                .unwrap_or(&empty_set)
                                .union(right_transitions.get(&action).unwrap_or(&empty_set))
                                .copied()
                                .collect(),
                        )
                    })
                    .collect()
            }
            FlatProcess::Compose(left, right) => {
                let left_transitions = self.get_transitions(left);
                let right_tansitions = self.get_transitions(right);

                let mut successors = HashMap::<Action, HashSet<DefaultKey>>::new();

                for (left_action, left_processes) in left_transitions {
                    let mut current_succesors_processes = HashSet::new();
                    for left_successor in left_processes {
                        let composed_process = FlatProcess::Compose(left_successor, right);
                        let composed_process_key = self
                            .process_bindings
                            .borrow_mut()
                            .get_or_insert_key(composed_process);
                        current_succesors_processes.insert(composed_process_key);

                        // find sync actions
                        match left_action {
                            Action::Label {
                                name,
                                is_complement,
                            } => {
                                let co_action = Action::Label {
                                    name,
                                    is_complement: !is_complement,
                                };
                                if let Some(right_successors) = right_tansitions.get(&co_action) {
                                    let current_sync_processes =
                                        right_successors.iter().map(|right_successor| {
                                            let composed_process = FlatProcess::Compose(
                                                left_successor,
                                                *right_successor,
                                            );
                                            self.process_bindings
                                                .borrow_mut()
                                                .get_or_insert_key(composed_process)
                                        });

                                    successors
                                        .entry(Action::Tau)
                                        .or_default()
                                        .extend(current_sync_processes);
                                }
                            }
                            Action::Tau => {}
                        }
                    }

                    successors
                        .entry(left_action)
                        .or_default()
                        .extend(current_succesors_processes);
                }

                for (right_action, right_processes) in right_tansitions {
                    let current_succesors_processes =
                        right_processes.iter().map(|right_successor| {
                            let composed_process = FlatProcess::Compose(left, *right_successor);
                            self.process_bindings
                                .borrow_mut()
                                .get_or_insert_key(composed_process)
                        });
                    successors
                        .entry(right_action)
                        .or_default()
                        .extend(current_succesors_processes);
                }

                successors
            }
        }
    }

    pub fn load_ast(&mut self, ast: Vec<Binding<'a>>) {
        // Loop over each binding
        for binding in ast {
            let process_key = self.get_process_key(&binding.value);
            self.process_names.insert(binding.name, process_key);
        }
    }

    fn get_process_key(&self, process: &Process<'a>) -> DefaultKey {
        match process {
            Process::Nil => self
                .process_bindings
                .borrow_mut()
                .get_or_insert_key(FlatProcess::Nil),
            Process::Named(name) => self
                .process_bindings
                .borrow_mut()
                .get_or_insert_key(FlatProcess::Named(name)),
            Process::ActionPrefix { action, process } => {
                let flat_process_key = self.get_process_key(process);
                self.process_bindings
                    .borrow_mut()
                    .get_or_insert_key(FlatProcess::ActionPrefix {
                        action: *action,
                        process: flat_process_key,
                    })
            }
            Process::Restriction {
                process,
                restriction,
            } => {
                let flat_process_key = self.get_process_key(process);
                self.process_bindings
                    .borrow_mut()
                    .get_or_insert_key(FlatProcess::Restriction {
                        process: flat_process_key,
                        restrictions: restriction.clone(),
                    })
            }
            Process::Relabelling { process, labels } => {
                let flat_process_key = self.get_process_key(process);
                self.process_bindings
                    .borrow_mut()
                    .get_or_insert_key(FlatProcess::Relabelling {
                        process: flat_process_key,
                        labels: labels.clone(),
                    })
            }
            Process::Sum(left, right) => {
                let left_key = self.get_process_key(left);
                let right_key = self.get_process_key(right);
                self.process_bindings
                    .borrow_mut()
                    .get_or_insert_key(FlatProcess::Sum(left_key, right_key))
            }
            Process::Compose(left, right) => {
                let left_key = self.get_process_key(left);
                let right_key = self.get_process_key(right);
                self.process_bindings
                    .borrow_mut()
                    .get_or_insert_key(FlatProcess::Compose(left_key, right_key))
            }
        }
    }

    /// Creates a key for a pair of variables, which can be used to tell the system which processes
    /// to check for strong bisimulation.
    pub fn specify_comparison(&mut self, left_process: &str, right_process: &str) -> DefaultKey {
        let left_key = *self
            .process_names
            .get(left_process)
            .expect("s must be defined");
        let right_key = *self
            .process_names
            .get(right_process)
            .expect("t must be defined");

        self.load_variables(left_key, right_key);

        self.bool_system
            .borrow_mut()
            .names
            .get_or_insert_key((left_key, right_key))
    }

    fn expand(&self, (left_key, right_key): &(DefaultKey, DefaultKey)) {
        let left_transitions = self.get_transitions(*left_key);
        let right_transitions = self.get_transitions(*right_key);

        let left_actions = left_transitions.keys().copied().collect::<HashSet<_>>();
        let right_actions = right_transitions.keys().copied().collect::<HashSet<_>>();

        let empty_set = HashSet::new();

        let var_key = self
            .bool_system
            .borrow_mut()
            .names
            .get_or_insert_key((*left_key, *right_key));

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

    /// Logical And (because Markus gets confused)
    fn construct_conjunction(&self, mut elements: impl Iterator<Item = DefaultKey>) -> DefaultKey {
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
    /// Logical Or (because Markus gets confused)
    fn construct_disjunction(&self, mut elements: impl Iterator<Item = DefaultKey>) -> DefaultKey {
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

impl System<DefaultKey, bool, HashSet<(DefaultKey, DefaultKey)>, HashSet<DefaultKey>>
    for StrongBisimulationSystem<'_>
{
    fn evaluate(&self, var_key: DefaultKey, assignment: &dyn Assignment<DefaultKey, bool>) -> bool {
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

    fn arguments(&self, var_key: DefaultKey) -> HashSet<DefaultKey> {
        let term_key = {
            let sys = self.bool_system.borrow();
            sys.definitions.get(var_key).copied()
        };

        if term_key.is_none() {
            self.expand(self.bool_system.borrow().names.get_value(var_key));
        }

        self.bool_system.borrow().arguments(var_key)
    }

    fn variables(&self) -> HashSet<DefaultKey> {
        self.bool_system.borrow().names.keys().collect()
    }

    fn bottom_assignment(&self) -> impl Assignment<DefaultKey, bool> {
        HashMap::new()
    }
}
