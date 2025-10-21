use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use radguy::bislotmap::BiSlotMap;
use slotmap::{Key, SecondaryMap};

use crate::systems::ccs::{
    ast::{Action, Binding, Process},
    strong_bisimulation_system::FlatProcess,
    transition_system::TransitionSystem,
};

type TransitionMap<'a, ProcKey> = HashMap<Action<'a>, HashSet<ProcKey>>;

#[derive(Default, Debug)]
pub struct StrongTransitionSystem<'a, ProcKey: Key> {
    process_names: HashMap<&'a str, ProcKey>,
    process_bindings: RefCell<BiSlotMap<ProcKey, FlatProcess<'a, ProcKey>>>,
    transition_cache: RefCell<SecondaryMap<ProcKey, TransitionMap<'a, ProcKey>>>,
}

impl<'a, ProcKey: Key> StrongTransitionSystem<'a, ProcKey> {
    fn insert_process(&self, process: FlatProcess<'a, ProcKey>) -> ProcKey {
        self.process_bindings
            .borrow_mut()
            .get_or_insert_key(process)
    }

    fn get_process(&self, process_key: ProcKey) -> FlatProcess<'a, ProcKey> {
        self.process_bindings
            .borrow()
            .get_value(process_key)
            .clone()
    }

    fn insert_ast_process(&self, process: &Process<'a>) -> ProcKey {
        match process {
            Process::Nil => self.insert_process(FlatProcess::Nil),
            Process::Named(name) => self.insert_process(FlatProcess::Named(name)),
            Process::ActionPrefix { action, process } => {
                let flat_process_key = self.insert_ast_process(process);
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
                let flat_process_key = self.insert_ast_process(process);
                self.process_bindings
                    .borrow_mut()
                    .get_or_insert_key(FlatProcess::Restriction {
                        process: flat_process_key,
                        restrictions: restriction.clone(),
                    })
            }
            Process::Relabelling { process, labels } => {
                let flat_process_key = self.insert_ast_process(process);
                self.process_bindings
                    .borrow_mut()
                    .get_or_insert_key(FlatProcess::Relabelling {
                        process: flat_process_key,
                        labels: labels.clone(),
                    })
            }
            Process::Sum(left, right) => {
                let left_key = self.insert_ast_process(left);
                let right_key = self.insert_ast_process(right);
                self.process_bindings
                    .borrow_mut()
                    .get_or_insert_key(FlatProcess::Sum(left_key, right_key))
            }
            Process::Compose(left, right) => {
                let left_key = self.insert_ast_process(left);
                let right_key = self.insert_ast_process(right);
                self.process_bindings
                    .borrow_mut()
                    .get_or_insert_key(FlatProcess::Compose(left_key, right_key))
            }
        }
    }
}

impl<'a, ProcKey: Key> TransitionSystem<'a, ProcKey> for StrongTransitionSystem<'a, ProcKey> {
    fn lookup_process_key(&self, name: &str) -> Option<&ProcKey> {
        self.process_names.get(name)
    }

    fn load_ast(&mut self, ast: Vec<Binding<'a>>) {
        for binding in ast {
            let process_key = self.insert_ast_process(&binding.value);
            self.process_names.insert(binding.name, process_key);
        }
    }

    fn get_transitions(&self, process_key: ProcKey) -> TransitionMap<'a, ProcKey> {
        if let Some(transitions) = self.transition_cache.borrow().get(process_key) {
            return transitions.clone(); // PERF: Remove this damn clone
        }

        let process = self.get_process(process_key);

        let empty_set = HashSet::<ProcKey>::new();

        let result = match process {
            FlatProcess::Nil => HashMap::new(),
            FlatProcess::Named(name) => self.get_transitions(
                *self
                    .lookup_process_key(name)
                    .expect("all process names should have been maped"),
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
                .map(|(action, targets)| {
                    (
                        action,
                        targets
                            .into_iter()
                            .map(|process| {
                                self.insert_process(FlatProcess::Restriction {
                                    process,
                                    restrictions: restrictions.clone(),
                                })
                            })
                            .collect(),
                    )
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
                .map(|(action, targets)| {
                    (
                        action,
                        targets
                            .into_iter()
                            .map(|process| {
                                self.insert_process(FlatProcess::Relabelling {
                                    process,
                                    labels: labels.clone(),
                                })
                            })
                            .collect(),
                    )
                })
                .collect(),
            FlatProcess::Sum(left, right) => {
                let left_transitions = self.get_transitions(left);
                let right_transitions = self.get_transitions(right);
                let keys: HashSet<Action> = left_transitions
                    .keys()
                    .chain(right_transitions.keys())
                    .copied()
                    .collect();

                keys.into_iter()
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

                let mut successors = TransitionMap::new();

                for (left_action, left_processes) in left_transitions {
                    let mut current_succesors_processes = HashSet::<ProcKey>::new();
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
                                    let current_sync_processes = right_successors
                                        .iter()
                                        .map(|right_successor| {
                                            let composed_process = FlatProcess::Compose(
                                                left_successor,
                                                *right_successor,
                                            );
                                            self.process_bindings
                                                .borrow_mut()
                                                .get_or_insert_key(composed_process)
                                        })
                                        .collect::<HashSet<ProcKey>>();

                                    if !current_sync_processes.is_empty() {
                                        successors
                                            .entry(Action::Tau)
                                            .or_default()
                                            .extend(current_sync_processes);
                                    }
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
        };
        self.transition_cache
            .borrow_mut()
            .insert(process_key, result.clone());
        result
    }
}
