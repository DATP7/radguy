use std::{
    cell::RefCell,
    collections::{BTreeMap, HashMap, HashSet},
};

use radguy::bislotmap::BiSlotMap;
use slotmap::{Key, SecondaryMap};

use crate::systems::ccs::{
    ast::{Action, Binding, Process},
    bisimulation_system::FlatProcess,
    transition_system::{TransitionMap, TransitionSystem},
};

#[derive(Default, Debug)]
pub struct StrongTransitionSystem<'a, ProcKey: Key> {
    process_names: HashMap<&'a str, ProcKey>,
    process_bindings: RefCell<BiSlotMap<ProcKey, FlatProcess<'a, ProcKey>>>,
    transition_cache: RefCell<SecondaryMap<ProcKey, TransitionMap<'a, ProcKey>>>,
    normalisation_cache: RefCell<SecondaryMap<ProcKey, ProcKey>>,
}

impl<'a, ProcKey: Key> StrongTransitionSystem<'a, ProcKey> {
    fn insert_process(&self, process: FlatProcess<'a, ProcKey>) -> ProcKey {
        self.process_bindings
            .borrow_mut()
            .get_or_insert_key(process)
    }

    pub fn get_process(&self, process_key: ProcKey) -> FlatProcess<'a, ProcKey> {
        self.process_bindings
            .borrow()
            .get_value(process_key)
            .clone()
    }

    pub fn process_to_string(&self, process_key: ProcKey) -> String {
        let proc = self.get_process(process_key);
        match proc {
            FlatProcess::Nil => "0".to_owned(),
            FlatProcess::Named(name) => name.to_owned(),
            FlatProcess::ActionPrefix { action, process } => {
                format!("{action}.{}", self.process_to_string(process))
            }
            FlatProcess::Restriction {
                process,
                restrictions,
            } => format!(
                "({})\\{{{}}}",
                self.process_to_string(process),
                restrictions.iter().copied().collect::<Vec<_>>().join(", "),
            ),
            FlatProcess::Relabelling { process, labels } => format!(
                "({})[{}]",
                self.process_to_string(process),
                labels
                    .iter()
                    .map(|(from, to)| format!("{to}/{from}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            FlatProcess::Sum(lhs, rhs) => format!(
                "({}) + ({})",
                self.process_to_string(lhs),
                self.process_to_string(rhs)
            ),
            FlatProcess::Compose(lhs, rhs) => format!(
                "({}) | ({})",
                self.process_to_string(lhs),
                self.process_to_string(rhs)
            ),
        }
    }

    pub fn insert_ast_process(&self, process: &Process<'a>) -> ProcKey {
        let proc_key = match process {
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
        };
        self.get_normalized_process(proc_key)
    }
    pub fn get_normalized_process(&self, key: ProcKey) -> ProcKey {
        if let Some(norm_key) = self.normalisation_cache.borrow().get(key) {
            return *norm_key;
        }
        // TODO potentially cache this
        let process = self.get_process(key);
        let norm_proc_key = match process {
            FlatProcess::Nil | FlatProcess::Named(..) => key,
            FlatProcess::ActionPrefix {
                action,
                process: inner_key,
            } => {
                let inner_normalized = self.get_normalized_process(inner_key);
                let new_process = FlatProcess::ActionPrefix {
                    action,
                    process: inner_normalized,
                };
                self.process_bindings
                    .borrow_mut()
                    .get_or_insert_key(new_process)
            }
            FlatProcess::Restriction {
                process,
                restrictions,
            } => self.normalize_restriction(process, restrictions),
            FlatProcess::Relabelling { process, labels } => {
                self.normalize_relabelling(process, labels)
            }
            FlatProcess::Sum(a, b) => {
                let a = self.get_normalized_process(a);
                let b = self.get_normalized_process(b);
                let new = if a < b {
                    FlatProcess::Sum(a, b)
                } else {
                    FlatProcess::Sum(b, a)
                };
                self.process_bindings.borrow_mut().get_or_insert_key(new)
            }
            FlatProcess::Compose(a, b) => {
                let a = self.get_normalized_process(a);
                let b = self.get_normalized_process(b);
                let new = if a < b {
                    FlatProcess::Compose(a, b)
                } else {
                    FlatProcess::Compose(b, a)
                };
                self.process_bindings.borrow_mut().get_or_insert_key(new)
            }
        };

        self.normalisation_cache
            .borrow_mut()
            .insert(key, norm_proc_key);

        norm_proc_key
    }

    fn normalize_relabelling(
        &self,
        process: ProcKey,
        labels: std::collections::BTreeMap<&'a str, &'a str>,
    ) -> ProcKey {
        let inner_normalized = self.get_normalized_process(process);
        if labels.is_empty() {
            inner_normalized
        } else {
            match self.get_process(inner_normalized) {
                FlatProcess::Nil => inner_normalized,
                FlatProcess::Relabelling {
                    process,
                    labels: labels_inner,
                } => {
                    // we want to clone the actual map here not just the reference, so we specifically use the clone on BTreeMap,
                    // so we get an error when we change to RC
                    let new_labels = relabelling_logic(&labels_inner, &labels);
                    self.process_bindings
                        .borrow_mut()
                        .get_or_insert_key(FlatProcess::Relabelling {
                            process,
                            labels: new_labels,
                        })
                }
                FlatProcess::Sum(a, b) => {
                    let a = self.get_normalized_process(a);
                    let b = self.get_normalized_process(b);
                    let a_relabeled = self.process_bindings.borrow_mut().get_or_insert_key(
                        FlatProcess::Relabelling {
                            process: a,
                            labels: labels.clone(),
                        },
                    );
                    let b_relabeled = self
                        .process_bindings
                        .borrow_mut()
                        .get_or_insert_key(FlatProcess::Relabelling { process: b, labels });
                    self.process_bindings
                        .borrow_mut()
                        .get_or_insert_key(FlatProcess::Sum(a_relabeled, b_relabeled))
                }
                FlatProcess::Named(..)
                | FlatProcess::ActionPrefix { .. }
                | FlatProcess::Compose(..)
                | FlatProcess::Restriction { .. } => self
                    .process_bindings
                    .borrow_mut()
                    .get_or_insert_key(FlatProcess::Relabelling {
                        process: inner_normalized,
                        labels,
                    }),
            }
        }
    }

    fn normalize_restriction(
        &self,
        process: ProcKey,
        restrictions: std::collections::BTreeSet<&'a str>,
    ) -> ProcKey {
        let inner_normalized = self.get_normalized_process(process);
        if restrictions.is_empty() {
            inner_normalized
        } else {
            match self.get_process(inner_normalized) {
                FlatProcess::Nil => inner_normalized,
                FlatProcess::Restriction {
                    process,
                    restrictions: inner_restriction,
                } => {
                    self.process_bindings
                        .borrow_mut()
                        .get_or_insert_key(FlatProcess::Restriction {
                            process,
                            restrictions: restrictions.union(&inner_restriction).copied().collect(),
                        })
                }
                FlatProcess::Sum(a, b) => {
                    let a = self.get_normalized_process(a);
                    let b = self.get_normalized_process(b);
                    let a_restricted = self.process_bindings.borrow_mut().get_or_insert_key(
                        FlatProcess::Restriction {
                            process: a,
                            restrictions: restrictions.clone(),
                        },
                    );
                    let b_restricted = self.process_bindings.borrow_mut().get_or_insert_key(
                        FlatProcess::Restriction {
                            process: b,
                            restrictions,
                        },
                    );
                    self.process_bindings
                        .borrow_mut()
                        .get_or_insert_key(FlatProcess::Sum(a_restricted, b_restricted))
                }
                FlatProcess::Named(..)
                | FlatProcess::ActionPrefix { .. }
                | FlatProcess::Relabelling { .. }
                | FlatProcess::Compose(..) => {
                    self.process_bindings
                        .borrow_mut()
                        .get_or_insert_key(FlatProcess::Restriction {
                            process: inner_normalized,
                            restrictions,
                        })
                }
            }
        }
    }
}

fn relabelling_logic<'a>(
    labels1: &BTreeMap<&'a str, &'a str>,
    labels2: &BTreeMap<&'a str, &'a str>,
) -> BTreeMap<&'a str, &'a str> {
    let mut new_labels1 = BTreeMap::clone(labels1);
    for (key, value) in labels1 {
        if let Some(new_value) = labels2.get(value) {
            new_labels1.insert(key, new_value);
        }
    }
    new_labels1.append(&mut labels2.clone());
    new_labels1
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
        let process_key = self.get_normalized_process(process_key);
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
                    .expect("all process names should have been mapped"),
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
                .map(|(action, targets)| match action {
                    Action::Label {
                        name,
                        is_complement,
                    } => (
                        Action::Label {
                            name: labels.get(name).unwrap_or(&name),
                            is_complement,
                        },
                        targets,
                    ),
                    Action::Tau => (action, targets),
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

        let result: TransitionMap<_> = result
            .into_iter()
            .map(|(act, targets)| {
                (
                    act,
                    targets
                        .into_iter()
                        .map(|target| self.get_normalized_process(target))
                        .collect(),
                )
            })
            .collect();

        self.transition_cache
            .borrow_mut()
            .insert(process_key, result.clone());

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::systems::ccs::grammar::ProgramParser;
    use crate::systems::ccs::strong_transition_system::Action;
    use crate::systems::ccs::strong_transition_system::Process;
    use crate::systems::ccs::strong_transition_system::StrongTransitionSystem;
    use crate::systems::ccs::transition_system::TransitionMap;
    use crate::systems::ccs::transition_system::TransitionSystem;
    use slotmap::DefaultKey;

    macro_rules! test_compose_labels {
        ($($first:expr, $second:expr => $result:expr;)*) => {
            $(
                assert_eq!(
                    relabelling_logic(&BTreeMap::from($first), &BTreeMap::from($second)),
                    BTreeMap::from($result)
                );
            )*
        };
    }

    #[test]
    fn test_compose_labels() {
        test_compose_labels! {
            [("a", "b")], [("b", "c")] => [("a", "c"), ("b", "c")];
            [("a", "d")], [("b", "c")] => [("a", "d"), ("b", "c")];
            [("a", "b"), ("d", "c")], [("b", "c")] => [("a", "c"), ("b", "c"), ("d", "c")];
            [("a", "b")], [("b", "c"), ("d", "c")] => [("a", "c"), ("b", "c"), ("d", "c")];
            [("a", "b"), ("b", "c")], [("c", "d")] => [("a", "b"), ("b", "d"), ("c", "d")];
        };
    }

    macro_rules! transition_set {
        ($lts:expr;) => {TransitionMap::new()};
        ($lts:expr;$($action:expr => $target:expr),*) => {{
            let mut transitions = TransitionMap::new();
            $(
                let action = Action::parse($action);
                let target = Process::parse($target);
                let target = $lts.insert_ast_process(&target);
                transitions.entry(action).or_default().insert(target);
            )*
            transitions
        }};
    }
    macro_rules! transition_tests {
        ($($name:ident: $proc:expr => [$($action:expr => $target:expr),*] $(in $ccs:expr)?;)*) => {
            $(
            #[test]
            #[allow(unused_variables)]
            fn $name() {
                #[allow(unused_mut)]
                let mut lts = StrongTransitionSystem::<DefaultKey>::default();
                $(
                    let parser = ProgramParser::new();
                    let ast = parser
                        .parse(&$ccs)
                        .expect("Failed to parse CCS program content.");
                    lts.load_ast(ast);
                )?
                let proc = Process::parse($proc);
                let key = lts.insert_ast_process(&proc);
                let transitions = lts.get_transitions(key);
                let expected = transition_set![lts; $($action => $target),*];

                println!("expected:");
                for (act, procs) in &expected {
                    println!("{act} => {:?}", procs.iter().map(|proc| lts.process_to_string(*proc)).collect::<Vec<_>>());
                }
                println!("got:");
                for (act, procs) in &transitions {
                    println!("{act} => {:?}", procs.iter().map(|proc| lts.process_to_string(*proc)).collect::<Vec<_>>());
                }

                assert_eq!(transitions, expected)
            }
            )*
        };
    }

    transition_tests! {
        nil: "0" => [];
        simple_sum: "a.a.0 + b.b.0" => ["a" => "a.0", "b" => "b.0"];
        simple_compose: "a.0 | b.0" => ["a" => "0 | b.0", "b" => "a.0 | 0"];
        simple_tau: "a.0 | 'a.0" => ["a" => "0 | 'a.0", "'a" => "a.0 | 0", "tau" => "0 | 0"];
        restrict_retained: "(a.b.0) \\ {b}" => ["a" => "(b.0) \\ {b}"];
        sum_restrict: "(a.b.0 + b.b.0) \\ {b}" => ["a" => "(b.0) \\ {b}"];
        compose_restrict: "(a.b.0 | b.b.0) \\ {b}" => ["a" => "(b.0 | b.b.0) \\ {b}"];
        restrict_to_nothing: "(a.b.0) \\ {a}" => [];
        tau_in_restrict: "(a.0 | 'a.0) \\ {a}" => ["tau" => "(0 | 0) \\ {a}"];
        restrict_left_of_tau: "((a.0) \\ {a}) | 'a.0" => ["'a" => "((a.0) \\ {a}) | 0"];
        restrict_right_of_tau: "a.0  | (('a.0) \\ {a})" => ["a" => "0  | (('a.0) \\ {a})"];
        relabel_retained: "(a.b.0)[b/c]" => ["a" => "(b.0)[b/c]"];
        simple_relabel: "(a.b.0)[c/a]" => ["c" => "(b.0)[c/a]"];
        tau_in_relabel: "(a.0 | 'a.0)[b/a]" => ["b" => "(0 | 'a.0)[b/a]", "'b" => "(a.0 | 0)[b/a]", "tau" => "(0 | 0)[b/a]"];
        relabel_to_left_of_tau: "((b.0)[a/b]) | 'a.0" => ["a" => "(0)[a/b] | 'a.0", "'a" => "((b.0)[a/b]) | 0", "tau" => "(0)[a/b] | 0"];
        relabel_from_left_of_tau: "((a.0)[b/a]) | 'a.0" => ["b" => "(0)[b/a] | 'a.0", "'a" => "((a.0)[b/a]) | 0"];
        restrict_then_relabel: "((a.0) \\ {a})[b/a]" => [];
        relabel_then_restrict: "((a.0)[b/a]) \\ {a}" => ["b" => "((0)[b/a]) \\ {a}"];
        simple_named: "A" => ["a" => "b.0"] in "A = a.b.0;";
        restrict_named: "A \\ {a}" => [] in "A = a.b.0;";
        restrict_named_retained: "A \\ {b}" => ["a" => "(b.0) \\ {b}"] in "A = a.b.0;";
        relabel_named: "A[b/a]" => ["b" => "(b.0)[b/a]"] in "A = a.b.0;";
        tau_through_named: "A | 'a.0" => ["a" => "0 | 'a.0", "'a" => "A | 0", "tau" => "0 | 0"] in "A = a.0;";
    }
}
