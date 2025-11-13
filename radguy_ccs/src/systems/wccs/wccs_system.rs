#![allow(clippy::vec_init_then_push)]
use std::{
    cell::RefCell,
    cmp::max,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
};

use radguy::bislotmap::BiSlotMap;
use slotmap::{Key, SecondaryMap};

use crate::systems::wccs::ast::{Action, Binding, Process, WeightedAction};

pub type TransitionMap<'a, ProcKey> = HashMap<WeightedAction<'a>, HashSet<ProcKey>>;

#[derive(Hash, Eq, PartialEq, Clone, Debug)]
pub enum FlatProcess<'a, ProcKey: Key> {
    Nil,
    Named(&'a str),
    ActionPrefix {
        action: WeightedAction<'a>,
        process: ProcKey,
    },
    Restriction {
        process: ProcKey,
        // PERF: Make this Rc or borrowed so we don't clone as much
        restrictions: BTreeSet<&'a str>,
    },
    ActionRelabelling {
        process: ProcKey,
        // PERF: Make this Rc or borrowed so we don't clone as much
        labels: BTreeMap<&'a str, &'a str>,
    },
    PropositionRelabelling {
        process: ProcKey,
        // PERF: Make this Rc or borrowed so we don't clone as much
        labels: BTreeMap<&'a str, &'a str>,
    },
    Sum(ProcKey, ProcKey),
    Compose(ProcKey, ProcKey),
    AtomicProposition {
        propositions: Vec<&'a str>,
        process: ProcKey,
    },
}

pub trait MultiSet<T: Eq> {
    fn count(&self, elem: T) -> usize;
}

impl<T: Eq + Copy> MultiSet<T> for Vec<T> {
    fn count(&self, elem: T) -> usize {
        self.iter().copied().filter(|x| *x == elem).count()
    }
}

#[derive(Default, Debug)]
pub struct WCCSSystem<'a, ProcKey: Key> {
    process_map: RefCell<BiSlotMap<ProcKey, FlatProcess<'a, ProcKey>>>,
    bindings: HashMap<&'a str, ProcKey>,
    transition_cache: RefCell<SecondaryMap<ProcKey, TransitionMap<'a, ProcKey>>>,
}

impl<'a, ProcKey: Key> WCCSSystem<'a, ProcKey> {
    pub fn lookup_process(&self, process_name: &'a str) -> Option<&ProcKey> {
        self.bindings.get(process_name)
    }
    pub fn get_propositions(&self, process_key: ProcKey) -> Vec<&'a str> {
        let process = self.get_process(process_key);

        match process {
            FlatProcess::Nil | FlatProcess::ActionPrefix { .. } => Vec::new(),
            FlatProcess::Named(name) => self.get_propositions(
                *self
                    .bindings
                    .get(name)
                    .expect("All named processes should have been bound"),
            ),
            FlatProcess::Restriction { process, .. }
            | FlatProcess::ActionRelabelling { process, .. } => self.get_propositions(process),
            FlatProcess::PropositionRelabelling { process, labels } => self
                .get_propositions(process)
                .into_iter()
                .map(|prop| dbg!(&labels).get(prop).copied().unwrap_or(prop))
                .collect(),
            FlatProcess::Sum(left, right) | FlatProcess::Compose(left, right) => self
                .get_propositions(left)
                .into_iter()
                .chain(self.get_propositions(right))
                .collect(),
            FlatProcess::AtomicProposition {
                propositions,
                process,
            } => propositions
                .into_iter()
                .chain(self.get_propositions(process))
                .collect(),
        }
    }

    pub fn get_transitions(&self, process_key: ProcKey) -> TransitionMap<'a, ProcKey> {
        if let Some(transitions) = self.transition_cache.borrow().get(process_key) {
            return transitions.clone();
        }

        let process = self.process_map.borrow().get_value(process_key).clone();
        let empty_set = HashSet::new();

        let transitions = match process {
            FlatProcess::Nil => HashMap::new(),
            FlatProcess::Named(name) => self.get_transitions(self.lookup_process_key(name)),
            FlatProcess::ActionPrefix { action, process } => {
                HashMap::from([(action, HashSet::from([process]))])
            }
            FlatProcess::Restriction {
                process,
                restrictions,
            } => self
                .get_transitions(process)
                .into_iter()
                .filter(|(WeightedAction { action, .. }, _)| match action {
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
            FlatProcess::ActionRelabelling { process, labels } => self
                .get_transitions(process)
                .into_iter()
                .map(
                    |(WeightedAction { action, weight }, targets)| match action {
                        Action::Label {
                            name,
                            is_complement,
                        } => (
                            WeightedAction {
                                weight,
                                action: Action::Label {
                                    name: labels.get(name).unwrap_or(&name),
                                    is_complement,
                                },
                            },
                            targets,
                        ),
                        Action::Tau => (WeightedAction { weight, action }, targets),
                    },
                )
                .map(|(action, targets)| {
                    (
                        action,
                        targets
                            .into_iter()
                            .map(|process| {
                                self.insert_process(FlatProcess::ActionRelabelling {
                                    process,
                                    labels: labels.clone(),
                                })
                            })
                            .collect(),
                    )
                })
                .collect(),
            FlatProcess::PropositionRelabelling { process, labels } => self
                .get_transitions(process)
                .into_iter()
                .map(|(action, sucessors)| {
                    (
                        action,
                        sucessors
                            .into_iter()
                            .map(|process| {
                                self.insert_process(FlatProcess::PropositionRelabelling {
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
                let keys: HashSet<WeightedAction> = left_transitions
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
            FlatProcess::Compose(left, right) => self.get_compose_transitions(left, right),
            FlatProcess::AtomicProposition { process, .. } => self.get_transitions(process),
        };

        self.transition_cache
            .borrow_mut()
            .insert(process_key, transitions.clone());

        transitions
    }

    fn insert_process(&self, process: FlatProcess<'a, ProcKey>) -> ProcKey {
        self.process_map.borrow_mut().get_or_insert_key(process)
    }

    fn insert_ast_bindings(&mut self, bindings: Vec<Binding<'a>>) {
        for binding in bindings {
            let process_key = self.insert_ast_process(&binding.process);
            self.bindings.insert(binding.name, process_key);
        }
    }

    pub fn get_process(&self, key: ProcKey) -> FlatProcess<'a, ProcKey> {
        self.process_map.borrow().get_value(key).clone()
    }

    pub fn insert_ast_process(&mut self, process: &Process<'a>) -> ProcKey {
        match process {
            Process::Nil => self.insert_process(FlatProcess::Nil),
            Process::Named(name) => self.insert_process(FlatProcess::Named(name)),
            Process::ActionPrefix { action, process } => {
                let flat_process_key = self.insert_ast_process(process);
                self.insert_process(FlatProcess::ActionPrefix {
                    action: *action,
                    process: flat_process_key,
                })
            }
            Process::Restriction {
                process,
                restriction,
            } => {
                let inner_process_key = self.insert_ast_process(process);
                self.insert_process(FlatProcess::Restriction {
                    process: inner_process_key,
                    restrictions: restriction.clone(),
                })
            }
            Process::ActionRelabelling { process, labels } => {
                let inner_process_key = self.insert_ast_process(process);
                self.insert_process(FlatProcess::ActionRelabelling {
                    process: inner_process_key,
                    labels: labels.clone(),
                })
            }
            Process::PropositionRelabelling { process, labels } => {
                let inner_process_key = self.insert_ast_process(process);
                self.insert_process(FlatProcess::PropositionRelabelling {
                    process: inner_process_key,
                    labels: labels.clone(),
                })
            }
            Process::Sum(left, right) => {
                let left_key = self.insert_ast_process(left);
                let right_key = self.insert_ast_process(right);
                self.insert_process(FlatProcess::Sum(left_key, right_key))
            }
            Process::Compose(left, right) => {
                let left_key = self.insert_ast_process(left);
                let right_key = self.insert_ast_process(right);
                self.insert_process(FlatProcess::Compose(left_key, right_key))
            }
            Process::AtomicPropositions {
                propositions,
                process,
            } => {
                let process = self.insert_ast_process(process);
                self.insert_process(FlatProcess::AtomicProposition {
                    propositions: propositions.clone(),
                    process,
                })
            }
        }
    }

    fn get_compose_transitions(&self, left: ProcKey, right: ProcKey) -> TransitionMap<'a, ProcKey> {
        let left_transitions = self.get_transitions(left);
        let right_tansitions = self.get_transitions(right);

        let mut successors = TransitionMap::new();

        for (left_action, left_sucessors) in left_transitions {
            let mut current_succesors_processes = HashSet::<ProcKey>::new();
            for left_successor in left_sucessors {
                let composed_process = FlatProcess::Compose(left_successor, right);
                let composed_process_key = self.insert_process(composed_process);
                current_succesors_processes.insert(composed_process_key);

                // find sync actions
                if let WeightedAction {
                    weight: left_weight,
                    action:
                        Action::Label {
                            name,
                            is_complement,
                        },
                } = left_action
                {
                    let co_action = Action::Label {
                        name,
                        is_complement: !is_complement,
                    };
                    let matching_right_transitions = right_tansitions
                        .iter()
                        .filter(|(WeightedAction { action, .. }, _)| *action == co_action)
                        .collect::<Vec<_>>();
                    if !matching_right_transitions.is_empty() {
                        for (
                            WeightedAction {
                                weight: right_weight,
                                ..
                            },
                            right_successors,
                        ) in matching_right_transitions
                        {
                            let current_sync_processes = right_successors
                                .iter()
                                .map(|right_successor| {
                                    self.insert_process(FlatProcess::Compose(
                                        left_successor,
                                        *right_successor,
                                    ))
                                })
                                .collect::<Vec<_>>();

                            if !current_sync_processes.is_empty() {
                                successors
                                    .entry(WeightedAction {
                                        action: Action::Tau,
                                        weight: max(left_weight, *right_weight),
                                    })
                                    .or_default()
                                    .extend(current_sync_processes);
                            }
                        }
                    }
                }
            }

            successors
                .entry(left_action)
                .or_default()
                .extend(current_succesors_processes);
        }

        for (right_action, right_processes) in right_tansitions {
            let current_succesors_processes = right_processes.iter().map(|right_successor| {
                let composed_process = FlatProcess::Compose(left, *right_successor);
                self.insert_process(composed_process)
            });

            successors
                .entry(right_action)
                .or_default()
                .extend(current_succesors_processes);
        }

        successors
    }

    fn lookup_process_key(&self, name: &str) -> ProcKey {
        *self
            .bindings
            .get(name)
            .expect("all bindings should have been mapped")
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::systems::wccs::grammar::ProgramParser;
    use slotmap::DefaultKey;

    macro_rules! transition_set {
        ($lts:expr;) => {HashMap::new()};
        ($lts:expr;$($action:expr => $target:expr),*) => {{
            let mut transitions = TransitionMap::new();
            $(
                let action = WeightedAction::parse($action);
                let target = Process::parse($target);
                let target = $lts.insert_ast_process(&target);
                transitions.entry(action).or_default().insert(target);
            )*
            transitions
        }};
    }

    macro_rules! proposition_set {
        ($lts:expr;) => {
            Vec::new()
        };
        ($lts:expr;$($prop:expr),*) => {{
            let mut propositions = Vec::new();
            $(
                propositions.push($prop);
            )*
            propositions
        }};
    }

    macro_rules! transition_tests {
        ($($name:ident: $proc:expr => [$($action:expr => $target:expr),*] $(in $ccs:expr)?;)*) => {
            $(
            #[test]
            #[allow(unused_variables)]
            fn $name() {
                #[allow(unused_mut)]
                let mut lts = WCCSSystem::<DefaultKey>::default();
                $(
                    let parser = ProgramParser::new();
                    let ast_bindings = parser
                        .parse(&$ccs)
                        .expect("Failed to parse CCS program content.");
                    lts.insert_ast_bindings(ast_bindings);
                )?
                let proc = Process::parse($proc);
                let key = lts.insert_ast_process(&proc);
                let transitions = lts.get_transitions(key);
                assert_eq!(transitions, transition_set![lts; $($action => $target),*])
            }
            )*
        };
    }

    macro_rules! proposition_tests {
        ($($name:ident: $proc:expr => [$($prop:expr),*] $(in $ccs:expr)?;)*) => {
            $(
            #[test]
            #[allow(unused_variables)]
            fn $name() {
                #[allow(unused_mut)]
                let mut lts = WCCSSystem::<DefaultKey>::default();
                $(
                    let parser = ProgramParser::new();
                    let ast_bindings = parser
                        .parse(&$ccs)
                        .expect("Failed to parse CCS program content.");
                    lts.insert_ast_bindings(ast_bindings);
                )?
                let proc = Process::parse($proc);
                let key = lts.insert_ast_process(&proc);
                let mut propositions = lts.get_propositions(key);
                let mut target_propositions = proposition_set![lts; $($prop),*];
                propositions.sort();
                target_propositions.sort();

                assert_eq!(propositions, target_propositions);
            }
            )*
        };
    }

    transition_tests! {
        nil: "0" => [];
        simple_sum: "<a>.<a>.0 + <b>.<b>.0" => ["<a>" => "<a>.0", "<b>" => "<b>.0"];
        simple_compose: "<a>.0 | <b>.0" => ["<a>" => "0 | <b>.0", "<b>" => "<a>.0 | 0"];
        simple_tau: "<a>.0 | <a!>.0" => ["<a>" => "0 | <a!>.0", "<a!>" => "<a>.0 | 0", "<tau>" => "0 | 0"];
        restrict_retained: "(<a>.<b>.0) \\ {b}" => ["<a>" => "(<b>.0) \\ {b}"];
        sum_restrict: "(<a>.<b>.0 + <b>.<b>.0) \\ {b}" => ["<a>" => "(<b>.0) \\ {b}"];
        compose_restrict: "(<a>.<b>.0 | <b>.<b>.0) \\ {b}" => ["<a>" => "(<b>.0 | <b>.<b>.0) \\ {b}"];
        restrict_to_nothing: "(<a>.<b>.0) \\ {a}" => [];
        tau_in_restrict: "(<a>.0 | <a!>.0) \\ {a}" => ["<tau>" => "(0 | 0) \\ {a}"];
        restrict_left_of_tau: "((<a>.0) \\ {a}) | <a!>.0" => ["<a!>" => "((<a>.0) \\ {a}) | 0"];
        restrict_right_of_tau: "<a>.0  | ((<a!>.0) \\ {a})" => ["<a>" => "0  | ((<a!>.0) \\ {a})"];
        relabel_retained: "(<a>.<b>.0)[c -> b]" => ["<a>" => "(<b>.0)[c -> b]"];
        simple_relabel: "(<a>.<b>.0)[a -> c]" => ["<c>" => "(<b>.0)[a -> c]"];
        tau_in_relabel: "(<a>.0 | <a!>.0)[a -> b]" => ["<b>" => "(0 | <a!>.0)[a -> b]", "<b!>" => "(<a>.0 | 0)[a -> b]", "<tau>" => "(0 | 0)[a -> b]"];
        relabel_to_left_of_tau: "((<b>.0)[b -> a]) | <a!>.0" => ["<a>" => "(0)[b -> a] | <a!>.0", "<a!>" => "((<b>.0)[b -> a]) | 0", "<tau>" => "(0)[b -> a] | 0"];
        relabel_from_left_of_tau: "((<a>.0)[a->b]) | <a!>.0" => ["<b>" => "(0)[a->b] | <a!>.0", "<a!>" => "((<a>.0)[a->b]) | 0"];
        restrict_then_relabel: "((<a>.0) \\ {a})[a->b]" => [];
        relabel_then_restrict: "((<a>.0)[a->b]) \\ {a}" => ["<b>" => "((0)[a->b]) \\ {a}"];
        simple_named: "A" => ["<a>" => "<b>.0"] in "A := <a>.<b>.0;";
        restrict_named: "A \\ {a}" => [] in "A := <a>.<b>.0;";
        restrict_named_retained: "A \\ {b}" => ["<a>" => "(<b>.0) \\ {b}"] in "A := <a>.<b>.0;";
        relabel_named: "A [a->b]" => ["<b>" => "(<b>.0)[a->b]"] in "A := <a>.<b>.0;";
        tau_through_named: "A | <a!>.0" => ["<a>" => "0 | <a!>.0", "<a!>" => "A | 0", "<tau>" => "0 | 0"] in "A := <a>.0;";
        atomic_propositions: "mow:dump:<a,1>.S" => ["<a,1>" => "S"];
        tau_weight: "(<a,1>.0 | <a!,2>.0) \\ {a}" => ["<tau,2>" => "(0 | 0) \\ {a}"];
        co_action: "<a!, 3>.0" => ["<a!, 3>" => "0"];
        co_action_weight: "<a,2>.0 | <a!,1>.0" => ["<tau,2>" => "0 | 0", "<a,2>" => "0 | <a!,1>.0", "<a!,1>" => "<a,2>.0 | 0"];
        nested_propositions: "mow:<a>.dump:0" => ["<a>" => "dump:0"];
        multiple_propositions: "mow:dump:<a>.0" => ["<a>" => "0"];
    }

    proposition_tests! {
        basic: "mow:dump:0" => ["mow", "dump"];
        sum: "mow:0 + dump:0" => ["mow", "dump"];
        composition: "mow:0 | dump:0" => ["mow", "dump"];
        named: "mow:A" => ["mow", "dump"] in "A := dump:0;";
        prop_relabeling: "(mow:0) [mow => dump]" => ["dump"];
        action_relabeling: "(mow:0) [mow -> dump]" => ["mow"];
        multi_prop: "mow:mow:0" => ["mow", "mow"];
    }
}
