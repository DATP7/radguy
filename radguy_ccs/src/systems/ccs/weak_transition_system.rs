use std::{cell::RefCell, collections::HashSet};

use slotmap::{Key, SecondaryMap};

use crate::systems::ccs::{
    ast::{Action, Binding},
    strong_transition_system::StrongTransitionSystem,
    transition_system::{TransitionMap, TransitionSystem},
};

#[derive(Default, Debug)]
pub struct WeakTransitionSystem<'a, ProcKey: Key> {
    strong_transition_system: StrongTransitionSystem<'a, ProcKey>,
    transition_cache: RefCell<SecondaryMap<ProcKey, TransitionMap<'a, ProcKey>>>, // Benchmark if this increases performance or if strong LTS cache is enough
    process_cache: RefCell<HashSet<ProcKey>>,
}

impl<'a, ProcKey: Key> TransitionSystem<'a, ProcKey> for WeakTransitionSystem<'a, ProcKey> {
    fn lookup_process_key(&self, name: &str) -> Option<&ProcKey> {
        self.strong_transition_system.lookup_process_key(name)
    }

    fn load_ast(&mut self, ast: Vec<Binding<'a>>) {
        self.strong_transition_system.load_ast(ast);
    }

    fn get_transitions(&self, process_key: ProcKey) -> TransitionMap<'a, ProcKey> {
        if let Some(transitions) = self.transition_cache.borrow().get(process_key) {
            return transitions.clone(); // PERF: Remove this damn clone
        }

        // Check how CAAL handles infinete loops
        if self.process_cache.borrow().contains(&process_key) {
            return TransitionMap::new();
        }
        self.process_cache.borrow_mut().insert(process_key);

        let mut transitions = self.strong_transition_system.get_transitions(process_key);

        let Some(tau_processes) = transitions.remove(&Action::Tau) else {
            self.transition_cache
                .borrow_mut()
                .insert(process_key, transitions.clone());

            return transitions;
        };

        for tau_process in tau_processes {
            let expanded_transitions = self.get_transitions(tau_process);
            for (action, successors) in expanded_transitions {
                transitions
                    .entry(action)
                    .and_modify(|existing_successors| {
                        *existing_successors =
                            existing_successors.union(&successors).copied().collect();
                    })
                    .or_insert(successors);
            }
        }

        self.transition_cache
            .borrow_mut()
            .insert(process_key, transitions.clone());

        transitions
    }
}
