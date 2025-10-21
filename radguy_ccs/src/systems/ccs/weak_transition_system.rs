use std::collections::{HashMap, HashSet};

use slotmap::Key;

use crate::systems::ccs::{
    ast::{Action, Binding},
    strong_transition_system::StrongTransitionSystem,
    transition_system::TransitionSystem,
};

#[derive(Default, Debug)]
pub struct WeakTransitionSystem<'a, ProcKey: Key> {
    strong_transition_system: StrongTransitionSystem<'a, ProcKey>,
}

impl<'a, ProcKey: Key> TransitionSystem<'a, ProcKey> for WeakTransitionSystem<'a, ProcKey> {
    fn lookup_process_key(&self, name: &str) -> Option<&ProcKey> {
        self.strong_transition_system.lookup_process_key(name)
    }

    fn load_ast(&mut self, ast: Vec<Binding<'a>>) {
        self.strong_transition_system.load_ast(ast);
    }

    fn get_transitions(&self, process_key: ProcKey) -> HashMap<Action<'a>, HashSet<ProcKey>> {
        let mut transitions = self.strong_transition_system.get_transitions(process_key);

        let tau_processes = match transitions.remove(&Action::Tau) {
            Some(set) => set.clone(),
            None => return transitions,
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

        transitions
    }
}
