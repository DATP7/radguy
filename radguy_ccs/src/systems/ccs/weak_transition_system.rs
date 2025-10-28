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

#[cfg(test)]
mod tests {
    use crate::systems::ccs::weak_transition_system::TransitionMap;
    use crate::systems::ccs::{
        ast::{Action, Process},
        grammar::ProgramParser,
        transition_system::TransitionSystem,
        weak_transition_system::WeakTransitionSystem,
    };
    use slotmap::DefaultKey;
    use std::collections::HashMap;

    macro_rules! transition_set {
        ($lts:expr;) => {HashMap::new()};
        ($lts:expr;$($action:expr => $target:expr),*) => {{
            let mut transitions = TransitionMap::new();
            $(
                let action = Action::parse($action);
                let target = Process::parse($target);
                let target = $lts.strong_transition_system.insert_ast_process(&target);
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
                let mut lts = WeakTransitionSystem::<DefaultKey>::default();
                $(
                    let parser = ProgramParser::new();
                    let ast = parser
                        .parse(&$ccs)
                        .expect("Failed to parse CCS program content.");
                    lts.load_ast(ast);
                )?
                let proc = Process::parse($proc);
                let key = lts.strong_transition_system.insert_ast_process(&proc);
                let transitions = lts.get_transitions(key);
                assert_eq!(transitions, transition_set![lts; $($action => $target),*])
            }
            )*
        };
    }

    // TODO: should tau actions still be in transition set?
    transition_tests! {
        nil: "0" => [];
        simple_sum: "a.a.0 + b.b.0" => ["a" => "a.0", "b" => "b.0"];
        simple_compose: "a.0 | b.0" => ["a" => "0 | b.0", "b" => "a.0 | 0"];
        simple_tau: "a.b.0 | 'a.0" => ["a" => "b.0 | 'a.0", "'a" => "a.b.0 | 0", "b" => "0 | 0"];
        restrict_retained: "(a.b.0) \\ {b}" => ["a" => "(b.0) \\ {b}"];
        sum_restrict: "(a.b.0 + b.b.0) \\ {b}" => ["a" => "(b.0) \\ {b}"];
        compose_restrict: "(a.b.0 | b.b.0) \\ {b}" => ["a" => "(b.0 | b.b.0) \\ {b}"];
        restrict_to_nothing: "(a.b.0) \\ {a}" => [];
        tau_in_restrict: "(a.b.0 | 'a.0) \\ {a}" => ["b" => "(0 | 0) \\ {a}"];
        restrict_left_of_tau: "((a.0) \\ {a}) | 'a.0" => ["'a" => "((a.0) \\ {a}) | 0"];
        restrict_right_of_tau: "a.0  | (('a.0) \\ {a})" => ["a" => "0  | (('a.0) \\ {a})"];
        relabel_retained: "(a.b.0)[b/c]" => ["a" => "(b.0)[b/c]"];
        simple_relabel: "(a.b.0)[c/a]" => ["c" => "(b.0)[c/a]"];
        tau_in_relabel: "(a.c.0 | 'a.0)[b/a]" => ["b" => "(c.0 | 'a.0)[b/a]", "'b" => "(a.c.0 | 0)[b/a]", "c" => "(0 | 0)[b/a]"];
        relabel_to_left_of_tau: "((b.0)[a/b]) | 'a.c.0" => ["a" => "(0)[a/b] | 'a.c.0", "'a" => "((b.0)[a/b]) | c.0", "c" => "(0)[a/b] | 0"];
        relabel_from_left_of_tau: "((a.0)[b/a]) | 'a.0" => ["b" => "(0)[b/a] | 'a.0", "'a" => "((a.0)[b/a]) | 0"];
        restrict_then_relabel: "((a.0) \\ {a})[b/a]" => [];
        relabel_then_restrict: "((a.0)[b/a]) \\ {a}" => ["b" => "((0)[b/a]) \\ {a}"];
        simple_named: "A" => ["a" => "b.0"] in "A = a.b.0;";
        restrict_named: "A \\ {a}" => [] in "A = a.b.0;";
        restrict_named_retained: "A \\ {b}" => ["a" => "(b.0) \\ {b}"] in "A = a.b.0;";
        relabel_named: "A[b/a]" => ["b" => "(b.0)[b/a]"] in "A = a.b.0;";
        tau_through_named: "A | 'a.c.0" => ["a" => "0 | 'a.c.0", "'a" => "A | c.0", "c" => "0 | 0"] in "A = a.0;";
        action_in_middle_of_taus: "tau.tau.a.tau.tau.0" => ["a" => "tau.tau.0"];
    }
}
