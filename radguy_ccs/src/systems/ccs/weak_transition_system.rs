use std::{cell::RefCell, collections::HashSet};

use radguy::arena::{Key, SecondaryArena};

use crate::systems::ccs::{
    ast::{Action, Binding},
    strong_transition_system::StrongTransitionSystem,
    transition_system::{TransitionMap, TransitionSystem},
};

#[derive(Default, Debug, Clone)]
pub struct WeakTransitionSystem<'a, ProcKey: Key> {
    pub(crate) strong_transition_system: StrongTransitionSystem<'a, ProcKey>,
    transition_cache: RefCell<SecondaryArena<ProcKey, TransitionMap<'a, ProcKey>>>, // Benchmark if this increases performance or if strong LTS cache is enough
    tau_cache: RefCell<SecondaryArena<ProcKey, HashSet<ProcKey>>>,
}

impl<ProcKey: Key> WeakTransitionSystem<'_, ProcKey> {
    fn tau_closure(&self, process_key: ProcKey) -> HashSet<ProcKey> {
        // PERF: Bench if this makes a difference when other optimisations are present
        if let Some(cached) = self.tau_cache.borrow().get(process_key) {
            // PERF: Rc
            return cached.clone();
        }

        let mut visited = HashSet::new();
        let mut frontier = vec![process_key];

        while let Some(proc) = frontier.pop() {
            visited.insert(proc);
            for (action, successors) in self.strong_transition_system.get_transitions(proc) {
                if action != Action::Tau {
                    continue;
                }
                for succ in successors {
                    if visited.insert(succ) {
                        frontier.push(succ);
                    }
                }
            }
        }

        self.tau_cache
            .borrow_mut()
            .insert(process_key, visited.clone());
        visited
    }
}

impl<'a, ProcKey: Key + Copy> TransitionSystem<'a, ProcKey> for WeakTransitionSystem<'a, ProcKey> {
    fn lookup_process_key(&self, name: &str) -> Option<&ProcKey> {
        self.strong_transition_system.lookup_process_key(name)
    }

    fn load_ast(&mut self, ast: Vec<Binding<'a>>) {
        self.strong_transition_system.load_ast(ast);
    }

    fn get_transitions(&self, process_key: ProcKey) -> TransitionMap<'a, ProcKey> {
        if let Some(transitions) = self.transition_cache.borrow().get(process_key) {
            // PERF: Rc
            return transitions.clone();
        }

        let mut transitions = TransitionMap::new();
        let tau_targets = self.tau_closure(process_key);

        for tau_target in tau_targets.iter().copied() {
            for (action, transitive_targets) in
                self.strong_transition_system.get_transitions(tau_target)
            {
                if action != Action::Tau {
                    let new_successors = transitive_targets
                        .iter()
                        .flat_map(|t| self.tau_closure(*t))
                        .collect();
                    transitions
                        .entry(action)
                        .and_modify(|existing_successors| {
                            *existing_successors = existing_successors
                                .union(&new_successors)
                                .copied()
                                .collect();
                        })
                        .or_insert(new_successors);
                }
            }
        }
        transitions.insert(Action::Tau, tau_targets);

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

    macro_rules! transition_set {
        ($lts:expr;) => {HashMap::new()};
        ($lts:expr;$($action:expr => $target:expr),* $(,)?) => {{
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
            fn $name() {
                #[allow(unused_mut)]
                let mut lts = WeakTransitionSystem::<usize>::default();
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
                assert_eq!(transitions, transition_set![lts; "tau" => $proc, $($action => $target),*])
            }
            )*
        };
    }

    // TODO: should tau actions still be in transition set?
    transition_tests! {
        nil: "0" => [];
        simple_sum: "a.a.0 + b.b.0" => ["a" => "a.0", "b" => "b.0"];
        simple_compose: "a.0 | b.0" => ["a" => "0 | b.0", "b" => "a.0 | 0"];
        simple_tau: "a.b.0 | 'a.0" => ["a" => "b.0 | 'a.0", "'a" => "a.b.0 | 0", "b" => "0 | 0", "tau" => "b.0 | 0"];
        restrict_retained: "(a.b.0) \\ {b}" => ["a" => "(b.0) \\ {b}"];
        sum_restrict: "(a.b.0 + b.b.0) \\ {b}" => ["a" => "(b.0) \\ {b}"];
        compose_restrict: "(a.b.0 | b.b.0) \\ {b}" => ["a" => "(b.0 | b.b.0) \\ {b}"];
        restrict_to_nothing: "(a.b.0) \\ {a}" => [];
        tau_in_restrict: "(a.b.0 | 'a.0) \\ {a}" => ["b" => "(0 | 0) \\ {a}", "tau" => "(b.0 | 0) \\ {a}"];
        restrict_left_of_tau: "((a.0) \\ {a}) | 'a.0" => ["'a" => "((a.0) \\ {a}) | 0"];
        restrict_right_of_tau: "a.0  | (('a.0) \\ {a})" => ["a" => "0  | (('a.0) \\ {a})"];
        relabel_retained: "(a.b.0)[b/c]" => ["a" => "(b.0)[b/c]"];
        simple_relabel: "(a.b.0)[c/a]" => ["c" => "(b.0)[c/a]"];
        tau_in_relabel: "(a.c.0 | 'a.0)[b/a]" => ["tau" => "(c.0 | 0)[b/a]", "b" => "(c.0 | 'a.0)[b/a]", "'b" => "(a.c.0 | 0)[b/a]", "c" => "(0 | 0)[b/a]"];
        relabel_to_left_of_tau: "((b.0)[a/b]) | 'a.c.0" => ["tau" => "0[a/b] | c.0", "a" => "(0)[a/b] | 'a.c.0", "'a" => "((b.0)[a/b]) | c.0", "c" => "(0)[a/b] | 0"];
        relabel_from_left_of_tau: "((a.0)[b/a]) | 'a.0" => ["b" => "(0)[b/a] | 'a.0", "'a" => "((a.0)[b/a]) | 0"];
        restrict_then_relabel: "((a.0) \\ {a})[b/a]" => [];
        relabel_then_restrict: "((a.0)[b/a]) \\ {a}" => ["b" => "((0)[b/a]) \\ {a}"];
        simple_named: "A" => ["a" => "b.0"] in "A = a.b.0;";
        restrict_named: "A \\ {a}" => [] in "A = a.b.0;";
        restrict_named_retained: "A \\ {b}" => ["a" => "(b.0) \\ {b}"] in "A = a.b.0;";
        relabel_named: "A[b/a]" => ["b" => "(b.0)[b/a]"] in "A = a.b.0;";
        tau_through_named: "A | 'a.c.0" => ["a" => "0 | 'a.c.0", "'a" => "A | c.0", "c" => "0 | 0", "tau" => "0 | c.0"] in "A = a.0;";
        action_in_middle_of_taus: "tau.tau.a.tau.tau.0" => ["tau" =>"tau.a.tau.tau.0","tau" => "a.tau.tau.0", "a" => "tau.tau.0", "a" => "tau.0", "a" => "0"];
    }
}
