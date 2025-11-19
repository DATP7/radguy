use radguy::{Assignment, Universe, extension::LocalExtension};
use slotmap::Key;
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
    marker::PhantomData,
};

use crate::systems::bool::{BoolSystem, BoolTerm};

#[derive(Default)]
pub struct BoolExtension<TermKey: Key + Hash, VarName: Hash + Eq + Clone>(
    PhantomData<(TermKey, VarName)>,
);

impl<
    VarKey: Key + Hash,
    TermKey: Key + Hash,
    VarName: Hash + Eq + Clone,
    System: BoolSystem<VarKey, TermKey, VarName> + Universe<HashSet<VarKey>>,
>
    LocalExtension<
        VarKey,
        bool,
        TermKey,
        HashSet<(VarKey, VarKey)>,
        HashSet<(VarKey, TermKey)>,
        System,
    > for BoolExtension<TermKey, VarName>
{
    fn depends(
        &self,
        visited: &HashSet<VarKey>,
        assignment: &HashMap<VarKey, bool>,
        possible: &HashSet<(VarKey, VarKey)>,
        system: &System,
    ) -> HashSet<(VarKey, TermKey)> {
        let mut deps = HashSet::new();
        for (x, y) in possible
            .iter()
            .filter(|(_, y)| visited.contains(y))
            .copied()
        {
            collect_terms(
                x,
                system.definition(y),
                assignment,
                possible,
                system,
                &mut deps,
            );
        }
        deps
    }
}

fn collect_terms<
    VarKey: Key,
    TermKey: Key,
    VarName: Hash + Eq + Clone,
    S: BoolSystem<VarKey, TermKey, VarName> + Universe<HashSet<VarKey>>,
>(
    x: VarKey,
    term_key: TermKey,
    assignment: &HashMap<VarKey, bool>,
    possible: &HashSet<(VarKey, VarKey)>,
    system: &S,
    current: &mut HashSet<(VarKey, TermKey)>,
) {
    // TODO: This caching could probably be a bit smarter by also keeping track of what we know to
    // exclude
    if current.contains(&(x, term_key)) {
        return;
    }
    let term = system.get_term(term_key);
    match term {
        BoolTerm::True | BoolTerm::False => (),
        BoolTerm::Variable(y) => {
            if possible.contains(&(x, y)) && !assignment.get_assignment(&y) {
                current.insert((x, term_key));
            }
        }
        BoolTerm::Or(term_keys) => {
            // All terms are false and there exist a false term that x can influence
            if term_keys
                .iter()
                .all(|&term_key| !system.evaluate_term(term_key, assignment))
                && term_keys.iter().any(|&term_key| {
                    collect_terms(x, term_key, assignment, possible, system, current);
                    current.contains(&(x, term_key))
                })
            {
                current.insert((x, term_key));
            }
        }
        BoolTerm::And(term_keys) => {
            // Filter out true terms
            let term_keys = term_keys
                .iter()
                .copied()
                .filter(|&term_key| !system.evaluate_term(term_key, assignment))
                .collect::<Vec<_>>();

            // x can influence at least one false term and all false terms are dependent on some var (can change)
            if term_keys.iter().any(|&term_key| {
                collect_terms(x, term_key, assignment, possible, system, current);
                current.contains(&(x, term_key))
            }) && term_keys.iter().all(|&term_key| {
                system.universe().iter().any(|&z| {
                    collect_terms(z, term_key, assignment, possible, system, current);
                    current.contains(&(z, term_key))
                })
            }) {
                current.insert((x, term_key));
            }
        }
    }
}

impl<TermKey: Key + Hash, VarName: Hash + Eq + Clone> Display for BoolExtension<TermKey, VarName> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bool")
    }
}
