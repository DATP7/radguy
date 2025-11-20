use radguy::{Assignment, Universe, extension::LocalExtension};
use slotmap::Key;
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    hash::Hash,
    marker::PhantomData,
};

use crate::systems::bool::{BoolSystem, BoolTerm};

#[derive(Default, Clone)]
pub struct BoolExtension<TermKey: Key + Hash, VarName: Hash + Eq + Clone>(
    PhantomData<(TermKey, VarName)>,
);

impl<
    VarKey: Key + Hash,
    TermKey: Key + Hash,
    VarName: Hash + Eq + Clone,
    System: BoolSystem<VarKey, TermKey, VarName> + Universe<HashSet<VarKey>>,
> LocalExtension<VarKey, bool, TermKey, HashSet<(VarKey, VarKey)>, System>
    for BoolExtension<TermKey, VarName>
{
    #[expect(clippy::used_underscore_binding)]
    fn depends(
        &self,
        term_key: TermKey,
        _visited: &HashSet<VarKey>,
        assignment: &HashMap<VarKey, bool>,
        possible: &HashSet<(VarKey, VarKey)>,
        system: &System,
    ) -> HashSet<VarKey> {
        let term = system.get_term(term_key);
        match term {
            BoolTerm::Variable(y) if !assignment.get_assignment(&y) => possible
                .iter()
                .filter_map(|(l, r)| if *r == y { Some(l) } else { None })
                .copied()
                .collect(),
            BoolTerm::Variable(_) | BoolTerm::True | BoolTerm::False => HashSet::new(),
            BoolTerm::Or(term_keys) => {
                // All terms are false and there exist a false term that x can influence
                if term_keys
                    .iter()
                    .all(|&term_key| !system.evaluate_term(term_key, assignment))
                {
                    term_keys
                        .into_iter()
                        .flat_map(|t| self.depends(t, _visited, assignment, possible, system))
                        .collect()
                } else {
                    HashSet::new()
                }
            }
            BoolTerm::And(term_keys) => {
                // Filter out true terms
                let term_keys = term_keys
                    .iter()
                    .copied()
                    .filter(|&term_key| !system.evaluate_term(term_key, assignment));

                let mut ret = HashSet::new();

                // x can influence at least one false term and all false terms are dependent on some var (can change)
                for term in term_keys {
                    let term_deps = self.depends(term, _visited, assignment, possible, system);
                    if term_deps.is_empty() && !system.evaluate_term(term_key, assignment) {
                        return HashSet::new();
                    }
                    ret.extend(term_deps);
                }
                ret
            }
        }
    }
}

impl<TermKey: Key + Hash, VarName: Hash + Eq + Clone> Display for BoolExtension<TermKey, VarName> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bool")
    }
}
