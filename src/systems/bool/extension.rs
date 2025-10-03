use itertools::iproduct;
use radguy::{
    Assignment, System,
    extension::{LocalExtension, TermSystem},
};
use slotmap::Key;
use std::{collections::HashSet, hash::Hash, marker::PhantomData};

use crate::systems::bool::{BoolSystem, BoolTerm};

#[derive(Default)]
pub struct BoolExtension<TermKey: Key + Hash>(PhantomData<TermKey>);

impl<VarKey: Key + Hash, TermKey: Key + Hash>
    LocalExtension<
        VarKey,
        bool,
        TermKey,
        HashSet<(VarKey, VarKey)>,
        HashSet<VarKey>,
        HashSet<(VarKey, TermKey)>,
    > for BoolExtension<TermKey>
{
    type System = BoolSystem<VarKey, TermKey>;

    fn depends(
        &self,
        _visited: &HashSet<VarKey>,
        assignment: &dyn Assignment<VarKey, bool>,
        possible: &HashSet<(VarKey, VarKey)>,
        system: &Self::System,
    ) -> HashSet<(VarKey, TermKey)> {
        let mut deps = HashSet::new();
        for (x, y) in iproduct!(
            system.variables().iter().copied(),
            system.variables().iter().copied()
        ) {
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

fn collect_terms<VarKey: Key + Hash, TermKey: Key + Hash>(
    x: VarKey,
    term_key: TermKey,
    assignment: &dyn Assignment<VarKey, bool>,
    possible: &HashSet<(VarKey, VarKey)>,
    system: &BoolSystem<VarKey, TermKey>,
    current: &mut HashSet<(VarKey, TermKey)>,
) {
    // TODO: This caching could probably be a bit smarter by also keeping track of what we know to
    // exclude
    if current.contains(&(x, term_key)) {
        return;
    }
    let term = system
        .terms
        .get_value(term_key)
        .expect("term should be defined");
    match *term {
        BoolTerm::True | BoolTerm::False => (),
        BoolTerm::Variable(y) => {
            if possible.contains(&(x, y)) && !assignment.get(&y) {
                current.insert((x, term_key));
            }
        }
        BoolTerm::Or(lhs, rhs) => {
            collect_terms(x, lhs, assignment, possible, system, current);
            collect_terms(x, rhs, assignment, possible, system, current);
            if (current.contains(&(x, lhs)) || current.contains(&(x, rhs)))
                && !system.evaluate_term(lhs, assignment)
                && !system.evaluate_term(rhs, assignment)
            {
                current.insert((x, term_key));
            }
        }
        BoolTerm::And(lhs, rhs) => {
            collect_terms(x, lhs, assignment, possible, system, current);
            collect_terms(x, rhs, assignment, possible, system, current);

            // Case 1
            if [(lhs, rhs), (rhs, lhs)].into_iter().any(|(i, j)| {
                current.contains(&(x, i))
                    && !system.evaluate_term(i, assignment)
                    && system.evaluate_term(j, assignment)
            }) {
                current.insert((x, term_key));
                return;
            }

            // Case 2
            if system.evaluate_term(lhs, assignment) || system.evaluate_term(rhs, assignment) {
                return;
            }
            for (i, j) in [(lhs, rhs), (rhs, lhs)] {
                if !current.contains(&(x, i)) {
                    continue;
                }
                for z in system.variables() {
                    collect_terms(z, j, assignment, possible, system, current);
                    if current.contains(&(z, j)) {
                        current.insert((x, term_key));
                        return;
                    }
                }
            }
        }
    }
}
