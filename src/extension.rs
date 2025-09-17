use std::{collections::HashSet, hash::Hash};

use crate::{Assignment, LocalOracle, System};

pub trait TermSystem<VarKey: Copy, VarValue, TermKey>: System<VarKey, VarValue> {
    fn definition(&self, variable: VarKey) -> TermKey;
}

pub trait LocalExtension<K: Hash + Eq + Copy, V> {
    type TermKey;
    type System: TermSystem<K, V, Self::TermKey>;

    fn depends(
        &self,
        visited: &HashSet<K>,
        assignment: &dyn Assignment<K, V>,
        possible: &HashSet<(K, K)>,
        system: &Self::System,
    ) -> HashSet<(K, Self::TermKey)>;
}

impl<K: Hash + Eq + Copy, V, T: Hash + Eq + Copy, E: LocalExtension<K, V, TermKey = T>>
    LocalOracle<K, V, E::System> for E
{
    fn flow(
        &self,
        visited: &HashSet<K>,
        assignment: &dyn Assignment<K, V>,
        possible: &HashSet<(K, K)>,
        system: &E::System,
    ) -> HashSet<(K, K)> {
        let unvisited = system
            .variables()
            .into_iter()
            .filter(|v| !visited.contains(v))
            .collect::<HashSet<_>>();
        let unvisited_dep = crate::cartesian(&system.variables(), &unvisited);
        let self_dep = visited.iter().map(|&x| (x, x)).collect();
        let terms = self.depends(visited, assignment, possible, system);
        let term_dep = visited.iter().flat_map(|&y| {
            let ty = system.definition(y);
            terms
                .iter()
                .filter_map(|&(x, t)| if ty == t { Some((x, y)) } else { None })
                .collect::<HashSet<_>>()
        });

        unvisited_dep
            .union(&self_dep)
            .copied()
            .chain(term_dep)
            .collect()
    }
}
