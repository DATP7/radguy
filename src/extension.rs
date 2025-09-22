use std::{collections::HashSet, hash::Hash};

use crate::{Assignment, System, oracle::LocalOracle};

pub trait TermSystem<VarKey: Copy, VarValue: PartialOrd, TermKey: Copy>:
    System<VarKey, VarValue>
{
    fn definition(&self, variable: VarKey) -> TermKey;
}

pub trait LocalExtension<K: Hash + Eq + Copy, V: PartialOrd>:
    LocalOracle<K, V, Self::System>
{
    type TermKey: Copy;
    type System: TermSystem<K, V, Self::TermKey>;

    fn depends(
        &self,
        visited: &HashSet<K>,
        assignment: &dyn Assignment<K, V>,
        possible: &HashSet<(K, K)>,
        system: &Self::System,
    ) -> HashSet<(K, Self::TermKey)>;

    fn flow(
        &self,
        visited: &HashSet<K>,
        assignment: &dyn Assignment<K, V>,
        possible: &HashSet<(K, K)>,
        system: &Self::System,
    ) -> HashSet<(K, K)>
    where
        <Self as LocalExtension<K, V>>::TermKey: std::cmp::PartialEq,
    {
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
