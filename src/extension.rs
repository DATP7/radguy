use std::{collections::HashSet, hash::Hash, marker::PhantomData};

use itertools::iproduct;

use crate::{Assignment, System, oracle::LocalOracle};

pub trait TermSystem<VarKey: Copy, VarValue: PartialOrd, TermKey: Copy>:
    System<VarKey, VarValue>
{
    fn definition(&self, variable: VarKey) -> TermKey;
}

pub trait LocalExtension<VarKey: Hash + Eq + Copy, VarValue: PartialOrd, TermKey: Copy> {
    type System: TermSystem<VarKey, VarValue, TermKey>;

    fn depends(
        &self,
        visited: &HashSet<VarKey>,
        assignment: &dyn Assignment<VarKey, VarValue>,
        possible: &HashSet<(VarKey, VarKey)>,
        system: &Self::System,
    ) -> HashSet<(VarKey, TermKey)>;
}

pub struct ExtensionOracle<
    VarKey: Hash + Eq + Copy,
    VarValue: PartialOrd,
    TermKey: Copy,
    S: TermSystem<VarKey, VarValue, TermKey>,
    E: LocalExtension<VarKey, VarValue, TermKey, System = S>,
> {
    extension: E,
    _phantom_data: PhantomData<(VarKey, VarValue, TermKey)>,
}

impl<
    VarKey: Hash + Eq + Copy,
    VarValue: PartialOrd,
    TermKey: Copy + Eq,
    S: TermSystem<VarKey, VarValue, TermKey>,
    E: LocalExtension<VarKey, VarValue, TermKey, System = S>,
> LocalOracle<VarKey, VarValue, S> for ExtensionOracle<VarKey, VarValue, TermKey, S, E>
{
    fn approximate_flow(
        &self,
        visited: &HashSet<VarKey>,
        assignment: &dyn Assignment<VarKey, VarValue>,
        possible: &HashSet<(VarKey, VarKey)>,
        system: &E::System,
    ) -> HashSet<(VarKey, VarKey)> {
        let unvisited = system
            .variables()
            .into_iter()
            .filter(|v| !visited.contains(v))
            .collect::<HashSet<_>>();
        let unvisited_dep = iproduct!(
            system.variables().iter().copied(),
            unvisited.iter().copied()
        )
        .collect();
        let self_dep: HashSet<(_, _)> = visited.iter().map(|&x| (x, x)).collect();
        let terms = self
            .extension
            .depends(visited, assignment, possible, system);
        let term_dep = visited.iter().flat_map(|&y| {
            let ty = system.definition(y);
            terms
                .iter()
                .filter_map(|&(x, t)| if ty == t { Some((x, y)) } else { None })
                .collect::<HashSet<_>>()
        });

        self_dep
            .union(&unvisited_dep)
            .copied()
            .chain(term_dep)
            .collect()
    }
}

impl<
    VarKey: Hash + Eq + Copy,
    VarValue: PartialOrd,
    TermKey: Copy + Eq,
    S: TermSystem<VarKey, VarValue, TermKey>,
    E: LocalExtension<VarKey, VarValue, TermKey, System = S>,
> From<E> for ExtensionOracle<VarKey, VarValue, TermKey, S, E>
{
    fn from(extension: E) -> Self {
        Self {
            extension,
            _phantom_data: PhantomData,
        }
    }
}
