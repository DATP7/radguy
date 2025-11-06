use crate::{
    Arguments, Assignment, Cartesian, IsSubset, Set, System, Union,
    ordered::{
        oracle::StrategicLocalOracle,
        strategy::{InitialStrategy, Intersect, Singleton, SliceRight, Strategy},
    },
};
use std::fmt::Debug;

pub mod oracle;
pub mod strategy;
pub fn kleene_local<
    VarKey: Copy + Eq + Debug,
    VarValue: PartialOrd,
    VarStrategy: Strategy<VarKey> + Intersect<VarKey, VarSet> + Singleton<VarKey> + Debug,
    PairStrat: Strategy<(VarKey, VarKey)> + SliceRight<VarKey, VarKey, VarStrategy>,
    VarSet: Set<VarKey> + Union + IsSubset + Cartesian<Output = PairSet> + FromIterator<VarKey> + Debug,
    PairSet,
    S: System<VarKey, VarValue>
        + InitialStrategy<VarKey, VarValue, PairStrat>
        + Arguments<VarKey, VarSet>,
>(
    system: &S,
    target: VarKey,
    oracle: &impl StrategicLocalOracle<VarKey, VarValue, VarSet, PairStrat, S>,
) -> VarValue {
    let initial_strategy = system.get_initial_strategy();
    let mut assignment = system.bottom_assignment();
    let mut discovered: VarSet = std::iter::once(target).collect();
    let mut visited: VarSet = std::iter::empty().collect();
    let mut todo = VarStrategy::singleton(target);

    while let Some(x) = todo.extract_min() {
        let evaluated = system.evaluate(x, &assignment);
        visited.insert(x);
        if assignment.get(&x) != evaluated || !system.arguments(x).is_subset(&discovered) {
            assignment.update(x, evaluated);
            discovered = discovered.union(system.arguments(x));
            todo = oracle
                .get_strategy(&visited, &assignment, &initial_strategy, system)
                .slice_right(target)
                .intersect(&discovered);
        }
    }

    assignment.get(&target)
}
