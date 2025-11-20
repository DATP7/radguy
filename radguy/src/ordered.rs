use crate::{
    Arguments, Assignment, Bottom, System, Union,
    ordered::{
        oracle::StrategicLocalOracle,
        strategy::{InitialStrategy, Intersect, Singleton, SliceRight, Strategy},
    },
};
use std::{collections::HashSet, fmt::Debug, hash::Hash};

pub mod oracle;
pub mod strategy;

pub fn kleene_local<
    VarKey: Copy + Eq + Debug + Hash,
    VarValue: PartialOrd + Bottom + Copy,
    VarStrategy: Strategy<VarKey> + Intersect<VarKey, HashSet<VarKey>> + Singleton<VarKey> + Debug,
    PairStrat: Strategy<(VarKey, VarKey)> + SliceRight<VarKey, VarKey, VarStrategy>,
    S: System<VarKey, VarValue>
        + InitialStrategy<VarKey, VarValue, PairStrat>
        + Arguments<VarKey, HashSet<VarKey>>,
>(
    system: &mut S,
    target: VarKey,
    oracle: &impl StrategicLocalOracle<VarKey, VarValue, PairStrat, S>,
) -> VarValue {
    let mut assignment = system.bottom_assignment();
    let mut discovered = HashSet::from([target]);
    let mut visited = HashSet::default();
    let mut todo = VarStrategy::singleton(target);

    while let Some(x) = todo.extract_min() {
        let evaluated = system.evaluate(x, &assignment);
        visited.insert(x);
        if assignment.get_assignment(&x) != evaluated || !system.arguments(x).is_subset(&discovered)
        {
            assignment.update_assignment(x, evaluated);
            discovered = discovered.union(system.arguments(x));
            system.lock();
            todo = oracle
                .get_strategy(
                    &visited,
                    &assignment,
                    &system.get_initial_strategy(),
                    system,
                )
                .slice_right(target)
                .intersect(&discovered);
            system.unlock();
        }
    }

    assignment.get_assignment(&target)
}
