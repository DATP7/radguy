use crate::{
    Assignment, Cartesian, IterSet, System,
    ordered::{
        oracle::StrategicLocalOracle,
        strategy::{InitialStrategy, Intersect, SliceRight, Strategy},
    },
};
use std::fmt::Debug;

pub mod oracle;
pub mod strategy;
pub fn kleene_local<
    VarKey: Copy + Eq + Debug,
    VarValue: PartialOrd,
    VarStrategy: Strategy<VarKey> + Intersect<VarKey, VarSet> + Debug,
    PairStrat: Strategy<(VarKey, VarKey)> + SliceRight<VarKey, VarKey, VarStrategy>,
    VarSet: IterSet<Item = VarKey> + FromIterator<VarKey> + Cartesian<Output = PairSet> + Debug,
    PairSet: IterSet<Item = (VarKey, VarKey)>,
    S: System<VarKey, VarValue, PairSet, VarSet>
        + InitialStrategy<VarKey, VarValue, PairSet, VarSet, PairStrat>,
>(
    system: &S,
    target: VarKey,
    oracle: &impl StrategicLocalOracle<VarKey, VarValue, PairSet, VarSet, PairStrat, S>,
) -> VarValue {
    let initial_strategy = system.get_initial_strategy();
    let mut assignment = system.bottom_assignment();
    let mut discovered: VarSet = std::iter::once(target).collect();
    let mut visited = std::iter::empty().collect();
    let mut todo = oracle
        .get_strategy(&visited, &assignment, &initial_strategy, system)
        .slice_right(target)
        .intersect(&discovered);

    while let Some(x) = todo.extract_min() {
        let evaluated = system.evaluate(x, &assignment);
        // TODO: i think this is a lot of allocation
        visited = visited.union(std::iter::once(x).collect());
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
