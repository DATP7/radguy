use crate::{
    Arguments, Assignment, Bottom, Cartesian, Intersect, PairUniverse, System, Union,
    ordered::{
        oracle::StrategicLocalOracle,
        strategy::{ResetWeights, Singleton, SliceRight, Strategy, StrategyItem, StrategyWeight},
    },
};
use crate::{Universe, Without};
use std::{collections::HashSet, fmt::Debug, hash::Hash};

pub mod extension;
pub mod oracle;
pub mod strategy;

#[expect(clippy::similar_names)]
pub fn kleene_local<
    VarKey: Copy + Eq + Debug + Hash,
    VarValue: PartialOrd + Bottom + Copy,
    VarStrategy: Strategy<VarKey> + Intersect<HashSet<VarKey>> + Singleton<VarKey> + Debug,
    PairStrat: Strategy<(VarKey, VarKey)>
        + Clone
        + SliceRight<VarKey, VarKey, VarStrategy>
        + Singleton<(VarKey, VarKey)>
        + Extend<StrategyItem<(VarKey, VarKey)>>
        + ResetWeights
        + Debug
        + Default,
    S: System<VarKey, VarValue>
        + Arguments<VarKey, HashSet<VarKey>>
        + Universe<HashSet<VarKey>>
        + PairUniverse<HashSet<(VarKey, VarKey)>>,
>(
    system: &mut S,
    target: VarKey,
    oracle: &impl StrategicLocalOracle<VarKey, VarValue, PairStrat, S>,
) -> Option<(VarValue, (u32, u32, usize))>
where
    for<'a> &'a PairStrat: IntoIterator<Item = StrategyItem<(VarKey, VarKey)>>,
{
    let mut assignment = system.bottom_assignment();
    let mut discovered = system.universe();
    let mut strategy = PairStrat::default();
    let initial_pairs = system
        .pair_universe()
        .into_iter()
        .map(|(x, y)| StrategyItem::infinite((x, y)));
    strategy.extend(initial_pairs);
    strategy = oracle.get_strategy(&assignment, &strategy, system);
    let mut todo = strategy.slice_right(target).intersect(&discovered);

    let mut variable_iterations = 0;
    let mut oracle_iterations = 0;

    #[cfg(feature = "timeout")]
    let start_time = chrono::Utc::now();

    while let Some(xs) = todo.extract_mins() {
        let mut updated = false;
        for x in xs {
            debug_assert!(discovered.contains(&x), "discovered should contain {x:?}");
            variable_iterations += 1;

            let evaluated = system.evaluate(x, &assignment);
            let args = system.arguments(x);
            if assignment.get_assignment(&x) != evaluated || !args.is_subset(&discovered) {
                #[cfg(feature = "timeout")]
                if (chrono::Utc::now() - start_time) >= crate::KLEENE_TIMEOUT {
                    return None;
                }
                updated = true;
                assignment.update_assignment(x, evaluated);
                // At this point `rel` is D x D with some elements pruned by oracles
                // We expand it with args to create (D u A) x (D u A), still with those elements
                // pruned, by unioning with the elements of the square below.
                // +-------------+-------+
                // | A x D       | A x A |
                // +-------------+-------+
                // | D x D (rel) | D x A |
                // +-------------+-------+
                let new_args = args.without(&discovered);
                let axa = new_args.cartesian(&new_args);
                let axd = new_args.cartesian(&discovered);
                let dxa = discovered.cartesian(&new_args);
                let new_pairs = axa
                    .union(axd)
                    .union(dxa)
                    .into_iter()
                    .map(|p| StrategyItem(StrategyWeight::Infinity, p));
                strategy.extend(new_pairs);
                strategy.reset_weights();
                discovered = system.universe();
            }
        }
        if updated {
            oracle_iterations += 1;
            system.lock();
            strategy = oracle.get_strategy(&assignment, &strategy, system);
            todo = strategy.slice_right(target);
            system.unlock();
        }
    }

    Some((
        assignment.get_assignment(&target),
        (
            variable_iterations,
            oracle_iterations,
            system.universe().len(),
        ),
    ))
}
