use radguy::{
    oracle::{IdentityOracle, SMax, TrivialOracle},
    ordered::{
        oracle::{
            ArgumentsStrategy, DependencyCountOracle, DependentCountOracle,
            InverseDependencyCountOracle, InverseDependentCountOracle, StrategicArgumentsOracle,
            StrategicHeightOracle, StrategicLocalOracle, ToConstant, ToOrdered,
        },
        strategy::StrategyWeight,
    },
};

pub mod systems;
macro_rules! test_oracle_system_strategy_numerical_fast {
    ($name:ident: test $oracle:expr, with $strategy:ty, on: $spec:ident) => {
        mod $name {
            use super::*;

            #[test]
            fn eager() {
                let $crate::systems::numeric::NumericSystemSpec {
                    mut system,
                    variables,
                    goal,
                } = $crate::systems::numeric::$spec();
                for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                    let start = system.names.get_or_insert_key(var);
                    let (result, _) =
                        ::radguy::ordered::kleene_local::<_, _, $strategy, $strategy, _>(
                            &mut system,
                            start,
                            &$oracle,
                        );
                    assert_eq!(result, goal, "{var} did not have the expected value");
                }
            }
            #[test]
            fn lazy() {
                let $crate::systems::numeric::NumericSystemSpec {
                    system,
                    variables,
                    goal,
                } = $crate::systems::numeric::$spec();
                let mut system: radguy_ccs::systems::numeric::numeric_system::LazyNumericSystem<
                    _,
                    _,
                    _,
                > = system.into();
                for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                    let start = system.init_target(var);
                    let (result, _) =
                        ::radguy::ordered::kleene_local::<_, _, $strategy, $strategy, _>(
                            &mut system,
                            start,
                            &$oracle,
                        );
                    assert_eq!(result, goal, "{var} did not have the expected value");
                }
            }
        }
    };
}

macro_rules! test_oracle_system_strategy_numerical_slow {
    ($name:ident: test $oracle:expr, with $strategy:ty, on: $spec:ident) => {
        mod $name {
            use super::*;

            #[test]
            #[cfg_attr(not(feature = "slow"), ignore = "Not running slow tests")]
            fn eager() {
                let $crate::systems::numeric::NumericSystemSpec {
                    mut system,
                    variables,
                    goal,
                } = $crate::systems::numeric::$spec();
                for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                    let start = system.names.get_or_insert_key(var);
                    let (result, _) =
                        ::radguy::ordered::kleene_local::<_, _, $strategy, $strategy, _>(
                            &mut system,
                            start,
                            &$oracle,
                        );
                    assert_eq!(result, goal, "{var} did not have the expected value");
                }
            }
            #[test]
            #[cfg_attr(not(feature = "slow"), ignore = "Not running slow tests")]
            fn lazy() {
                let $crate::systems::numeric::NumericSystemSpec {
                    system,
                    variables,
                    goal,
                } = $crate::systems::numeric::$spec();
                let mut system: radguy_ccs::systems::numeric::numeric_system::LazyNumericSystem<
                    _,
                    _,
                    _,
                > = system.into();
                for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                    let start = system.init_target(var);
                    let (result, _) =
                        ::radguy::ordered::kleene_local::<_, _, $strategy, $strategy, _>(
                            &mut system,
                            start,
                            &$oracle,
                        );
                    assert_eq!(result, goal, "{var} did not have the expected value");
                }
            }
        }
    };
}

macro_rules! test_oracle_system_ordered_numerical {
    (test $oracle:expr, on: $($spec:ident),* $(,)?) => {
        $(
        mod $spec {
            use super::*;

            use radguy::ordered::strategy::{BinaryHeapStrategy, HashMapStrategy, OrxStrategy, LazyHeap};
            use orx_priority_queue::DaryHeapWithMap;

            test_oracle_system_strategy_numerical_fast! {
                std_binary: test $oracle, with BinaryHeapStrategy<_>, on: $spec
            }
            test_oracle_system_strategy_numerical_slow! {
                std_hashmap: test $oracle, with HashMapStrategy<_>, on: $spec
            }
            test_oracle_system_strategy_numerical_slow! {
                orx_quad: test $oracle, with OrxStrategy<_, DaryHeapWithMap<_, StrategyWeight, 4>>, on: $spec
            }
            test_oracle_system_strategy_numerical_slow! {
                std_binary_lazy: test $oracle, with LazyHeap<_, BinaryHeapStrategy<_>>, on: $spec
            }
            test_oracle_system_strategy_numerical_slow! {
                orx_quad_lazy: test $oracle, with LazyHeap<_, OrxStrategy<_, DaryHeapWithMap<_, StrategyWeight, 4>>>, on: $spec
            }
        }
        )*
    };
}

macro_rules! test_oracle_ordered_numerical {
    ($oracle:expr, $name:ident) => {
        mod $name {
            use super::*;
            test_oracle_system_ordered_numerical! {
                test $oracle, on:
                large,
                inf,
                literal,
                reference,
                add_literal_literal,
                add_inf_literal,
                add_literal_inf,
                add_inf_inf,
                mult_literal_literal,
                mult_inf_literal,
                mult_literal_inf,
                mult_inf_inf,
                max_literal_literal,
                max_inf_literal,
                max_literal_inf,
                max_inf_inf,
                min_literal_literal,
                min_inf_literal,
                min_literal_inf,
                min_inf_inf,
                chain_literal,
                chain_infinity,
                recursive,
                mutual_recursion,
            }
        }
    };
}

macro_rules! test_oracles_ordered_numerical {
    ( $( $oracle:expr, $name:ident; )*) => {
            $(
                test_oracle_ordered_numerical!($oracle, $name);
            )*
    };
}
test_oracles_ordered_numerical! {
    IdentityOracle.constant(StrategyWeight::Infinity), identity_oracle_inf;
    IdentityOracle.ordered(), identity_oracle_ord;
    TrivialOracle.constant(StrategyWeight::Infinity), trivial_oracle_inf;
    TrivialOracle.ordered(), trivial_oracle_ord;
    SMax.constant(StrategyWeight::Num(0)), smax_const_0;
    SMax.constant(StrategyWeight::Infinity), smax_const_infinity;
    SMax.constant(StrategyWeight::Num(0)).then(DependencyCountOracle::default()), smax_then_dependency_count;
    SMax.constant(StrategyWeight::Num(10)).and_by(DependencyCountOracle::default(), std::cmp::min), smax_10_and_min_dependency_count;
    SMax.ordered(), smax_ord;
    SMax.ordered().then(DependencyCountOracle::default()), smax_ord_then_count;
    SMax.ordered().and_by(DependencyCountOracle::default(), std::cmp::min), smax_ord_and_min_dependency;
    DependencyCountOracle::default(), count;
    InverseDependencyCountOracle::default(), count_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors), arguments_s_s;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).and_by(DependencyCountOracle::default(), std::cmp::min), args_s_s_and_min_dependency;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).and_by(InverseDependencyCountOracle::default(), std::cmp::min), args_s_s_and_min_dependency_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).then(StrategicHeightOracle::transitive()), args_s_s_then_height_transitive;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).and_by(StrategicHeightOracle::transitive(), std::cmp::min), args_s_s_and_height_transitive;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors), arguments_s_a;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(DependencyCountOracle::default(), std::cmp::min), args_s_a_and_min_dependency;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(InverseDependencyCountOracle::default(), std::cmp::min), args_s_a_and_min_dependency_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).then(StrategicHeightOracle::transitive()), args_s_a_then_height_transitive;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(StrategicHeightOracle::transitive(), std::cmp::min), args_s_a_and_height_transitive;
    StrategicArgumentsOracle::with(ArgumentsStrategy::SuccessorsInverted), arguments_s_si;
    StrategicArgumentsOracle::with(ArgumentsStrategy::SuccessorsInverted).and_by(DependencyCountOracle::default(), std::cmp::min), args_s_si_and_min_dependency;
    StrategicArgumentsOracle::with(ArgumentsStrategy::SuccessorsInverted).and_by(InverseDependencyCountOracle::default(), std::cmp::min), args_s_si_and_min_dependency_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::SuccessorsInverted).then(StrategicHeightOracle::transitive()), args_s_si_then_height_transitive;
    StrategicArgumentsOracle::with(ArgumentsStrategy::SuccessorsInverted).and_by(StrategicHeightOracle::transitive(), std::cmp::min), args_s_si_and_height_transitive;
    StrategicArgumentsOracle::with(ArgumentsStrategy::AncestorsInverted), arguments_s_ai;
    StrategicArgumentsOracle::with(ArgumentsStrategy::AncestorsInverted).and_by(DependencyCountOracle::default(), std::cmp::min), args_s_ai_and_min_dependency;
    StrategicArgumentsOracle::with(ArgumentsStrategy::AncestorsInverted).and_by(InverseDependencyCountOracle::default(), std::cmp::min), args_s_ai_and_min_dependency_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::AncestorsInverted).then(StrategicHeightOracle::transitive()), args_s_ai_then_height_transitive;
    StrategicArgumentsOracle::with(ArgumentsStrategy::AncestorsInverted).and_by(StrategicHeightOracle::transitive(), std::cmp::min), args_s_ai_and_height_transitive;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).and_by(DependentCountOracle::default(), std::cmp::min), args_s_s_and_min_dependent;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).and_by(InverseDependentCountOracle::default(), std::cmp::min), args_s_s_and_min_dependent_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(DependentCountOracle::default(), std::cmp::min), args_s_a_and_min_dependent;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(InverseDependentCountOracle::default(), std::cmp::min), args_s_a_and_min_dependent_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::SuccessorsInverted).and_by(DependentCountOracle::default(), std::cmp::min), args_s_si_and_min_dependent;
    StrategicArgumentsOracle::with(ArgumentsStrategy::SuccessorsInverted).and_by(InverseDependentCountOracle::default(), std::cmp::min), args_s_si_and_min_dependent_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::AncestorsInverted).and_by(DependentCountOracle::default(), std::cmp::min), args_s_ai_and_min_dependent;
    StrategicArgumentsOracle::with(ArgumentsStrategy::AncestorsInverted).and_by(InverseDependentCountOracle::default(), std::cmp::min), args_s_ai_and_min_dependent_inverse;
    StrategicHeightOracle::simple(), height_simple;
    StrategicHeightOracle::simple().and_by(DependencyCountOracle::default(), std::cmp::min), height_simple_and_min_dependency_count;
    StrategicHeightOracle::simple().then(DependencyCountOracle::default()), height_simple_then_dependency_count;
    StrategicHeightOracle::transitive(), height_transitive;
    StrategicHeightOracle::transitive().and_by(InverseDependencyCountOracle::default(), std::cmp::min), height_transitive_and_min_dependency_count_inverse;
}
