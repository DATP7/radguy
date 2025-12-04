use radguy::{
    oracle::{IdentityOracle, SMax, TrivialOracle},
    ordered::{
        oracle::{
            ArgumentsStrategy, DependencyCountOracle, DependentCountOracle,
            InverseDependencyCountOracle, InverseDependentCountOracle, StrategicArgumentsOracle,
            StrategicHeightOracle, StrategicLocalOracle, StrategicNonStuckOracle, ToConstant,
            ToInverse, ToOrdered,
        },
        strategy::StrategyWeight,
    },
};
use radguy_ccs::systems::bool::extension::BoolExtension;

pub mod systems;

macro_rules! test_oracle_system_strategy_fast {
    ($name:ident: test $oracle:expr, with $strategy:ty, on: $spec:ident) => {
        mod $name {
            use super::*;

            #[test]
            fn eager() {
                let $crate::systems::bool::SystemSpec {
                    mut system,
                    variables,
                    goal,
                } = $crate::systems::bool::$spec();
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
                let $crate::systems::bool::SystemSpec {
                    system,
                    variables,
                    goal,
                } = $crate::systems::bool::$spec();
                let mut system: radguy_ccs::systems::bool::LazyBoolSystem<_, _, _> = system.into();
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

macro_rules! test_oracle_system_strategy_slow {
    ($name:ident: test $oracle:expr, with $strategy:ty, on: $spec:ident) => {
        mod $name {
            use super::*;

            #[test]
            #[cfg_attr(not(feature = "slow"), ignore = "Not running slow tests")]
            fn eager() {
                let $crate::systems::bool::SystemSpec {
                    mut system,
                    variables,
                    goal,
                } = $crate::systems::bool::$spec();
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
                let $crate::systems::bool::SystemSpec {
                    system,
                    variables,
                    goal,
                } = $crate::systems::bool::$spec();
                let mut system: radguy_ccs::systems::bool::LazyBoolSystem<_, _, _> = system.into();
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

macro_rules! test_oracle_system_ordered {
    (test $oracle:expr, on: $($spec:ident),* $(,)?) => {
        $(
        mod $spec {
            use super::*;

            use radguy::ordered::strategy::{BinaryHeapStrategy, HashMapStrategy, OrxStrategy, LazyHeap};
            use orx_priority_queue::DaryHeapWithMap;

            test_oracle_system_strategy_fast! {
                std_binary: test $oracle, with BinaryHeapStrategy<_>, on: $spec
            }
            test_oracle_system_strategy_slow! {
                std_hashmap: test $oracle, with HashMapStrategy<_>, on: $spec
            }
            test_oracle_system_strategy_slow! {
                orx_quad: test $oracle, with OrxStrategy<_, DaryHeapWithMap<_, StrategyWeight, 4>>, on: $spec
            }
            test_oracle_system_strategy_slow! {
                std_binary_lazy: test $oracle, with LazyHeap<_, BinaryHeapStrategy<_>>, on: $spec
            }
            test_oracle_system_strategy_slow! {
                orx_quad_lazy: test $oracle, with LazyHeap<_, OrxStrategy<_, DaryHeapWithMap<_, StrategyWeight, 4>>>, on: $spec
            }
        }
        )*
    };
}

macro_rules! test_oracle_ordered {
    ($oracle:expr, $name:ident) => {
        mod $name {
            use super::*;
            test_oracle_system_ordered! {
                test $oracle, on:
                large,
                self_reference_true,
                self_reference_false,
                true_single,
                false_single,
                and_00,
                and_01,
                and_10,
                and_11,
                or_00,
                or_01,
                or_10,
                or_11,
                parens_true,
                parens_false,
                chain,
            }
        }
    };
}
macro_rules! test_oracles_ordered {
    ( $( $oracle:expr, $name:ident; )*) => {
            $(
                test_oracle_ordered!($oracle, $name);
            )*
    };
}

test_oracles_ordered! {
    IdentityOracle::bitset().constant(StrategyWeight::Infinity), identity_oracle_inf_bitset;
    IdentityOracle::bitset().ordered(), identity_oracle_ord_bitset;
    TrivialOracle::bitset().constant(StrategyWeight::Infinity), trivial_oracle_inf_bitset;
    TrivialOracle::bitset().ordered(), trivial_oracle_ord_bitset;
    SMax::bitset().constant(StrategyWeight::Num(0)), smax_const_0_bitset;
    SMax::bitset().constant(StrategyWeight::Infinity), smax_const_infinity_bitset;
    SMax::bitset().constant(StrategyWeight::Num(0)).then(DependencyCountOracle::default()), smax_then_count_bitset;
    SMax::bitset().constant(StrategyWeight::Num(10)).and_by(DependencyCountOracle::default(), std::cmp::min), smax_10_and_min_count_bitset;
    SMax::bitset().ordered(), smax_ord_bitset;
    SMax::bitset().ordered().then(DependencyCountOracle::default()), smax_ord_then_count_bitset;
    SMax::bitset().ordered().then(DependencyCountOracle::default()).inverse(), smax_ord_then_count_bitset_inversed;
    BoolExtension::bitset().as_oracle().constant(StrategyWeight::Num(0)), bool_extension_0_bitset;
    BoolExtension::bitset().as_oracle().constant(StrategyWeight::Num(0)).and_by(DependencyCountOracle::default(), std::cmp::min), bool_extension_0_and_min_count_bitset;
    BoolExtension::bitset().as_oracle().constant(StrategyWeight::Infinity).and_by(DependencyCountOracle::default(), std::cmp::min), bool_extension_inf_and_min_count_bitset;
    BoolExtension::bitset().as_oracle().constant(StrategyWeight::Infinity).and_by(InverseDependencyCountOracle::default(), std::cmp::min), bool_extension_inf_and_min_count_inverse_bitset;
    BoolExtension::bitset().as_oracle().ordered(), bool_extension_ord_bitset;
    BoolExtension::bitset().as_oracle().ordered().and_by(DependencyCountOracle::default(), std::cmp::min), bool_extension_ord_and_min_count_bitset;
    BoolExtension::bitset().as_oracle().ordered().and_by(InverseDependencyCountOracle::default(), std::cmp::min), bool_extension_ord_and_min_count_inverse_bitset;
    IdentityOracle::hashset().constant(StrategyWeight::Infinity), identity_oracle_inf_hashset;
    IdentityOracle::hashset().ordered(), identity_oracle_ord_hashset;
    IdentityOracle::hashset().constant(StrategyWeight::Infinity).inverse(), identity_oracle_inf_hashset_inverse;
    IdentityOracle::hashset().ordered().inverse(), identity_oracle_ord_hashset_inverse;
    TrivialOracle::hashset().constant(StrategyWeight::Infinity), trivial_oracle_inf_hashset;
    TrivialOracle::hashset().ordered(), trivial_oracle_ord_hashset;
    SMax::hashset().constant(StrategyWeight::Num(0)), smax_const_0_hashset;
    SMax::hashset().constant(StrategyWeight::Infinity), smax_const_infinity_hashset;
    SMax::hashset().constant(StrategyWeight::Num(0)).then(DependencyCountOracle::default()), smax_then_count_hashset;
    SMax::hashset().constant(StrategyWeight::Num(10)).and_by(DependencyCountOracle::default(), std::cmp::min), smax_10_and_min_count_hashset;
    SMax::hashset().ordered(), smax_ord_hashset;
    SMax::hashset().ordered().then(DependencyCountOracle::default()), smax_ord_then_count_hashset;
    BoolExtension::hashset().as_oracle().constant(StrategyWeight::Num(0)), bool_extension_0_hashset;
    BoolExtension::hashset().as_oracle().constant(StrategyWeight::Num(0)).and_by(DependencyCountOracle::default(), std::cmp::min), bool_extension_0_and_min_count_hashset;
    BoolExtension::hashset().as_oracle().constant(StrategyWeight::Infinity).and_by(DependencyCountOracle::default(), std::cmp::min), bool_extension_inf_and_min_count_hashset;
    BoolExtension::hashset().as_oracle().constant(StrategyWeight::Infinity).and_by(InverseDependencyCountOracle::default(), std::cmp::min), bool_extension_inf_and_min_count_inverse_hashset;
    BoolExtension::hashset().as_oracle().ordered(), bool_extension_ord_hashset;
    BoolExtension::hashset().as_oracle().ordered().and_by(DependencyCountOracle::default(), std::cmp::min), bool_extension_ord_and_min_count_hashset;
    BoolExtension::hashset().as_oracle().ordered().and_by(InverseDependencyCountOracle::default(), std::cmp::min), bool_extension_ord_and_min_count_inverse_hashset;
    BoolExtension::hashset().as_oracle().ordered().and_by(DependencyCountOracle::default(), std::cmp::min).inverse(), bool_extension_ord_and_min_count_hashset_inversed;
    BoolExtension::hashset().as_oracle().ordered().and_by(InverseDependencyCountOracle::default(), std::cmp::min).inverse(), bool_extension_ord_and_min_count_inverse_hashset_inversed;
    DependencyCountOracle::default(), dependency_count;
    InverseDependencyCountOracle::default(), dependency_count_inverse;
    DependentCountOracle::default(), dependent_count;
    InverseDependentCountOracle::default(), dependent_count_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors), arguments_s_s;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).inverse(), arguments_s_s_inversed;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).and_by(DependencyCountOracle::default(), std::cmp::min), args_s_s_and_min_dependency;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).and_by(InverseDependencyCountOracle::default(), std::cmp::min), args_s_s_and_min_dependency_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).then(StrategicHeightOracle::transitive()), args_s_s_then_height_transitive;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Successors).and_by(StrategicHeightOracle::transitive(), std::cmp::min), args_s_s_and_height_transitive;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors), arguments_s_a;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(DependencyCountOracle::default(), std::cmp::min), args_s_a_and_min_dependency;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(InverseDependencyCountOracle::default(), std::cmp::min), args_s_a_and_min_dependency_inverse;
    StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(InverseDependencyCountOracle::default(), std::cmp::min).inverse(), args_s_a_and_min_dependency_inverse_inversed;
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
    StrategicHeightOracle::simple().and_by(DependencyCountOracle::default(), std::cmp::min).inverse(), height_simple_and_min_dependency_count_inverse;
    StrategicHeightOracle::simple().then(DependencyCountOracle::default()), height_simple_then_dependency_count;
    StrategicHeightOracle::transitive(), height_transitive;
    StrategicHeightOracle::transitive().and_by(InverseDependencyCountOracle::default(), std::cmp::min), height_transitive_and_min_dependency_count_inverse;
    StrategicNonStuckOracle::bitset(), nonstuck_bitset;
    StrategicNonStuckOracle::hashset(), nonstuck_hashset;
    StrategicNonStuckOracle::bitset().then(SMax::bitset().ordered()), nonstuck_bitset_then_smax;
    StrategicNonStuckOracle::hashset().then(SMax::hashset().ordered()), nonstuck_hashset_then_smax;
}
