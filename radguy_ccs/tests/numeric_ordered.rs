use radguy::{
    oracle::{IdentityOracle, SMax, TrivialOracle},
    ordered::{
        oracle::{
            DependencyCountOracle, DependentCountOracle, InverseDependencyCountOracle,
            InverseDependentCountOracle, StrategicArgumentsOracle, StrategicHeightOracle,
            StrategicLocalOracle, ToConstant, ToOrdered,
        },
        strategy::StrategyWeight,
    },
};

pub mod systems;
macro_rules! test_oracle_system_strategy_numerical {
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
macro_rules! test_oracle_system_ordered_numerical {
    (test $oracle:expr, on: $($spec:ident),* $(,)?) => {
        $(
        mod $spec {
            use super::*;

            use radguy::ordered::strategy::{BinaryHeapStrategy, HashMapStrategy, OrxStrategy, LazyHeap};
            use orx_priority_queue::DaryHeapWithMap;

            test_oracle_system_strategy_numerical! {
                std_binary: test $oracle, with BinaryHeapStrategy<_>, on: $spec
            }
            test_oracle_system_strategy_numerical! {
                std_hashmap: test $oracle, with HashMapStrategy<_>, on: $spec
            }
            test_oracle_system_strategy_numerical! {
                orx_quad: test $oracle, with OrxStrategy<_, DaryHeapWithMap<_, StrategyWeight, 4>>, on: $spec
            }
            test_oracle_system_strategy_numerical! {
                std_binary_lazy: test $oracle, with LazyHeap<_, BinaryHeapStrategy<_>>, on: $spec
            }
            test_oracle_system_strategy_numerical! {
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
    SMax.ordered().then(DependencyCountOracle::default()), smax_ord_then_dependency_count;
    SMax.ordered().and_by(DependencyCountOracle::default(), std::cmp::min), smax_ord_and_min_dependency_count;
    DependencyCountOracle::default(), dependency_count;
    InverseDependencyCountOracle::default(), dependency_count_inverse;
    DependentCountOracle::default(), dependent_count;
    InverseDependentCountOracle::default(), dependent_count_inverse;
    StrategicArgumentsOracle::successors(), arguments_s;
    StrategicArgumentsOracle::successors().and_by(DependencyCountOracle::default(), std::cmp::min), args_s_and_min_dependency_count;
    StrategicArgumentsOracle::successors().and_by(InverseDependencyCountOracle::default(), std::cmp::min), args_s_and_min_dependency_count_inverse;
    StrategicArgumentsOracle::successors().and_by(DependentCountOracle::default(), std::cmp::min), args_s_and_min_dependent_count;
    StrategicArgumentsOracle::successors().and_by(InverseDependentCountOracle::default(), std::cmp::min), args_s_and_min_dependent_count_inverse;
    StrategicArgumentsOracle::successors().then(StrategicHeightOracle::transitive()), args_s_then_height_transitive;
    StrategicArgumentsOracle::successors().and_by(StrategicHeightOracle::transitive(), std::cmp::min), args_s_and_height_transitive;
    StrategicHeightOracle::simple(), height_simple;
    StrategicHeightOracle::simple().and_by(DependencyCountOracle::default(), std::cmp::min), height_simple_and_min_dependency_count;
    StrategicHeightOracle::simple().then(DependencyCountOracle::default()), height_simple_then_dependency_count;
    StrategicHeightOracle::transitive(), height_transitive;
    StrategicHeightOracle::transitive().and_by(InverseDependencyCountOracle::default(), std::cmp::min), height_transitive_and_min_dependency_count_inverse;
}
