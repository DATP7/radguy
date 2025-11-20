use radguy::{
    extension::LocalExtension,
    oracle::{IdentityOracle, SMax, TrivialOracle},
    ordered::{
        oracle::{
            CountOracle, InverseCountOracle, StrategicArgumentsOracle, StrategicHeightOracle,
            StrategicLocalOracle, ToConstant,
        },
        strategy::StrategyWeight,
    },
};
use radguy_ccs::systems::bool::extension::BoolExtension;

mod systems;

macro_rules! test_oracle_system_strategy {
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
                    assert_eq!(
                        ::radguy::ordered::kleene_local::<_, _, $strategy, $strategy, _>(
                            &mut system,
                            start,
                            &$oracle
                        ),
                        goal,
                        "{var} did not have the expected value"
                    );
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
                    assert_eq!(
                        ::radguy::ordered::kleene_local::<_, _, $strategy, $strategy, _>(
                            &mut system,
                            start,
                            &$oracle
                        ),
                        goal,
                        "{var} did not have the expected value"
                    );
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

            use radguy::ordered::strategy::{BinaryHeapStrategy, HashMapStrategy, OrxStrategy};
            use orx_priority_queue::DaryHeapWithMap;

            test_oracle_system_strategy! {
                std_binary: test $oracle, with BinaryHeapStrategy<_>, on: $spec
            }
            test_oracle_system_strategy! {
                std_hashmap: test $oracle, with HashMapStrategy<_>, on: $spec
            }
            test_oracle_system_strategy! {
                orx_quad: test $oracle, with OrxStrategy<_, DaryHeapWithMap<_, StrategyWeight, 4>>, on: $spec
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
    IdentityOracle.constant(StrategyWeight::Infinity), identity_oracle_inf;
    TrivialOracle.constant(StrategyWeight::Infinity), trivial_oracle_inf;
    SMax.constant(StrategyWeight::Num(0)), smax_const_0;
    SMax.constant(StrategyWeight::Infinity), smax_const_infinity;
    SMax.constant(StrategyWeight::Num(0)).then(CountOracle::default()), smax_then_count;
    SMax.constant(StrategyWeight::Num(10)).and_by(CountOracle::default(), std::cmp::min), smax_10_and_min_count;
    BoolExtension::oracle().constant(StrategyWeight::Num(0)), bool_extension_0;
    BoolExtension::oracle().constant(StrategyWeight::Num(0)).and_by(CountOracle::default(), std::cmp::min), bool_extension_0_and_min_count;
    BoolExtension::oracle().constant(StrategyWeight::Infinity).and_by(CountOracle::default(), std::cmp::min), bool_extension_inf_and_min_count;
    BoolExtension::oracle().constant(StrategyWeight::Infinity).and_by(InverseCountOracle::default(), std::cmp::min), bool_extension_inf_and_min_count_inverse;
    CountOracle::default(), count;
    InverseCountOracle::default(), count_inverse;
    StrategicArgumentsOracle::default(), arguments_s;
    StrategicArgumentsOracle::default().and_by(CountOracle::default(), std::cmp::min), args_s_and_min_count;
    StrategicArgumentsOracle::default().and_by(InverseCountOracle::default(), std::cmp::min), args_s_and_min_count_inverse;
    StrategicArgumentsOracle::default().then(StrategicHeightOracle::transitive()), args_s_then_height_transitive;
    StrategicArgumentsOracle::default().and_by(StrategicHeightOracle::transitive(), std::cmp::min), args_s_and_height_transitive;
    StrategicHeightOracle::simple(), height_simple;
    StrategicHeightOracle::simple().and_by(CountOracle::default(), std::cmp::min), height_simple_and_min_count;
    StrategicHeightOracle::simple().then(CountOracle::default()), height_simple_then_count;
    StrategicHeightOracle::transitive(), height_transitive;
    StrategicHeightOracle::transitive().and_by(InverseCountOracle::default(), std::cmp::min), height_transitive_and_min_count_inverse;
}
