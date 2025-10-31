mod systems;

macro_rules! test_oracle_system_unordered {
    (test $oracle:expr, on: $($spec:ident),* $(,)?) => {
        $(
        #[test]
        fn $spec() {
            let $crate::systems::bool::SystemSpec {
                mut system,
                variables,
                goal,
            } = $crate::systems::bool::$spec();
            for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                let start = system.names.get_or_insert_key(var);
                assert_eq!(::radguy::kleene_local(&system, start, &$oracle), goal, "{var} did not have the expected value");
            }
        }
        )*
    };
}

macro_rules! test_oracle_unordered {
    ($oracle:expr, $name:ident) => {
        mod $name {
            use super::*;
            test_oracle_system_unordered! {
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
            }
        }
    };
}
macro_rules! test_oracles_unordered {
    ( $( $oracle:expr, $name:ident; )*) => {
            $(
                test_oracle_unordered!($oracle, $name);
            )*
    };
}

macro_rules! test_oracle_system_ordered {
    (test $oracle:expr, on: $($spec:ident),* $(,)?) => {
        $(
        #[test]
        fn $spec() {
            let $crate::systems::bool::SystemSpec {
                mut system,
                variables,
                goal,
            } = $crate::systems::bool::$spec();
            for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                let start = system.names.get_or_insert_key(var);
                assert_eq!(::radguy::ordered::kleene_local(&system, start, &$oracle), goal, "{var} did not have the expected value");
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

mod unordered {
    use radguy::{
        extension::ExtensionOracle,
        oracle::{LocalMaxR, LocalOracle, SMax, TrivialOracle},
    };
    use radguy_ccs::systems::bool::extension::BoolExtension;

    test_oracles_unordered! {
        SMax, smax;
        TrivialOracle, trivialoracle;
        LocalMaxR, localmaxr;
        TrivialOracle.and(SMax), trivialoracle_and_smax;
        LocalMaxR.and(SMax), localmaxr_and_smax;
        LocalMaxR.and(TrivialOracle), localmaxr_and_trivialoracle;
        TrivialOracle.then(SMax), trivialoracle_then_smax;
        TrivialOracle.then(LocalMaxR), trivialoracle_then_localmaxr;
        SMax.then(TrivialOracle), smax_then_trivialoracle;
        SMax.then(LocalMaxR), smax_then_localmaxr;
        LocalMaxR.then(SMax), localmaxr_then_smax;
        LocalMaxR.then(TrivialOracle), localmaxr_then_trivialoracle;
        ExtensionOracle::from(BoolExtension::default()), bool_extension;
        SMax.then(ExtensionOracle::from(BoolExtension::default())), smax_then_bool_extension;
        ExtensionOracle::from(BoolExtension::default()).then(SMax), bool_extension_then_smax;
        SMax.and(ExtensionOracle::from(BoolExtension::default())), smax_and_bool_extension;
        LocalMaxR.then(ExtensionOracle::from(BoolExtension::default())), localmaxr_then_bool_extension;
    }
}

mod ordered {
    use radguy::{
        oracle::SMax,
        ordered::{
            oracle::{CountOracle, StrategicLocalOracle, ToConstant},
            strategy::StrategyWeight,
        },
    };

    test_oracles_ordered! {
        SMax.constant(StrategyWeight::Num(0)), smax_const_0;
        SMax.constant(StrategyWeight::Infinity), smax_const_infinity;
        SMax.constant(StrategyWeight::Num(0)).then(CountOracle), smax_then_count;
        SMax.constant(StrategyWeight::Num(10)).and_by(CountOracle, std::cmp::min), smax_10_and_min_count;
    }
}
