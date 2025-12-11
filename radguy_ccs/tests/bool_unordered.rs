use radguy::{
    extension::{ExtensionOracle, LocalExtension},
    oracle::{ArgumentsOracle, IdentityOracle, LocalMaxR, LocalOracle, SMax, TrivialOracle},
};
use radguy_ccs::systems::bool::extension::BoolExtension;

pub mod systems;

macro_rules! test_oracle_system_unordered {
    (test $oracle:expr, on: $($spec:ident),* $(,)?) => {
        $(
            mod $spec {
                use super::*;
                use std::collections::HashSet;
                use radguy::set::bitset::{BitsetRelation, BitSet};

                #[test]
                fn eager_hashset() {
                    let $crate::systems::bool::SystemSpec {
                        mut system,
                        variables,
                        goal,
                    } = $crate::systems::bool::$spec();
                    for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                        let start = system.names.get_or_insert_key(var);
                        let (result, _) = ::radguy::kleene_local::<_, _, HashSet<_>, HashSet<_>, _>(&mut system, start, &$oracle);
                        assert_eq!(result, goal, "{var} did not have the expected value");
                    }
                }

                #[test]
                fn lazy_hashset() {
                    let $crate::systems::bool::SystemSpec {
                        system,
                        variables,
                        goal,
                    } = $crate::systems::bool::$spec();
                    let mut system: radguy_ccs::systems::bool::LazyBoolSystem<_,_,_> = system.into();
                    for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                        let start = system.init_target(var);
                        let (result, _) = ::radguy::kleene_local::<_, _, HashSet<_>, HashSet<_>, _>(&mut system, start, &$oracle);
                        assert_eq!(result, goal, "{var} did not have the expected value");
                    }
                }

                #[test]
                fn eager_bitset() {
                    let $crate::systems::bool::SystemSpec {
                        mut system,
                        variables,
                        goal,
                    } = $crate::systems::bool::$spec();
                    for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                        let start = system.names.get_or_insert_key(var);
                        let (result, _) = ::radguy::kleene_local::<_, _, BitSet<_>, BitsetRelation<_, _>, _>(&mut system, start, &$oracle);
                        assert_eq!(result, goal, "{var} did not have the expected value");
                    }
                }

                #[test]
                fn lazy_bitset() {
                    let $crate::systems::bool::SystemSpec {
                        system,
                        variables,
                        goal,
                    } = $crate::systems::bool::$spec();
                    let mut system: radguy_ccs::systems::bool::LazyBoolSystem<_,_,_> = system.into();
                    for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                        let start = system.init_target(var);
                        let (result, _) = ::radguy::kleene_local::<_, _, BitSet<_>, BitsetRelation<_, _>, _>(&mut system, start, &$oracle);
                        assert_eq!(result, goal, "{var} did not have the expected value");
                    }
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
                chain,
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
test_oracles_unordered! {
    SMax::default(), smax;
    TrivialOracle::default(), trivialoracle;
    IdentityOracle::default(), identityoracle;
    LocalMaxR::default(), localmaxr;
    TrivialOracle::default().and(SMax::default()), trivialoracle_and_smax;
    LocalMaxR::default().and(SMax::default()), localmaxr_and_smax;
    LocalMaxR::default().and(TrivialOracle::default()), localmaxr_and_trivialoracle;
    TrivialOracle::default().then(SMax::default()), trivialoracle_then_smax;
    TrivialOracle::default().then(LocalMaxR::default()), trivialoracle_then_localmaxr;
    SMax::default().then(TrivialOracle::default()), smax_then_trivialoracle;
    SMax::default().then(LocalMaxR::default()), smax_then_localmaxr;
    LocalMaxR::default().then(SMax::default()), localmaxr_then_smax;
    LocalMaxR::default().then(TrivialOracle::default()), localmaxr_then_trivialoracle;
    BoolExtension::oracle(), bool_extension;
    SMax::default().then(ExtensionOracle::from(BoolExtension::default())), smax_then_bool_extension;
    ExtensionOracle::from(BoolExtension::default()).then(SMax::default()), bool_extension_then_smax;
    SMax::default().and(ExtensionOracle::from(BoolExtension::default())), smax_and_bool_extension;
    LocalMaxR::default().then(ExtensionOracle::from(BoolExtension::default())), localmaxr_then_bool_extension;
    ArgumentsOracle::default(), arguments;
    ArgumentsOracle::default().and(SMax::default()), arguments_and_smax;
    ArgumentsOracle::default().and(IdentityOracle::default()), arguments_and_identity;
}
