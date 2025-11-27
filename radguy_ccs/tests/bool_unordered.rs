use radguy::{
    extension::ExtensionOracle,
    oracle::{ArgumentsOracle, IdentityOracle, LocalMaxR, LocalOracle, SMax, TrivialOracle},
};
use radguy_ccs::systems::bool::extension::BoolExtension;

pub mod systems;

macro_rules! test_oracle_system_unordered {
    (test $oracle:expr, on: $($spec:ident),* $(,)?) => {
        $(
            mod $spec {
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
                        let (result, _) = ::radguy::kleene_local(&mut system, start, &$oracle);
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
                    let mut system: radguy_ccs::systems::bool::LazyBoolSystem<_,_,_> = system.into();
                    for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                        let start = system.init_target(var);
                        let (result, _) = ::radguy::kleene_local(&mut system, start, &$oracle);
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
    SMax, smax;
    TrivialOracle, trivialoracle;
    IdentityOracle, identityoracle;
    LocalMaxR::default(), localmaxr;
    TrivialOracle.and(SMax), trivialoracle_and_smax;
    LocalMaxR::default().and(SMax), localmaxr_and_smax;
    LocalMaxR::default().and(TrivialOracle), localmaxr_and_trivialoracle;
    TrivialOracle.then(SMax), trivialoracle_then_smax;
    TrivialOracle.then(LocalMaxR::default()), trivialoracle_then_localmaxr;
    SMax.then(TrivialOracle), smax_then_trivialoracle;
    SMax.then(LocalMaxR::default()), smax_then_localmaxr;
    LocalMaxR::default().then(SMax), localmaxr_then_smax;
    LocalMaxR::default().then(TrivialOracle), localmaxr_then_trivialoracle;
    ExtensionOracle::from(BoolExtension::default()), bool_extension;
    SMax.then(ExtensionOracle::from(BoolExtension::default())), smax_then_bool_extension;
    ExtensionOracle::from(BoolExtension::default()).then(SMax), bool_extension_then_smax;
    SMax.and(ExtensionOracle::from(BoolExtension::default())), smax_and_bool_extension;
    LocalMaxR::default().then(ExtensionOracle::from(BoolExtension::default())), localmaxr_then_bool_extension;
    ArgumentsOracle::default(), arguments;
}
