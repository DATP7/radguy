use radguy::oracle::{
    ArgumentsOracle, IdentityOracle, LocalMaxR, LocalOracle, SMax, TrivialOracle,
};

pub mod systems;

macro_rules! test_numerical_oracle_system_unordered {
    (test $oracle:expr, on: $($spec:ident),* $(,)?) => {
        $(
            mod $spec {
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
                        assert_eq!(::radguy::kleene_local(&mut system, start, &$oracle), goal, "{var} did not have the expected value");
                    }
                }
                #[test]
                fn lazy() {
                    let $crate::systems::numeric::NumericSystemSpec {
                        system,
                        variables,
                        goal,
                    } = $crate::systems::numeric::$spec();
                    let mut system: radguy_ccs::systems::numeric::numeric_system::LazyNumericSystem<_,_,_> = system.into();
                    for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                        let start = system.init_target(var);
                        assert_eq!(::radguy::kleene_local(&mut system, start, &$oracle), goal, "{var} did not have the expected value");
                    }
                }
            }
        )*
    };
}

macro_rules! test_oracle_unordered_numerical {
    ($oracle:expr, $name:ident) => {
        mod $name {
            use super::*;
            test_numerical_oracle_system_unordered! {
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

macro_rules! test_oracles_unordered_numerical {
    ( $( $oracle:expr, $name:ident; )*) => {
            $(
                test_oracle_unordered_numerical!($oracle, $name);
            )*
    };
}
test_oracles_unordered_numerical! {
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
    ArgumentsOracle::default(), arguments;
}
