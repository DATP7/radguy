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
                        let (result, _) = ::radguy::kleene_local(&mut system, start, &$oracle);
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
                    let mut system: radguy_ccs::systems::numeric::numeric_system::LazyNumericSystem<_,_,_> = system.into();
                    for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                        let start = system.init_target(var);
                        let (result, _) =::radguy::kleene_local(&mut system, start, &$oracle);
                        assert_eq!(result, goal, "{var} did not have the expected value");
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
    SMax::bitset(), smax_bitset;
    TrivialOracle::bitset(), trivialoracle_bitset;
    IdentityOracle::bitset(), identityoracle_bitset;
    LocalMaxR::bitset(), localmaxr_bitset;
    TrivialOracle::bitset().and(SMax::bitset()), trivialoracle_and_smax_bitset;
    LocalMaxR::bitset().and(SMax::bitset()), localmaxr_and_smax_bitset;
    LocalMaxR::bitset().and(TrivialOracle::bitset()), localmaxr_and_trivialoracle_bitset;
    TrivialOracle::bitset().then(SMax::bitset()), trivialoracle_then_smax_bitset;
    TrivialOracle::bitset().then(LocalMaxR::bitset()), trivialoracle_then_localmaxr_bitset;
    SMax::bitset().then(TrivialOracle::bitset()), smax_then_trivialoracle_bitset;
    SMax::bitset().then(LocalMaxR::bitset()), smax_then_localmaxr_bitset;
    LocalMaxR::bitset().then(SMax::bitset()), localmaxr_then_smax_bitset;
    LocalMaxR::bitset().then(TrivialOracle::bitset()), localmaxr_then_trivialoracle_bitset;
    ArgumentsOracle::bitset(), arguments_bitset;
    ArgumentsOracle::bitset().and(SMax::bitset()), args_and_smax_bitset;
    ArgumentsOracle::bitset().then(SMax::bitset()), args_then_smax_bitset;
    SMax::hashset(), smax_hashset;
    TrivialOracle::hashset(), trivialoracle_hashset;
    IdentityOracle::hashset(), identityoracle_hashset;
    LocalMaxR::hashset(), localmaxr_hashset;
    TrivialOracle::hashset().and(SMax::hashset()), trivialoracle_and_smax_hashset;
    LocalMaxR::hashset().and(SMax::hashset()), localmaxr_and_smax_hashset;
    LocalMaxR::hashset().and(TrivialOracle::hashset()), localmaxr_and_trivialoracle_hashset;
    TrivialOracle::hashset().then(SMax::hashset()), trivialoracle_then_smax_hashset;
    TrivialOracle::hashset().then(LocalMaxR::hashset()), trivialoracle_then_localmaxr_hashset;
    SMax::hashset().then(TrivialOracle::hashset()), smax_then_trivialoracle_hashset;
    SMax::hashset().then(LocalMaxR::hashset()), smax_then_localmaxr_hashset;
    LocalMaxR::hashset().then(SMax::hashset()), localmaxr_then_smax_hashset;
    LocalMaxR::hashset().then(TrivialOracle::hashset()), localmaxr_then_trivialoracle_hashset;
    ArgumentsOracle::hashset(), arguments_hashset;
    ArgumentsOracle::hashset().and(SMax::hashset()), args_and_smax_hashset;
    ArgumentsOracle::bitset().then(SMax::bitset()), args_then_smax_hashset;
}
