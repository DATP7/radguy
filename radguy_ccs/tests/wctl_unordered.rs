use radguy::kleene_local;

use radguy::oracle::{
    ArgumentsOracle, IdentityOracle, LocalMaxR, LocalOracle, SMax, TrivialOracle, WeightedDepOracle,
};

use radguy_ccs::systems::numeric::Number;
use radguy_ccs::systems::wccs;
use radguy_ccs::systems::wccs::wccs_system::WCCSSystem;
use radguy_ccs::systems::wctl;
use radguy_ccs::systems::wctl::wctl_system::WCTLSystem;

macro_rules! wctl_test_fast {
    ($($(#ignore($reason:literal))? $test_name:ident: $oracle:expr, $($process_name:literal, $formula_str:expr => $eq:literal),* $(,)? in $wccs:expr;)*) => {
        $(
            $(#[ignore = $reason])?
            #[test]
            fn $test_name()
            {
                $(
                    let wccs_parser = wccs::ProgramParser::new();
                    let wccs_ast = wccs_parser
                        .parse(&$wccs)
                        .expect("Failed to parse WCCS program content.");
                    let mut wccs_system = WCCSSystem::<usize>::default();
                    wccs_system.insert_ast_bindings(wccs_ast);

                    let formula_parser = wctl::grammar::FormulaParser::new();
                    let formula = formula_parser.parse($formula_str).expect("Formula should parse");

                    let mut sys = WCTLSystem::<usize, usize, usize, usize, usize>::new(wccs_system);
                    let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
                    let formula_key = sys.insert_ast_formula(formula.clone());
                    let start = sys.get_var(process_key, formula_key);

                    let (result, _) = kleene_local(&mut sys, start, &$oracle);
                    assert_eq!($eq, result == Number::Val(0), "{} should{} satisfy {} in {}", $process_name, if !$eq { " not" } else {""}, $formula_str, $wccs);
                )*
            }
        )*
    };
}
macro_rules! wctl_test_slow {
    ($($(#ignore($reason:literal))? $test_name:ident: $oracle:expr, $($process_name:literal, $formula_str:expr => $eq:literal),* $(,)? in $wccs:expr;)*) => {
        $(
            #[cfg_attr(not(feature = "slow"), ignore = "Not running slow tests")]
            #[allow(unused_attributes)]
            $(#[ignore = $reason])?
            #[test]
            fn $test_name()
            {
                $(
                    let wccs_parser = wccs::ProgramParser::new();
                    let wccs_ast = wccs_parser
                        .parse(&$wccs)
                        .expect("Failed to parse WCCS program content.");
                    let mut wccs_system = WCCSSystem::<usize>::default();
                    wccs_system.insert_ast_bindings(wccs_ast);

                    let formula_parser = wctl::grammar::FormulaParser::new();
                    let formula = formula_parser.parse($formula_str).expect("Formula should parse");

                    let mut sys = WCTLSystem::<usize, usize, usize, usize, usize>::new(wccs_system);
                    let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
                    let formula_key = sys.insert_ast_formula(formula.clone());
                    let start = sys.get_var(process_key, formula_key);

                    let (result, _) = kleene_local(&mut sys, start, &$oracle);
                    assert_eq!($eq, result == Number::Val(0), "{} should{} satisfy {} in {}", $process_name, if !$eq { " not" } else {""}, $formula_str, $wccs);
                )*
            }
        )*
    };
}

macro_rules! wctl_test_oracles {
    ($($oracle:expr, $name:ident;)*) => {
        $(
            mod $name {
                use super::*;
                wctl_test_fast! {
                    mower_example: $oracle,
                        "S0", "A mow U[<=6] dump" => true,
                        "S0", "A mow U[<=4] dump" => false,
                        in r"
                        S0 := mow:(<go,2>.S1 + <go,2>.S2 + <go,2>.S3);
                        S1 := mow:<go,1>.S4;
                        S2 := mow:<go,2>.S4;
                        S3 := mow:<go,1>.S5;
                        S4 := mow:(<go,0>.S5 + <go,1>.S6);
                        S5 := mow:<go,2>.S6;
                        S6 := dump:<go,0>.S6;
                    ";
                    proposition: $oracle, "S", "mow" => true in "S := mow:0;";
                    proposition_multiple: $oracle, "S", "mow && dump" => true in "S := mow:dump:0;";
                    proposition_multiple_neg: $oracle, "S", "mow && dump && dud" => false in "S := mow:dump:0;";
                    linear_universal_final: $oracle, "S", "AF dump" => true in "S := <go>.<go>.<go>.<go>.dump:0;";
                    recursive: $oracle, "S", "AF dump" => true in "S := <go>.dump:S;";
                    recursive_neg: $oracle, "S", "AF mow" => false in "S := <go>.dump:S;";
                    compare: $oracle, "S", "mow == 4" => true in "S := mow:0 + mow:0 + mow:0 + mow:0;";
                }
                wctl_test_slow! {
                    leader_election: $oracle,
                    "Ring", "EF leader > 1" => false,
                    "Ring", "EF leader" => true
                    in include_str!("../systems/wccs/LeaderElection2.wccs");

                    semaphore_3_5_fail: $oracle, "System", "EF critical_section > 3" => false in include_str!("../systems/wccs/Semaphore_3_5.wccs");
                    semaphore_3_5_succ: $oracle, "System", "EF critical_section == 3" => true in include_str!("../systems/wccs/Semaphore_3_5.wccs");

                    #ignore("too slow") bit_protocol: $oracle, "System", "EF[<= 35] delivered == 7" => true in include_str!("../systems/wccs/BitProtocol(B5M7).wccs");
                    client_server: $oracle,
                        "System", "E True U[<=10] (A True U[<=1] failed)" => true,
                        "System", "E True U[<=8] delivered" => true,
                        "System", "E True U[<=5] failed" => true,
                        "System", "EF[<=10] (AF[<=1] failed)" => true,
                        in include_str!("../systems/wccs/ClientServer.wccs");
                }
            }
        )*
    }
}

wctl_test_oracles! {
    SMax::bitset(), smax_bitset;
    WeightedDepOracle::bitset(), wctl_oracle_bitset;
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
    SMax::hashset(), smax_hashset;
    WeightedDepOracle::hashset(), wctl_oracle_hashset;
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
}
