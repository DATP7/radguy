use radguy::ordered;
use radguy::{
    oracle::{IdentityOracle, SMax, TrivialOracle, WeightedDepOracle},
    ordered::{
        oracle::{
            CountOracle, InverseCountOracle, SiblingsOracle, StrategicArgumentsOracle,
            StrategicLocalOracle, ToConstant,
        },
        strategy::StrategyWeight,
    },
};

use radguy_ccs::systems::numeric::Number;
use radguy_ccs::systems::wccs;
use radguy_ccs::systems::wccs::wccs_system::WCCSSystem;
use radguy_ccs::systems::wctl;
use radguy_ccs::systems::wctl::wctl_system::WCTLSystem;
use slotmap::DefaultKey;

macro_rules! wctl_test {
    ($($(#ignore($reason:literal))? $test_name:ident: $oracle:expr, $strategy_type:ty, $($process_name:literal, $formula_str:expr => $eq:literal),* $(,)? in $wccs:expr;)*) => {
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
                    let mut wccs_system = WCCSSystem::<DefaultKey>::default();
                    wccs_system.insert_ast_bindings(wccs_ast);

                    let formula_parser = wctl::grammar::FormulaParser::new();
                    let formula = formula_parser.parse($formula_str).expect("Formula should parse");

                    let mut sys = WCTLSystem::<DefaultKey, DefaultKey, DefaultKey, DefaultKey, DefaultKey>::new(wccs_system);
                    let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
                    let formula_key = sys.insert_ast_formula(formula.clone());
                    let start = sys.get_var(process_key, formula_key);

                    let (result, _) = ordered::kleene_local::<_, _, $strategy_type, $strategy_type, _>(&mut sys, start, &$oracle);
                    assert_eq!($eq, result == Number::Val(0), "{} should{} satisfy {} in {}", $process_name, if !$eq { " not" } else {""}, $formula_str, $wccs);
                )*
            }
        )*
    };
}

macro_rules! wctl_test_oracles_strategy {
    ($($strategy:ident: $strategy_type:ty, $oracle:expr;)*) => {
        $(
            mod $strategy {
                use super::*;
                wctl_test! {
                    mower_example: $oracle, $strategy_type,
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
                    proposition: $oracle, $strategy_type, "S", "mow" => true in "S := mow:0;";
                    proposition_multiple: $oracle, $strategy_type, "S", "mow && dump" => true in "S := mow:dump:0;";
                    proposition_multiple_neg: $oracle, $strategy_type, "S", "mow && dump && dud" => false in "S := mow:dump:0;";
                    linear_universal_final: $oracle, $strategy_type, "S", "AF dump" => true in "S := <go>.<go>.<go>.<go>.dump:0;";
                    recursive: $oracle, $strategy_type, "S", "AF dump" => true in "S := <go>.dump:S;";
                    recursive_neg: $oracle, $strategy_type, "S", "AF mow" => false in "S := <go>.dump:S;";
                    compare: $oracle, $strategy_type, "S", "mow == 4" => true in "S := mow:0 + mow:0 + mow:0 + mow:0;";
                    leader_election: $oracle, $strategy_type,
                    "Ring", "EF leader > 1" => false,
                    "Ring", "EF leader" => true
                    in include_str!("../systems/wccs/LeaderElection2.wccs");

                    #ignore("too slow") bit_protocol: $oracle, $strategy_type, "System", "EF[<= 35] delivered == 7" => true in include_str!("../systems/wccs/BitProtocol(B5M7).wccs");
                    #ignore("too slow") client_server: $oracle, $strategy_type,
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

macro_rules! wctl_test_oracles {
    ($($oracle:expr, $name:ident;)*) => {
        $(
            mod $name {
                use super::*;
                use radguy::ordered::strategy::{BinaryHeapStrategy, HashMapStrategy, OrxStrategy, LazyHeap};
                use orx_priority_queue::DaryHeapWithMap;

                wctl_test_oracles_strategy! {
                    std_binary: BinaryHeapStrategy<_>, $oracle;
                    std_hashmap: HashMapStrategy<_>, $oracle;
                    orx_quad: OrxStrategy<_, DaryHeapWithMap<_, StrategyWeight, 4>>, $oracle;
                    std_binary_lazy: LazyHeap<_, BinaryHeapStrategy<_>>, $oracle;
                    orx_quad_lazy: LazyHeap<_, OrxStrategy<_, DaryHeapWithMap<_, StrategyWeight, 4>>>, $oracle;
                }
            }
        )*
    }
}

wctl_test_oracles! {
    IdentityOracle.constant(StrategyWeight::Infinity), identity_oracle_inf;
    TrivialOracle.constant(StrategyWeight::Infinity), trivial_oracle_inf;
    SMax.constant(StrategyWeight::Num(0)), smax_const_0;
    SMax.constant(StrategyWeight::Infinity), smax_const_infinity;
    SMax.constant(StrategyWeight::Num(0)).then(CountOracle::default()), smax_then_count;
    SMax.constant(StrategyWeight::Num(10)).and_by(CountOracle::default(), std::cmp::min), smax_10_and_min_count;
    WeightedDepOracle::default().constant(StrategyWeight::Num(1)).then(SiblingsOracle), wctl_1_then_siblings;
    CountOracle::default(), count;
    InverseCountOracle::default(), count_inverse;
    StrategicArgumentsOracle::successors(), arguments_s_s;
    StrategicArgumentsOracle::successors().and_by(CountOracle::default(), std::cmp::min), args_s_s_and_min_count;
    StrategicArgumentsOracle::successors().and_by(InverseCountOracle::default(), std::cmp::min), args_s_s_and_min_count_inverse;
    StrategicArgumentsOracle::ancestors(), arguments_s_a;
    StrategicArgumentsOracle::ancestors().and_by(CountOracle::default(), std::cmp::min), args_s_a_and_min_count;
    StrategicArgumentsOracle::ancestors().and_by(InverseCountOracle::default(), std::cmp::min), args_s_a_and_min_count_inverse;
}
