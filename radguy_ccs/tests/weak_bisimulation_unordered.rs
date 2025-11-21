use radguy::kleene_local;
use radguy_ccs::systems::ccs::bisimulation_system::BisimulationSystem;
use radguy_ccs::systems::ccs::grammar::ProgramParser;
use radguy_ccs::systems::ccs::transition_system::TransitionSystem;
use radguy_ccs::systems::ccs::weak_transition_system::WeakTransitionSystem;

use radguy::oracle::{
    ArgumentsOracle, IdentityOracle, LocalMaxR, LocalOracle, SMax, TrivialOracle,
};
use radguy_ccs::systems::bool::extension::BoolExtension;

macro_rules! weak_bisim_test_fast {
    ($($name:ident: $oracle:expr, $left:expr, $right:expr => $eq:literal in $ccs:expr;)*) => {
        $(
            #[test]
            fn $name()
            {
                let parser = ProgramParser::new();
                let program_ast = parser
                    .parse(&$ccs)
                    .expect("Failed to parse CCS program content.");
                let mut weak_transition_system = WeakTransitionSystem::<usize>::default();
                weak_transition_system.load_ast(program_ast);

                let mut sys = BisimulationSystem::<usize, usize, usize, WeakTransitionSystem<usize>>::new(weak_transition_system);
                let start = sys.specify_comparison($left, $right);

                let (result, _) = kleene_local(&mut sys, start, &$oracle);
                assert_eq!($eq, !result, "{} and {} should{} be bisimilar in{}", $left, $right, if !$eq { " not" } else {""}, $ccs);
            }
        )*
    };
}

macro_rules! weak_bisim_test_slow {
    ($($name:ident: $oracle:expr, $left:expr, $right:expr => $eq:literal in $ccs:expr;)*) => {
        $(
            #[test]
            #[cfg_attr(not(feature = "slow"), ignore = "Not running slow tests")]
            fn $name()
            {
                let parser = ProgramParser::new();
                let program_ast = parser
                    .parse(&$ccs)
                    .expect("Failed to parse CCS program content.");
                let mut weak_transition_system = WeakTransitionSystem::<usize>::default();
                weak_transition_system.load_ast(program_ast);

                let mut sys = BisimulationSystem::<usize, usize, usize, WeakTransitionSystem<usize>>::new(weak_transition_system);
                let start = sys.specify_comparison($left, $right);

                let (result, _) = kleene_local(&mut sys, start, &$oracle);
                assert_eq!($eq, !result, "{} and {} should{} be bisimilar in{}", $left, $right, if !$eq { " not" } else {""}, $ccs);
            }
        )*
    };
}

macro_rules! weak_bisim_test_oracles {
    ($($oracle:expr, $name:ident;)*) => {
        $(
            mod $name {
                use super::*;
                weak_bisim_test_fast!{
                    simple_infinite_tau_loop: $oracle, "S", "T" => true in r"
                    S = tau.S;
                    T = 0;
                    ";
                    dual_tau_loop: $oracle, "A", "B" => true in r"
                    A = tau.B + a.0;
                    B = tau.A + b.0;
                    Spec = a.0 + b.0;
                    ";
                    tau_prefix: $oracle,  "S", "T" => false in r"
                    S = tau.(a.0 + b.0);
                    T = tau.a.0 + tau.b.0;
                    ";
                    basic_buffer_example: $oracle, "Buff3", "Spec" => true in r"
                    Buff3 = (C0 | C1 | C2)\{c,d};
                    C0 = Cell[c/b];
                    C1 = Cell[c/a,d/b];
                    C2 = Cell[d/a];
                    Cell = a.'b.Cell;
                    
                    Spec = a.Spec';
                    Spec' = 'b.Spec + a.Spec'';
                    Spec'' = 'b.Spec' + a.'b.Spec'';
                    ";
                    orchard: $oracle, "Spec", "Orchard" => true in r"
                    Man = 'shake.(redapple.walk.Man + greenapple.walk.Man);
                    AppleTree = shake.('greenapple.AppleTree + 'redapple.AppleTree);
                    Orchard = (AppleTree | Man) \ {shake, redapple, greenapple};
                    Spec = walk.Spec;
                    ";
                }
                weak_bisim_test_slow!{
                    abp_ok_small: $oracle, "SPEC", "ABP" => true in include_str!("../systems/ccs/abp_ok.ccs");
                    abpl_ok_small_1: $oracle, "SPEC", "ABPl" => true in include_str!("../systems/ccs/abp_ok.ccs");
                    abp_bad_small: $oracle, "SPEC", "ABP" => true in include_str!("../systems/ccs/abp_bad.ccs");
                    abpl_bad_small_2: $oracle, "SPEC", "ABPl_2" => false in include_str!("../systems/ccs/abp_bad.ccs");
                    dekkers_mutual_exclusion: $oracle, "Dekker-2", "Spec" => true in include_str!("../systems/ccs/dekkers_mutual_exclusion.ccs");
                    leader_election_ok_3: $oracle, "Spec", "Ring" => true in include_str!("../systems/ccs/leader_election_ok_3.ccs");
                    leader_election_bad_3: $oracle, "Spec", "Ring" => false in include_str!("../systems/ccs/leader_election_bad_3.ccs");
                }
            }
        )*
    }
}

weak_bisim_test_oracles! {
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
    BoolExtension::bitset().as_oracle(), bool_extension_bitset;
    SMax::bitset().then(BoolExtension::bitset().as_oracle()), smax_then_bool_extension_bitset;
    BoolExtension::bitset().as_oracle().then(SMax::bitset()), bool_extension_then_smax_bitset;
    SMax::bitset().and(BoolExtension::bitset().as_oracle()), smax_and_bool_extension_bitset;
    LocalMaxR::bitset().then(BoolExtension::bitset().as_oracle()), localmaxr_then_bool_extension_bitset;
    ArgumentsOracle::bitset(), arguments_bitset;
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
    BoolExtension::hashset().as_oracle(), bool_extension_hashset;
    SMax::hashset().then(BoolExtension::hashset().as_oracle()), smax_then_bool_extension_hashset;
    BoolExtension::hashset().as_oracle().then(SMax::hashset()), bool_extension_then_smax_hashset;
    SMax::hashset().and(BoolExtension::hashset().as_oracle()), smax_and_bool_extension_hashset;
    LocalMaxR::hashset().then(BoolExtension::hashset().as_oracle()), localmaxr_then_bool_extension_hashset;
    ArgumentsOracle::hashset(), arguments_hashset;

}
