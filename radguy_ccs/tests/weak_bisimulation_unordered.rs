use radguy::kleene_local;
use radguy_ccs::systems::ccs::bisimulation_system::BisimulationSystem;
use radguy_ccs::systems::ccs::grammar::ProgramParser;
use radguy_ccs::systems::ccs::transition_system::TransitionSystem;
use radguy_ccs::systems::ccs::weak_transition_system::WeakTransitionSystem;
use slotmap::DefaultKey;

use radguy::{
    extension::ExtensionOracle,
    oracle::{ArgumentsOracle, IdentityOracle, LocalMaxR, LocalOracle, SMax, TrivialOracle},
};
use radguy_ccs::systems::bool::extension::BoolExtension;

macro_rules! weak_bisim_test {
        ($($name:ident: $oracle:expr, $left:expr, $right:expr => $eq:literal in $ccs:expr;)*) => {
            $(
                #[test]
                fn $name()
                {
                    let parser = ProgramParser::new();
                    let program_ast = parser
                        .parse(&$ccs)
                        .expect("Failed to parse CCS program content.");
                    let mut weak_transition_system = WeakTransitionSystem::<DefaultKey>::default();
                    weak_transition_system.load_ast(program_ast);

                    let mut sys = BisimulationSystem::<DefaultKey, DefaultKey, DefaultKey, WeakTransitionSystem<DefaultKey>>::new(weak_transition_system);
                    let start = sys.specify_comparison($left, $right);

                    let result = !kleene_local(&mut sys, start, &$oracle);
                    assert_eq!($eq, result, "{} and {} should{} be bisimilar in{}", $left, $right, if !$eq { " not" } else {""}, $ccs);
                }
            )*
        };
    }

macro_rules! weak_bisim_test_oracles {
    ($($oracle:expr, $name:ident;)*) => {
        $(
            mod $name {
                use super::*;
                weak_bisim_test!{
                    abp_ok_small: $oracle, "SPEC", "ABP" => true in include_str!("../systems/ccs/abp_ok.ccs");
                    abpl_ok_small_1: $oracle, "SPEC", "ABPl" => true in include_str!("../systems/ccs/abp_ok.ccs");
                    abpl_ok_small_2: $oracle, "SPEC", "ABPl_2" => true in include_str!("../systems/ccs/abp_ok.ccs");
                    abp_bad_small: $oracle, "SPEC", "ABP" => true in include_str!("../systems/ccs/abp_bad.ccs");
                    abpl_bad_small_2: $oracle, "SPEC", "ABPl_2" => false in include_str!("../systems/ccs/abp_bad.ccs");
                    abpl_bad_small_3: $oracle, "SPEC", "ABPl_3" => false in include_str!("../systems/ccs/abp_bad.ccs");
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
                    dekkers_mutual_exclusion: $oracle, "Dekker-2", "Spec" => true in include_str!("../systems/ccs/dekkers_mutual_exclusion.ccs");
                    orchard: $oracle, "Spec", "Orchard" => true in r"
                    Man = 'shake.(redapple.walk.Man + greenapple.walk.Man);
                    AppleTree = shake.('greenapple.AppleTree + 'redapple.AppleTree);
                    Orchard = (AppleTree | Man) \ {shake, redapple, greenapple};
                    Spec = walk.Spec;
                    ";
                    leader_election_ok_6: $oracle, "Spec", "Ring" => true in include_str!("../systems/ccs/leader_election_ok_6.ccs");
                    leader_election_bad_6: $oracle, "Spec", "Ring" => false in include_str!("../systems/ccs/leader_election_bad_6.ccs");
                }
            }
        )*
    }
}

weak_bisim_test_oracles! {
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
