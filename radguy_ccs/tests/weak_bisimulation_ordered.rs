use radguy::ordered::kleene_local;
use radguy_ccs::systems::ccs::bisimulation_system::BisimulationSystem;
use radguy_ccs::systems::ccs::grammar::ProgramParser;
use radguy_ccs::systems::ccs::transition_system::TransitionSystem;
use radguy_ccs::systems::ccs::weak_transition_system::WeakTransitionSystem;
use slotmap::DefaultKey;

use radguy::{
    extension::LocalExtension,
    oracle::SMax,
    ordered::{
        oracle::{CountOracle, SiblingsOracle, StrategicLocalOracle, ToConstant},
        strategy::StrategyWeight,
    },
};
use radguy_ccs::systems::bool::extension::BoolExtension;

macro_rules! weak_bisim_test {
        ($oracle:expr, $strategy:ty, $($name:ident: $left:expr, $right:expr => $eq:literal in $ccs:expr;)*) => {
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

                    let result = !kleene_local::<_, _, $strategy, $strategy, _>(&mut sys, start, &$oracle);
                    assert_eq!($eq, result, "{} and {} should{} be bisimilar in{}", $left, $right, if !$eq { " not" } else {""}, $ccs);
                }
            )*
        };
    }

macro_rules! weak_bisim_test_strategies {
    ($oracle:expr, $($stratagy_type_name:ident: $stratagy_type:ty;)*) => {
        $(
            mod $stratagy_type_name {
                use super::*;
                weak_bisim_test!{
                    $oracle, $stratagy_type,
                    abp_ok_small: "SPEC", "ABP" => true in include_str!("../systems/ccs/abp_ok.ccs");
                    abpl_ok_small_1: "SPEC", "ABPl" => true in include_str!("../systems/ccs/abp_ok.ccs");
                    abp_bad_small: "SPEC", "ABP" => true in include_str!("../systems/ccs/abp_bad.ccs");
                    abpl_bad_small_2: "SPEC", "ABPl_2" => false in include_str!("../systems/ccs/abp_bad.ccs");
                    simple_infinite_tau_loop: "S", "T" => true in r"
                        S = tau.S;
                        T = 0;
                    ";
                    dual_tau_loop: "A", "B" => true in r"
                        A = tau.B + a.0;
                        B = tau.A + b.0;
                        Spec = a.0 + b.0;
                    ";
                    tau_prefix:  "S", "T" => false in r"
                        S = tau.(a.0 + b.0);
                        T = tau.a.0 + tau.b.0;
                    ";
                    basic_buffer_example: "Buff3", "Spec" => true in r"
                        Buff3 = (C0 | C1 | C2)\{c,d};
                        C0 = Cell[c/b];
                        C1 = Cell[c/a,d/b];
                        C2 = Cell[d/a];
                        Cell = a.'b.Cell;

                        Spec = a.Spec';
                        Spec' = 'b.Spec + a.Spec'';
                        Spec'' = 'b.Spec' + a.'b.Spec'';
                    ";
                    dekkers_mutual_exclusion: "Dekker-2", "Spec" => true in include_str!("../systems/ccs/dekkers_mutual_exclusion.ccs");
                    orchard: "Spec", "Orchard" => true in r"
                        Man = 'shake.(redapple.walk.Man + greenapple.walk.Man);
                        AppleTree = shake.('greenapple.AppleTree + 'redapple.AppleTree);
                        Orchard = (AppleTree | Man) \ {shake, redapple, greenapple};
                        Spec = walk.Spec;
                    ";
                    leader_election_ok_3: "Spec", "Ring" => true in include_str!("../systems/ccs/leader_election_ok_3.ccs");
                    leader_election_bad_3: "Spec", "Ring" => false in include_str!("../systems/ccs/leader_election_bad_3.ccs");
                }
            }
        )*
    }
}

macro_rules! weak_bisim_test_oracles {
    ($($oracle:expr, $name:ident;)*) => {
        $(
            mod $name {
                use super::*;
                use radguy::ordered::strategy::{BinaryHeapStrategy, HashMapStrategy, OrxStrategy, LazyHeap};
                use orx_priority_queue::DaryHeapWithMap;

                weak_bisim_test_strategies! {
                    $oracle,
                    std_binary: BinaryHeapStrategy<_>;
                    std_hashmap: HashMapStrategy<_>;
                    orx_quad: OrxStrategy<_, DaryHeapWithMap<_, StrategyWeight, 4>>;
                    std_binary_lazy: LazyHeap<_, BinaryHeapStrategy<_>>;
                    orx_quad_lazy: LazyHeap<_, OrxStrategy<_, DaryHeapWithMap<_, StrategyWeight, 4>>>;
                }
            }
        )*
    }
}

weak_bisim_test_oracles! {
    BoolExtension::oracle().constant(StrategyWeight::Num(1)).then(SiblingsOracle::default()), bool_extension_1_then_siblings;
    SMax.constant(StrategyWeight::Num(0)), smax_const_0;
    SMax.constant(StrategyWeight::Num(0)).then(CountOracle::default()), smax_then_count;
    // These are commented out due to perfromance
    // TrivialOracle.constant(StrategyWeight::Infinity), trivial_oracle_inf;
    // IdentityOracle.constant(StrategyWeight::Infinity), identity_oracle_inf;
    // SMax.constant(StrategyWeight::Infinity), smax_const_infinity;
    // SMax.constant(StrategyWeight::Num(1)), smax_const_1;
    // SMax.constant(StrategyWeight::Num(1)).then(SiblingsOracle::default()), smax_const_1_siblings;
    // SMax.constant(StrategyWeight::Num(10)).and_by(CountOracle::default(), std::cmp::min), smax_10_and_min_count;
    // BoolExtension::oracle().constant(StrategyWeight::Num(0)), bool_extension_0;
    // BoolExtension::oracle().constant(StrategyWeight::Num(0)).and_by(CountOracle::default(), std::cmp::min), bool_extension_0_and_min_count;
    // BoolExtension::oracle().constant(StrategyWeight::Infinity).and_by(CountOracle::default(), std::cmp::min), bool_extension_inf_and_min_count;
    // BoolExtension::oracle().constant(StrategyWeight::Infinity).and_by(InverseCountOracle::default(), std::cmp::min), bool_extension_inf_and_min_count_inverse;
    // CountOracle::default(), count;
    // InverseCountOracle::default(), count_inverse;
    // StrategicArgumentsOracle::default(), arguments_s;
    // StrategicArgumentsOracle::default().and_by(CountOracle::default(), std::cmp::min), args_s_and_min_count;
    // StrategicArgumentsOracle::default().and_by(InverseCountOracle::default(), std::cmp::min), args_s_and_min_count_inverse;
}
