use radguy::kleene_local;
use radguy::oracle::SMax;
use radguy_ccs::systems::wccs::wccs_system::WCCSSystem;
use radguy_ccs::systems::wccs;
use radguy_ccs::systems::wctl;
use radguy_ccs::systems::wctl::WCTLSystem;
use slotmap::DefaultKey;

macro_rules! wctl_test {
        ($($state:literal, $formula:literal => $eq:literal in $wccs:expr, $wctl:expr;)*) => {
            $(
                {
                    let wccs_parser = wccs::ProgramParser::new();
                    let wccs_ast = wccs_parser
                        .parse(&$wccs)
                        .expect("Failed to parse WCCS program content.");
                    let mut transition_system = WCCSSystem::<DefaultKey>::default();
                    transition_system.insert_ast_bindings(wccs_ast);

                    let wctl_parser = wctl::ProgramParser::new();
                    let wctl_bindings = wctl_parser.parse(&$wctl).expect("Failed to parse WCTL program content.")
                    let formula = wctl_bindings.get($formula).expect("Formula should be bound");

                    let mut sys = WCTLSystem::default();
                    //let mut sys = BisimulationSystem::<DefaultKey, DefaultKey, DefaultKey, StrongTransitionSystem<DefaultKey>>::new(strong_transition_system);
                    let start = sys.specify_comparison($state, $formula);


                    let result = !kleene_local(&sys, start, &SMax::default());
                    assert_eq!($eq, result, "{} should{} satisfy {} in {} {}", $left, $right, if !$eq { " not" } else {""}, $ccs);
                }
            )*
        };
    }


#[test]
fn wctl() {
    wctl_test! {
        "S", "T" => true in r"
            S = (a.a.a.0)[b/a];
            T = b.b.b.0;
        ";
    };
}
