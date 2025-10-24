use radguy::kleene_local;
use radguy::oracle::SMax;
use radguy_ccs::systems::ccs::grammar::ProgramParser;
use radguy_ccs::systems::ccs::strong_bisimulation_system::BisimulationSystem;
use radguy_ccs::systems::ccs::transition_system::TransitionSystem;
use radguy_ccs::systems::ccs::weak_transition_system::WeakTransitionSystem;
use slotmap::DefaultKey;

macro_rules! weak_bisim_test {
        ($($left:expr, $right:expr => $eq:literal in $ccs:expr;)*) => {
            $(
                {
                    let parser = ProgramParser::new();
                    let program_ast = parser
                        .parse(&$ccs)
                        .expect("Failed to parse CCS program content.");
                    let mut weak_transition_system = WeakTransitionSystem::<DefaultKey>::default();
                    weak_transition_system.load_ast(program_ast);

                    let mut sys = BisimulationSystem::<DefaultKey, DefaultKey, DefaultKey, WeakTransitionSystem<DefaultKey>>::new(weak_transition_system);
                    let start = sys.specify_comparison($left, $right);


                    let result = !kleene_local(&sys, start, &SMax);
                    assert_eq!($eq, result, "{} and {} should{} be bisimilar in{}", $left, $right, if !$eq { " not" } else {""}, $ccs);
                }
            )*
        };
    }

#[test]
fn infinete_tau_loop() {
    weak_bisim_test! {
        "S", "T" => true in r"
            S = tau.S;
            T = 0;
        ";
    };
}

#[test]
fn basic_buffer_example() {
    weak_bisim_test! {
        "Buff3", "Spec" => true in r"
            Buff3 = (C0 | C1 | C2)\{c,d};
            C0 = Cell[c/b];
            C1 = Cell[c/a,d/b];
            C2 = Cell[d/a];
            Cell = a.'b.Cell;

            Spec = a.Spec';
            Spec' = 'b.Spec + a.Spec'';
            Spec'' = 'b.Spec' + a.'b.Spec'';
        ";
    };
}

#[test]
fn dekkers_mutual_exclusion() {
    weak_bisim_test! {
        "Dekker-2", "Spec" => true in r"
            B1f = 'b1rf.B1f + b1wf.B1f + b1wt.B1t;
            B1t = 'b1rt.B1t + b1wt.B1t + b1wf.B1f;
            B2f = 'b2rf.B2f + b2wf.B2f + b2wt.B2t;
            B2t = 'b2rt.B2t + b2wt.B2t + b2wf.B2f;

            K1 = 'kr1.K1 + kw1.K1 + kw2.K2;
            K2 = 'kr2.K2 + kw2.K2 + kw1.K1;

            P1 = 'b1wt.P11;
            P11 = b2rf.P14 + b2rt.P12;
            P12 = kr1.P11 + kr2.'b1wf.P13;
            P13 = kr2.P13 + kr1.'b1wt.P11;
            P14 = enter.exit.'kw2.'b1wf.P1;

            P2 = 'b2wt.P21;
            P21 = b1rf.P24 + b1rt.P22;
            P22 = kr2.P21 + kr1.'b2wf.P23;
            P23 = kr1.P23 + kr2.'b2wt.P21;
            P24 = enter.exit.'kw1.'b2wf.P2;

            Pre-Dekker-2 = P1 | P2 | K1 | B1f | B2f;
            Dekker-2 = Pre-Dekker-2\{b1rf,b1rt,b1wf,b1wt,b2rf,b2rt,b2wf,b2wt,kr1,kr2,kw1,kw2};

            Spec = enter.exit.Spec;
        ";
    };
}

#[test]
fn orchard() {
    weak_bisim_test! {
        "Spec", "Orchard" => true in r"
            Man = 'shake.(redapple.walk.Man + greenapple.walk.Man);
            AppleTree = shake.('greenapple.AppleTree + 'redapple.AppleTree);
            Orchard = (AppleTree | Man) \ {shake, redapple, greenapple};
            Spec = walk.Spec;
        ";
    };
}
