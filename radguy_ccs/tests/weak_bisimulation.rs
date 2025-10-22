use radguy::kleene_local;
use radguy::oracle::SMax;
use radguy_ccs::systems::ccs::grammar::ProgramParser;
use radguy_ccs::systems::ccs::strong_bisimulation_system::BisimulationSystem;
use radguy_ccs::systems::ccs::transition_system::TransitionSystem;
use radguy_ccs::systems::ccs::weak_transition_system::WeakTransitionSystem;
use slotmap::DefaultKey;

macro_rules! bisim_test {
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
fn test_weak_bisimulation() {
    bisim_test! {
        "S", "T" => true in r"
            S = tau.S;
            T = 0;
        ";


        // "Buff3", "Spec" => true in r"
        //     Buff3 = (C0 | C1 | C2)\{c,d};
        //     C0 = Cell[c/b];
        //     C1 = Cell[c/a,d/b];
        //     C2 = Cell[d/a];
        //     Cell = a.'b.Cell;

        //     Spec = a.Spec';
        //     Spec' = 'b.Spec + a.Spec'';
        //     Spec'' = 'b.Spec' + a.'b.Spec'';
        // ";

        // "Dekker-2", "Spec" => true in r"
        //     B1f = 'b1rf.B1f + b1wf.B1f + b1wt.B1t;
        //     B1t = 'b1rt.B1t + b1wt.B1t + b1wf.B1f;
        //     B2f = 'b2rf.B2f + b2wf.B2f + b2wt.B2t;
        //     B2t = 'b2rt.B2t + b2wt.B2t + b2wf.B2f;

        //     K1 = 'kr1.K1 + kw1.K1 + kw2.K2;
        //     K2 = 'kr2.K2 + kw2.K2 + kw1.K1;

        //     P1 = 'b1wt.P11;
        //     P11 = b2rf.P14 + b2rt.P12;
        //     P12 = kr1.P11 + kr2.'b1wf.P13;
        //     P13 = kr2.P13 + kr1.'b1wt.P11;
        //     P14 = enter.exit.'kw2.'b1wf.P1;

        //     P2 = 'b2wt.P21;
        //     P21 = b1rf.P24 + b1rt.P22;
        //     P22 = kr2.P21 + kr1.'b2wf.P23;
        //     P23 = kr1.P23 + kr2.'b2wt.P21;
        //     P24 = enter.exit.'kw1.'b2wf.P2;

        //     Pre-Dekker-2 = P1 | P2 | K1 | B1f | B2f;
        //     Dekker-2 = Pre-Dekker-2\{b1rf,b1rt,b1wf,b1wt,b2rf,b2rt,b2wf,b2wt,kr1,kr2,kw1,kw2};

        //     Spec = enter.exit.Spec;
        // ";



        // "S", "T" => true in r"
        //     S = (b.0)[a/b];
        //     T = a.0;
        // ";

    //     // Strong bisimullation
    //     "S", "T" => true in r"
    //         S = a.b.S2;
    //         S2 = b.S2;

    //         T = a.T2;
    //         T2 = b.T2;
    //     ";
    //    "S", "T" => true in r"
    //         S = a.S1 + a.S2;
    //         S1 = a.S3 + b.S4;
    //         S2 = a.S4;
    //         S3 = a.S;
    //         S4 = a.S;

    //         T = a.T1 + a.T3;
    //         T1 = a.T2 + b.T2;
    //         T2 = a.T;
    //         T3 = a.T4;
    //         T4 = a.T;
    //     ";

    //     "P", "Q" => true in r"
    //         P = a.P1;
    //         P1 = b.P + c.P;

    //         Q = a.Q1;
    //         Q1 = b.Q2 + c.Q;
    //         Q2 = a.Q3;
    //         Q3 = b.Q + c.Q2;
    //     ";

    //     "S", "T" => false in r"
    //         S = a.S2;
    //         S2 = b.0 + c.0;

    //         T = a.T2 + a.T3;
    //         T2 = b.0;
    //         T3 = b.0;
    //     ";
    //     // Sync
    //     "S", "T" => true in r"
    //         S = a.0 | 'a.0;
    //         T = tau.0 + a.'a.0 + 'a.a.0;
    //     ";

    //     // Restriction
    //     "S", "T" => true in r"
    //         S = (a.0 | 'a.0) \ {a};
    //         T = tau.0;
    //     ";
    //     "S", "T" => false in r"
    //         S = (a.0 | 'a.0) \ {a};
    //         T = tau.0 + a.'a.0 + 'a.a.0;
    //     ";

    //     // Relabling
    //     "S", "T" => true in r"
    //         S = (a.0)[b/a];
    //         T = b.0;
    //     ";
    //      "S", "T" => false in r"
    //         S = (a.0)[b/a];
    //         T = a.0;
    //     ";
    };
}
