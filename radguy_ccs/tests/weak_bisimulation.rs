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

        "S", "T" => true in r"
            S = (b.0)[a/b];
            T = a.0;
        ";

        // Strong bisimullation
        "S", "T" => true in r"
            S = a.b.S2;
            S2 = b.S2;

            T = a.T2;
            T2 = b.T2;
        ";
       "S", "T" => true in r"
            S = a.S1 + a.S2;
            S1 = a.S3 + b.S4;
            S2 = a.S4;
            S3 = a.S;
            S4 = a.S;

            T = a.T1 + a.T3;
            T1 = a.T2 + b.T2;
            T2 = a.T;
            T3 = a.T4;
            T4 = a.T;
        ";

        "P", "Q" => true in r"
            P = a.P1;
            P1 = b.P + c.P;

            Q = a.Q1;
            Q1 = b.Q2 + c.Q;
            Q2 = a.Q3;
            Q3 = b.Q + c.Q2;
        ";

        "S", "T" => false in r"
            S = a.S2;
            S2 = b.0 + c.0;

            T = a.T2 + a.T3;
            T2 = b.0;
            T3 = b.0;
        ";
        // Sync
        "S", "T" => true in r"
            S = a.0 | 'a.0;
            T = tau.0 + a.'a.0 + 'a.a.0;
        ";

        // Restriction
        "S", "T" => true in r"
            S = (a.0 | 'a.0) \ {a};
            T = tau.0;
        ";
        "S", "T" => false in r"
            S = (a.0 | 'a.0) \ {a};
            T = tau.0 + a.'a.0 + 'a.a.0;
        ";

        // Relabling
        "S", "T" => true in r"
            S = (a.0)[b/a];
            T = b.0;
        ";
         "S", "T" => false in r"
            S = (a.0)[b/a];
            T = a.0;
        ";
    };
}
