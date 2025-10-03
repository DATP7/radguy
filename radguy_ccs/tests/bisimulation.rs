use radguy::kleene_local;
use radguy::oracle::SMax;
use radguy_ccs::systems::ccs::grammar::ProgramParser;
use radguy_ccs::systems::ccs::strong_bisimulation_system::StrongBisimulationSystem;

macro_rules! bisim_test {
        ($($left:expr, $right:expr => $eq:literal in $ccs:expr;)*) => {
            $(
                {
                    let parser = ProgramParser::new();
                    let program_ast = parser
                        .parse(&$ccs)
                        .expect("Failed to parse CCS program content.");
                    let mut sys = StrongBisimulationSystem::default();
                    sys.load_ast(program_ast);
                    let start = sys.specify_comparison($left, $right);


                    let result = !kleene_local(&sys, start, &SMax);
                    assert_eq!($eq, result, "processes should{} be bisimilar", if !$eq { " not" } else {""});
                }
            )*
        };
    }

#[test]
fn test_strong_bisimulation() {
    bisim_test! {
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
