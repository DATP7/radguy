use radguy::kleene_local;
use radguy::oracle::SMax;
use radguy_ccs::systems::ccs::bisimulation_system::BisimulationSystem;
use radguy_ccs::systems::ccs::grammar::ProgramParser;
use radguy_ccs::systems::ccs::strong_transition_system::StrongTransitionSystem;
use radguy_ccs::systems::ccs::transition_system::TransitionSystem;
use slotmap::DefaultKey;

macro_rules! strong_bisim_test {
        ($($left:expr, $right:expr => $eq:literal in $ccs:expr;)*) => {
            $(
                {
                    let parser = ProgramParser::new();
                    let program_ast = parser
                        .parse(&$ccs)
                        .expect("Failed to parse CCS program content.");
                    let mut strong_transition_system = StrongTransitionSystem::<DefaultKey>::default();
                    strong_transition_system.load_ast(program_ast);

                    let mut sys = BisimulationSystem::<DefaultKey, DefaultKey, DefaultKey, StrongTransitionSystem<DefaultKey>>::new(strong_transition_system);
                    let start = sys.specify_comparison($left, $right);


                    let oracle = SMax::default();
                    let result = !kleene_local(&sys, start, &oracle);
                    assert_eq!($eq, result, "{} and {} should{} be bisimilar in{}", $left, $right, if !$eq { " not" } else {""}, $ccs);
                }
            )*
        };
    }

#[test]
fn strong_bisimulation() {
    strong_bisim_test! {
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
            S = (a.0 | b.0)\{a};
            T = a.0 + b.0;
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
        "S", "T" => true in r"
            S = (a.b.c.0)[b/a][c/b];
            T = c.c.c.0;
        ";

        "S", "S" => true in r"
            S = a.b.0 | a.c.0 | b.c.0;
        ";
    };
}

#[test]
fn relabelling_preserved() {
    strong_bisim_test! {
        "S", "T" => true in r"
            S = (a.a.a.0)[b/a];
            T = b.b.b.0;
        ";
    };
}

#[test]
fn restriction_preserved() {
    strong_bisim_test! {
        "S", "T" => true in r"
            S = (a.a.a.0 | b.0) \ {b};
            T = a.a.a.0;
        ";
    };
}

#[test]
fn strong_bisimulation_large_protocol() {
    strong_bisim_test! {
        // Big
        "Protocol", "ZProtocol" => true in r"
        Send0 = acc.Sending0;
        Sending0 = 'left0.Sending0 + leftAck0.Send1 + leftAck1.Sending0;
        Send1 = acc.Sending1;
        Sending1 = 'left1.Sending1 + leftAck1.Send0 + leftAck0.Sending1;
        
        Received0 = 'del.RecvAck1;
        Received1 = 'del.RecvAck0;
        RecvAck0 = right0.Received0 + right1.RecvAck0 + 'rightAck1.RecvAck0;
        RecvAck1 = right1.Received1 + right0.RecvAck1 + 'rightAck0.RecvAck1;
        
        Med = MedTop | MedBot;
        MedBot = left0.MedBotRep0 + left1.MedBotRep1;
        MedBotRep0 = 'right0.MedBotRep0 + tau.MedBot;
        MedBotRep1 = 'right1.MedBotRep1 + tau.MedBot;
        MedTop = rightAck0.MedTopRep0 + rightAck1.MedTopRep1;
        MedTopRep0 = 'leftAck0.MedTopRep0 + tau.MedTop;
        MedTopRep1 = 'leftAck1.MedTopRep1 + tau.MedTop;
        
        ZSend0 = acc.ZSending0;
        ZSending0 = 'left0.ZSending0 + leftAck0.ZSend1 + leftAck1.ZSending0;
        ZSend1 = acc.ZSending1;
        ZSending1 = 'left1.ZSending1 + leftAck1.ZSend0 + leftAck0.ZSending1;
        
        ZReceived0 = 'del.ZRecvAck1;
        ZReceived1 = 'del.ZRecvAck0;
        ZRecvAck0 = right0.ZReceived0 + right1.ZRecvAck0 + 'rightAck1.ZRecvAck0;
        ZRecvAck1 = right1.ZReceived1 + right0.ZRecvAck1 + 'rightAck0.ZRecvAck1;
        
        ZMed = ZMedTop | ZMedBot;
        ZMedBot = left0.ZMedBotRep0 + left1.ZMedBotRep1;
        ZMedBotRep0 = 'right0.ZMedBotRep0 + tau.ZMedBot;
        ZMedBotRep1 = 'right1.ZMedBotRep1 + tau.ZMedBot;
        ZMedTop = rightAck0.ZMedTopRep0 + rightAck1.ZMedTopRep1;
        ZMedTopRep0 = 'leftAck0.ZMedTopRep0 + tau.ZMedTop;
        ZMedTopRep1 = 'leftAck1.ZMedTopRep1 + tau.ZMedTop;
        
        Protocol = (Send0 | Med | RecvAck0) \ {left0, left1, right0, right1, leftAck0, leftAck1, rightAck0, rightAck1};
        ZProtocol = (ZSend0 | ZMed | ZRecvAck0) \ {left0, left1, right0, right1, leftAck0, leftAck1, rightAck0, rightAck1};
        ";
    }
}
