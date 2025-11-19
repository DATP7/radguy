use radguy::kleene_local;
use radguy::oracle::SMax;
use radguy_ccs::systems::ccs::bisimulation_system::BisimulationSystem;
use radguy_ccs::systems::ccs::grammar::ProgramParser;
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

                    let result = !kleene_local(&mut sys, start, &SMax::default());
                    assert_eq!($eq, result, "{} and {} should{} be bisimilar in{}", $left, $right, if !$eq { " not" } else {""}, $ccs);
                }
            )*
        };
    }

#[test]
fn abp_ok_small() {
    let ccs = include_str!("../systems/ccs/abp_ok.ccs");
    weak_bisim_test! {
        "SPEC", "ABP" => true in ccs;
    };
}

#[test]
fn abpl_ok_small() {
    let ccs = include_str!("../systems/ccs/abp_ok.ccs");
    weak_bisim_test! {
        "SPEC", "ABPl" => true in ccs;
        "SPEC", "ABPl_2" => true in ccs;
    };
}

#[test]
fn abp_bad_small() {
    let ccs = include_str!("../systems/ccs/abp_bad.ccs");
    weak_bisim_test! {
        "SPEC", "ABP" => true in ccs;
    };
}

#[test]
fn abpl_bad_small() {
    let ccs = include_str!("../systems/ccs/abp_bad.ccs");
    weak_bisim_test! {
        "SPEC", "ABPl_2" => false in ccs;
        "SPEC", "ABPl_3" => false in ccs;
    };
}

#[test]
fn simple_infinite_tau_loop() {
    weak_bisim_test! {
        "S", "T" => true in r"
            S = tau.S;
            T = 0;
        ";
    };
}

#[test]
fn dual_tau_loop() {
    weak_bisim_test! {
        "A", "B" => true in r"
            A = tau.B + a.0;
            B = tau.A + b.0;
            Spec = a.0 + b.0;
        ";
    };
}

#[test]
fn tau_prefix() {
    weak_bisim_test! {
        "S", "T" => false in r"
            S = tau.(a.0 + b.0);
            T = tau.a.0 + tau.b.0;
        ";
    }
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

#[test]
fn leader_election_bad_6() {
    weak_bisim_test! {
        "Spec", "Ring" => false in r"
            P1 = 'm6r1.P1 + m1r1.leader.0 + m1r2.P1_2 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6;
            P1_2 = 'm6r2.P1_2 + m1r1.leader.0 + m1r2.P1_2 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6;
            P1_3 = 'm6r3.P1_3 + m1r1.leader.0 + m1r2.P1_3 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6;
            P1_4 = 'm6r4.P1_4 + m1r1.leader.0 + m1r2.P1_4 + m1r3.P1_4 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6;
            P1_5 = 'm6r5.P1_5 + m1r1.leader.0 + m1r2.P1_5 + m1r3.P1_5 + m1r4.P1_5 + m1r5.P1_5 + m1r6.P1_6;
            P1_6 = 'm6r6.P1_6 + m1r1.leader.0 + m1r2.P1_6 + m1r3.P1_6 + m1r4.P1_6 + m1r5.P1_6 + m1r6.P1_6;

            P2 = 'm1r2.P2 + m2r1.P2 + m2r2.leader.0 + m2r3.P2_3 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6;
            P2_3 = 'm1r3.P2_3 + m2r2.leader.0 + m2r1.P2_3 + m2r3.P2_3 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6;
            P2_4 = 'm1r4.P2_4 + m2r2.leader.0 + m2r1.P2_4 + m2r3.P2_4 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6;
            P2_5 = 'm1r5.P2_5 + m2r2.leader.0 + m2r1.P2_5 + m2r3.P2_5 + m2r4.P2_5 + m2r5.P2_5 + m2r6.P2_6;
            P2_6 = 'm1r6.P2_6 + m2r2.leader.0 + m2r1.P2_6 + m2r3.P2_6 + m2r4.P2_6 + m2r5.P2_6 + m2r6.P2_6;

            P3 = 'm2r3.P3 + m3r1.P3 + m3r2.P3 + m3r3.leader.0 + m3r4.P3_4 + m3r5.P3_5 + m3r6.P3_6;
            P3_4 = 'm2r4.P3_4 + m3r3.leader.0 + m3r1.P3_4 + m3r2.P3_4 + m3r4.P3_4 + m3r5.P3_5 + m3r6.P3_6;
            P3_5 = 'm2r5.P3_5 + m3r3.leader.0 + m3r1.P3_5 + m3r2.P3_5 + m3r4.P3_5 + m3r5.P3_5 + m3r6.P3_6;
            P3_6 = 'm2r6.P3_6 + m3r3.leader.0 + m3r1.P3_6 + m3r2.P3_6 + m3r4.P3_6 + m3r5.P3_6 + m3r6.P3_6;

            P4 = 'm3r4.P4 + m4r1.P4 + m4r2.P4 + m4r3.P4 + m4r4.leader.0 + m4r5.P4_5 + m4r6.P4_6;
            P4_5 = 'm3r5.P4_5 + m4r4.leader.0 + m4r1.P4_5 + m4r2.P4_5 + m4r3.P4_5 + m4r5.P4_5 + m4r6.P4_6;
            P4_6 = 'm3r6.P4_6 + m4r4.leader.0 + m4r1.P4_6 + m4r2.P4_6 + m4r3.P4_6 + m4r5.P4_6 + m4r6.P4_6;

            P5 = 'm4r5.P5 + m5r1.P5 + m5r2.P5 + m5r3.P5 + m5r4.P5 + m5r5.leader.0 + m5r6.P5_6;
            P5_6 = 'm4r6.P5_6 + m5r5.leader.0 + m5r1.P5_6 + m5r2.P5_6 + m5r3.P5_6 + m5r4.P5_6 + m5r6.leader.0;

            P6 = 'm5r6.P6 + m6r1.P6 + m6r2.P6 + m6r3.P6 + m6r4.P6 + m6r5.P6 + m6r6.leader.0;

            Ring = (P1 | P2 | P3 | P4 | P5 | P6)
                    \ {m1r1, m1r2, m1r3, m1r4, m1r5, m1r6, m2r1, m2r2, m2r3, m2r4, m2r5, m2r6, m3r1, m3r2, m3r3, m3r4, m3r5, m3r6, m4r1, m4r2, m4r3, m4r4, m4r5, m4r6, m5r1, m5r2, m5r3, m5r4, m5r5, m5r6, m6r1, m6r2, m6r3, m6r4, m6r5, m6r6};

            Spec = leader.0;
        ";
    };
}

#[test]
fn leader_election_ok_6() {
    weak_bisim_test! {
        "Spec", "Ring" => true in r"
            P1 = 'm6r1.P1 + m1r1.leader.0 + m1r2.P1_2 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6;
            P1_2 = 'm6r2.P1_2 + m1r1.leader.0 + m1r2.P1_2 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6;
            P1_3 = 'm6r3.P1_3 + m1r1.leader.0 + m1r2.P1_3 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6;
            P1_4 = 'm6r4.P1_4 + m1r1.leader.0 + m1r2.P1_4 + m1r3.P1_4 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6;
            P1_5 = 'm6r5.P1_5 + m1r1.leader.0 + m1r2.P1_5 + m1r3.P1_5 + m1r4.P1_5 + m1r5.P1_5 + m1r6.P1_6;
            P1_6 = 'm6r6.P1_6 + m1r1.leader.0 + m1r2.P1_6 + m1r3.P1_6 + m1r4.P1_6 + m1r5.P1_6 + m1r6.P1_6;

            P2 = 'm1r2.P2 + m2r1.P2 + m2r2.leader.0 + m2r3.P2_3 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6;
            P2_3 = 'm1r3.P2_3 + m2r2.leader.0 + m2r1.P2_3 + m2r3.P2_3 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6;
            P2_4 = 'm1r4.P2_4 + m2r2.leader.0 + m2r1.P2_4 + m2r3.P2_4 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6;
            P2_5 = 'm1r5.P2_5 + m2r2.leader.0 + m2r1.P2_5 + m2r3.P2_5 + m2r4.P2_5 + m2r5.P2_5 + m2r6.P2_6;
            P2_6 = 'm1r6.P2_6 + m2r2.leader.0 + m2r1.P2_6 + m2r3.P2_6 + m2r4.P2_6 + m2r5.P2_6 + m2r6.P2_6;

            P3 = 'm2r3.P3 + m3r1.P3 + m3r2.P3 + m3r3.leader.0 + m3r4.P3_4 + m3r5.P3_5 + m3r6.P3_6;
            P3_4 = 'm2r4.P3_4 + m3r3.leader.0 + m3r1.P3_4 + m3r2.P3_4 + m3r4.P3_4 + m3r5.P3_5 + m3r6.P3_6;
            P3_5 = 'm2r5.P3_5 + m3r3.leader.0 + m3r1.P3_5 + m3r2.P3_5 + m3r4.P3_5 + m3r5.P3_5 + m3r6.P3_6;
            P3_6 = 'm2r6.P3_6 + m3r3.leader.0 + m3r1.P3_6 + m3r2.P3_6 + m3r4.P3_6 + m3r5.P3_6 + m3r6.P3_6;

            P4 = 'm3r4.P4 + m4r1.P4 + m4r2.P4 + m4r3.P4 + m4r4.leader.0 + m4r5.P4_5 + m4r6.P4_6;
            P4_5 = 'm3r5.P4_5 + m4r4.leader.0 + m4r1.P4_5 + m4r2.P4_5 + m4r3.P4_5 + m4r5.P4_5 + m4r6.P4_6;
            P4_6 = 'm3r6.P4_6 + m4r4.leader.0 + m4r1.P4_6 + m4r2.P4_6 + m4r3.P4_6 + m4r5.P4_6 + m4r6.P4_6;

            P5 = 'm4r5.P5 + m5r1.P5 + m5r2.P5 + m5r3.P5 + m5r4.P5 + m5r5.leader.0 + m5r6.P5_6;
            P5_6 = 'm4r6.P5_6 + m5r5.leader.0 + m5r1.P5_6 + m5r2.P5_6 + m5r3.P5_6 + m5r4.P5_6 + m5r6.P5_6;

            P6 = 'm5r6.P6 + m6r1.P6 + m6r2.P6 + m6r3.P6 + m6r4.P6 + m6r5.P6 + m6r6.leader.0;

            Ring = (P1 | P2 | P3 | P4 | P5 | P6) \ {m1r1, m1r2, m1r3, m1r4, m1r5, m1r6, m2r1, m2r2, m2r3, m2r4, m2r5, m2r6, m3r1, m3r2, m3r3, m3r4, m3r5, m3r6, m4r1, m4r2, m4r3, m4r4, m4r5, m4r6, m5r1, m5r2, m5r3, m5r4, m5r5, m5r6, m6r1, m6r2, m6r3, m6r4, m6r5, m6r6};

            Spec = leader.0;
        ";
    };
}

#[ignore = "performance too bad for ci"]
#[test]
fn leader_election_ok_8() {
    weak_bisim_test! {
        "Spec", "Ring" => true in r"
            P1 = 'm8r1.P1 + m1r1.leader.0 + m1r2.P1_2 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_2 = 'm8r2.P1_2 + m1r1.leader.0 + m1r2.P1_2 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_3 = 'm8r3.P1_3 + m1r1.leader.0 + m1r2.P1_3 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_4 = 'm8r4.P1_4 + m1r1.leader.0 + m1r2.P1_4 + m1r3.P1_4 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_5 = 'm8r5.P1_5 + m1r1.leader.0 + m1r2.P1_5 + m1r3.P1_5 + m1r4.P1_5 + m1r5.P1_5 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_6 = 'm8r6.P1_6 + m1r1.leader.0 + m1r2.P1_6 + m1r3.P1_6 + m1r4.P1_6 + m1r5.P1_6 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_7 = 'm8r7.P1_7 + m1r1.leader.0 + m1r2.P1_7 + m1r3.P1_7 + m1r4.P1_7 + m1r5.P1_7 + m1r6.P1_7 + m1r7.P1_7 + m1r8.P1_8;
            P1_8 = 'm8r8.P1_8 + m1r1.leader.0 + m1r2.P1_8 + m1r3.P1_8 + m1r4.P1_8 + m1r5.P1_8 + m1r6.P1_8 + m1r7.P1_8 + m1r8.P1_8;

            P2 = 'm1r2.P2 + m2r1.P2 + m2r2.leader.0 + m2r3.P2_3 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6 + m2r7.P2_7 + m2r8.P2_8;
            P2_3 = 'm1r3.P2_3 + m2r2.leader.0 + m2r1.P2_3 + m2r3.P2_3 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6 + m2r7.P2_7 + m2r8.P2_8;
            P2_4 = 'm1r4.P2_4 + m2r2.leader.0 + m2r1.P2_4 + m2r3.P2_4 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6 + m2r7.P2_7 + m2r8.P2_8;
            P2_5 = 'm1r5.P2_5 + m2r2.leader.0 + m2r1.P2_5 + m2r3.P2_5 + m2r4.P2_5 + m2r5.P2_5 + m2r6.P2_6 + m2r7.P2_7 + m2r8.P2_8;
            P2_6 = 'm1r6.P2_6 + m2r2.leader.0 + m2r1.P2_6 + m2r3.P2_6 + m2r4.P2_6 + m2r5.P2_6 + m2r6.P2_6 + m2r7.P2_7 + m2r8.P2_8;
            P2_7 = 'm1r7.P2_7 + m2r2.leader.0 + m2r1.P2_7 + m2r3.P2_7 + m2r4.P2_7 + m2r5.P2_7 + m2r6.P2_7 + m2r7.P2_7 + m2r8.P2_8;
            P2_8 = 'm1r8.P2_8 + m2r2.leader.0 + m2r1.P2_8 + m2r3.P2_8 + m2r4.P2_8 + m2r5.P2_8 + m2r6.P2_8 + m2r7.P2_8 + m2r8.P2_8;

            P3 = 'm2r3.P3 + m3r1.P3 + m3r2.P3 + m3r3.leader.0 + m3r4.P3_4 + m3r5.P3_5 + m3r6.P3_6 + m3r7.P3_7 + m3r8.P3_8;
            P3_4 = 'm2r4.P3_4 + m3r3.leader.0 + m3r1.P3_4 + m3r2.P3_4 + m3r4.P3_4 + m3r5.P3_5 + m3r6.P3_6 + m3r7.P3_7 + m3r8.P3_8;
            P3_5 = 'm2r5.P3_5 + m3r3.leader.0 + m3r1.P3_5 + m3r2.P3_5 + m3r4.P3_5 + m3r5.P3_5 + m3r6.P3_6 + m3r7.P3_7 + m3r8.P3_8;
            P3_6 = 'm2r6.P3_6 + m3r3.leader.0 + m3r1.P3_6 + m3r2.P3_6 + m3r4.P3_6 + m3r5.P3_6 + m3r6.P3_6 + m3r7.P3_7 + m3r8.P3_8;
            P3_7 = 'm2r7.P3_7 + m3r3.leader.0 + m3r1.P3_7 + m3r2.P3_7 + m3r4.P3_7 + m3r5.P3_7 + m3r6.P3_7 + m3r7.P3_7 + m3r8.P3_8;
            P3_8 = 'm2r8.P3_8 + m3r3.leader.0 + m3r1.P3_8 + m3r2.P3_8 + m3r4.P3_8 + m3r5.P3_8 + m3r6.P3_8 + m3r7.P3_8 + m3r8.P3_8;

            P4 = 'm3r4.P4 + m4r1.P4 + m4r2.P4 + m4r3.P4 + m4r4.leader.0 + m4r5.P4_5 + m4r6.P4_6 + m4r7.P4_7 + m4r8.P4_8;
            P4_5 = 'm3r5.P4_5 + m4r4.leader.0 + m4r1.P4_5 + m4r2.P4_5 + m4r3.P4_5 + m4r5.P4_5 + m4r6.P4_6 + m4r7.P4_7 + m4r8.P4_8;
            P4_6 = 'm3r6.P4_6 + m4r4.leader.0 + m4r1.P4_6 + m4r2.P4_6 + m4r3.P4_6 + m4r5.P4_6 + m4r6.P4_6 + m4r7.P4_7 + m4r8.P4_8;
            P4_7 = 'm3r7.P4_7 + m4r4.leader.0 + m4r1.P4_7 + m4r2.P4_7 + m4r3.P4_7 + m4r5.P4_7 + m4r6.P4_7 + m4r7.P4_7 + m4r8.P4_8;
            P4_8 = 'm3r8.P4_8 + m4r4.leader.0 + m4r1.P4_8 + m4r2.P4_8 + m4r3.P4_8 + m4r5.P4_8 + m4r6.P4_8 + m4r7.P4_8 + m4r8.P4_8;

            P5 = 'm4r5.P5 + m5r1.P5 + m5r2.P5 + m5r3.P5 + m5r4.P5 + m5r5.leader.0 + m5r6.P5_6 + m5r7.P5_7 + m5r8.P5_8;
            P5_6 = 'm4r6.P5_6 + m5r5.leader.0 + m5r1.P5_6 + m5r2.P5_6 + m5r3.P5_6 + m5r4.P5_6 + m5r6.P5_6 + m5r7.P5_7 + m5r8.P5_8;
            P5_7 = 'm4r7.P5_7 + m5r5.leader.0 + m5r1.P5_7 + m5r2.P5_7 + m5r3.P5_7 + m5r4.P5_7 + m5r6.P5_7 + m5r7.P5_7 + m5r8.P5_8;
            P5_8 = 'm4r8.P5_8 + m5r5.leader.0 + m5r1.P5_8 + m5r2.P5_8 + m5r3.P5_8 + m5r4.P5_8 + m5r6.P5_8 + m5r7.P5_8 + m5r8.P5_8;

            P6 = 'm5r6.P6 + m6r1.P6 + m6r2.P6 + m6r3.P6 + m6r4.P6 + m6r5.P6 + m6r6.leader.0 + m6r7.P6_7 + m6r8.P6_8;
            P6_7 = 'm5r7.P6_7 + m6r6.leader.0 + m6r1.P6_7 + m6r2.P6_7 + m6r3.P6_7 + m6r4.P6_7 + m6r5.P6_7 + m6r7.P6_7 + m6r8.P6_8;
            P6_8 = 'm5r8.P6_8 + m6r6.leader.0 + m6r1.P6_8 + m6r2.P6_8 + m6r3.P6_8 + m6r4.P6_8 + m6r5.P6_8 + m6r7.P6_8 + m6r8.P6_8;

            P7 = 'm6r7.P7 + m7r1.P7 + m7r2.P7 + m7r3.P7 + m7r4.P7 + m7r5.P7 + m7r6.P7 + m7r7.leader.0 + m7r8.P7_8;
            P7_8 = 'm6r8.P7_8 + m7r7.leader.0 + m7r1.P7_8 + m7r2.P7_8 + m7r3.P7_8 + m7r4.P7_8 + m7r5.P7_8 + m7r6.P7_8 + m7r8.P7_8;

            P8 = 'm7r8.P8 + m8r1.P8 + m8r2.P8 + m8r3.P8 + m8r4.P8 + m8r5.P8 + m8r6.P8 + m8r7.P8 + m8r8.leader.0;

            Ring = (P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8)
                \ {m1r1, m1r2, m1r3, m1r4, m1r5, m1r6, m1r7, m1r8, m2r1, m2r2, m2r3, m2r4, m2r5, m2r6, m2r7, m2r8, m3r1, m3r2, m3r3, m3r4, m3r5, m3r6, m3r7, m3r8, m4r1, m4r2, m4r3, m4r4, m4r5, m4r6, m4r7, m4r8, m5r1, m5r2, m5r3, m5r4, m5r5, m5r6, m5r7, m5r8, m6r1, m6r2, m6r3, m6r4, m6r5, m6r6, m6r7, m6r8, m7r1, m7r2, m7r3, m7r4, m7r5, m7r6, m7r7, m7r8, m8r1, m8r2, m8r3, m8r4, m8r5, m8r6, m8r7, m8r8};

            Spec = leader.0;
        ";
    };
}

#[ignore = "performance too bad for ci"]
#[test]
fn leader_election_bad_8() {
    weak_bisim_test! {
        "Spec", "Ring" => false in r"
            P1 = 'm8r1.P1 + m1r1.leader.0 + m1r2.P1_2 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_2 = 'm8r2.P1_2 + m1r1.leader.0 + m1r2.P1_2 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_3 = 'm8r3.P1_3 + m1r1.leader.0 + m1r2.P1_3 + m1r3.P1_3 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_4 = 'm8r4.P1_4 + m1r1.leader.0 + m1r2.P1_4 + m1r3.P1_4 + m1r4.P1_4 + m1r5.P1_5 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_5 = 'm8r5.P1_5 + m1r1.leader.0 + m1r2.P1_5 + m1r3.P1_5 + m1r4.P1_5 + m1r5.P1_5 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_6 = 'm8r6.P1_6 + m1r1.leader.0 + m1r2.P1_6 + m1r3.P1_6 + m1r4.P1_6 + m1r5.P1_6 + m1r6.P1_6 + m1r7.P1_7 + m1r8.P1_8;
            P1_7 = 'm8r7.P1_7 + m1r1.leader.0 + m1r2.P1_7 + m1r3.P1_7 + m1r4.P1_7 + m1r5.P1_7 + m1r6.P1_7 + m1r7.P1_7 + m1r8.P1_8;
            P1_8 = 'm8r8.P1_8 + m1r1.leader.0 + m1r2.P1_8 + m1r3.P1_8 + m1r4.P1_8 + m1r5.P1_8 + m1r6.P1_8 + m1r7.P1_8 + m1r8.P1_8;

            P2 = 'm1r2.P2 + m2r1.P2 + m2r2.leader.0 + m2r3.P2_3 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6 + m2r7.P2_7 + m2r8.P2_8;
            P2_3 = 'm1r3.P2_3 + m2r2.leader.0 + m2r1.P2_3 + m2r3.P2_3 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6 + m2r7.P2_7 + m2r8.P2_8;
            P2_4 = 'm1r4.P2_4 + m2r2.leader.0 + m2r1.P2_4 + m2r3.P2_4 + m2r4.P2_4 + m2r5.P2_5 + m2r6.P2_6 + m2r7.P2_7 + m2r8.P2_8;
            P2_5 = 'm1r5.P2_5 + m2r2.leader.0 + m2r1.P2_5 + m2r3.P2_5 + m2r4.P2_5 + m2r5.P2_5 + m2r6.P2_6 + m2r7.P2_7 + m2r8.P2_8;
            P2_6 = 'm1r6.P2_6 + m2r2.leader.0 + m2r1.P2_6 + m2r3.P2_6 + m2r4.P2_6 + m2r5.P2_6 + m2r6.P2_6 + m2r7.P2_7 + m2r8.P2_8;
            P2_7 = 'm1r7.P2_7 + m2r2.leader.0 + m2r1.P2_7 + m2r3.P2_7 + m2r4.P2_7 + m2r5.P2_7 + m2r6.P2_7 + m2r7.P2_7 + m2r8.P2_8;
            P2_8 = 'm1r8.P2_8 + m2r2.leader.0 + m2r1.P2_8 + m2r3.P2_8 + m2r4.P2_8 + m2r5.P2_8 + m2r6.P2_8 + m2r7.P2_8 + m2r8.P2_8;

            P3 = 'm2r3.P3 + m3r1.P3 + m3r2.P3 + m3r3.leader.0 + m3r4.P3_4 + m3r5.P3_5 + m3r6.P3_6 + m3r7.P3_7 + m3r8.P3_8;
            P3_4 = 'm2r4.P3_4 + m3r3.leader.0 + m3r1.P3_4 + m3r2.P3_4 + m3r4.P3_4 + m3r5.P3_5 + m3r6.P3_6 + m3r7.P3_7 + m3r8.P3_8;
            P3_5 = 'm2r5.P3_5 + m3r3.leader.0 + m3r1.P3_5 + m3r2.P3_5 + m3r4.P3_5 + m3r5.P3_5 + m3r6.P3_6 + m3r7.P3_7 + m3r8.P3_8;
            P3_6 = 'm2r6.P3_6 + m3r3.leader.0 + m3r1.P3_6 + m3r2.P3_6 + m3r4.P3_6 + m3r5.P3_6 + m3r6.P3_6 + m3r7.P3_7 + m3r8.P3_8;
            P3_7 = 'm2r7.P3_7 + m3r3.leader.0 + m3r1.P3_7 + m3r2.P3_7 + m3r4.P3_7 + m3r5.P3_7 + m3r6.P3_7 + m3r7.P3_7 + m3r8.P3_8;
            P3_8 = 'm2r8.P3_8 + m3r3.leader.0 + m3r1.P3_8 + m3r2.P3_8 + m3r4.P3_8 + m3r5.P3_8 + m3r6.P3_8 + m3r7.P3_8 + m3r8.P3_8;

            P4 = 'm3r4.P4 + m4r1.P4 + m4r2.P4 + m4r3.P4 + m4r4.leader.0 + m4r5.P4_5 + m4r6.P4_6 + m4r7.P4_7 + m4r8.P4_8;
            P4_5 = 'm3r5.P4_5 + m4r4.leader.0 + m4r1.P4_5 + m4r2.P4_5 + m4r3.P4_5 + m4r5.P4_5 + m4r6.P4_6 + m4r7.P4_7 + m4r8.P4_8;
            P4_6 = 'm3r6.P4_6 + m4r4.leader.0 + m4r1.P4_6 + m4r2.P4_6 + m4r3.P4_6 + m4r5.P4_6 + m4r6.P4_6 + m4r7.P4_7 + m4r8.P4_8;
            P4_7 = 'm3r7.P4_7 + m4r4.leader.0 + m4r1.P4_7 + m4r2.P4_7 + m4r3.P4_7 + m4r5.P4_7 + m4r6.P4_7 + m4r7.P4_7 + m4r8.P4_8;
            P4_8 = 'm3r8.P4_8 + m4r4.leader.0 + m4r1.P4_8 + m4r2.P4_8 + m4r3.P4_8 + m4r5.P4_8 + m4r6.P4_8 + m4r7.P4_8 + m4r8.P4_8;

            P5 = 'm4r5.P5 + m5r1.P5 + m5r2.P5 + m5r3.P5 + m5r4.P5 + m5r5.leader.0 + m5r6.P5_6 + m5r7.P5_7 + m5r8.P5_8;
            P5_6 = 'm4r6.P5_6 + m5r5.leader.0 + m5r1.P5_6 + m5r2.P5_6 + m5r3.P5_6 + m5r4.P5_6 + m5r6.P5_6 + m5r7.P5_7 + m5r8.P5_8;
            P5_7 = 'm4r7.P5_7 + m5r5.leader.0 + m5r1.P5_7 + m5r2.P5_7 + m5r3.P5_7 + m5r4.P5_7 + m5r6.P5_7 + m5r7.P5_7 + m5r8.P5_8;
            P5_8 = 'm4r8.P5_8 + m5r5.leader.0 + m5r1.P5_8 + m5r2.P5_8 + m5r3.P5_8 + m5r4.P5_8 + m5r6.P5_8 + m5r7.P5_8 + m5r8.P5_8;

            P6 = 'm5r6.P6 + m6r1.P6 + m6r2.P6 + m6r3.P6 + m6r4.P6 + m6r5.P6 + m6r6.leader.0 + m6r7.P6_7 + m6r8.P6_8;
            P6_7 = 'm5r7.P6_7 + m6r6.leader.0 + m6r1.P6_7 + m6r2.P6_7 + m6r3.P6_7 + m6r4.P6_7 + m6r5.P6_7 + m6r7.P6_7 + m6r8.P6_8;
            P6_8 = 'm5r8.P6_8 + m6r6.leader.0 + m6r1.P6_8 + m6r2.P6_8 + m6r3.P6_8 + m6r4.P6_8 + m6r5.P6_8 + m6r7.P6_8 + m6r8.P6_8;

            P7 = 'm6r7.P7 + m7r1.P7 + m7r2.P7 + m7r3.P7 + m7r4.P7 + m7r5.P7 + m7r6.P7 + m7r7.leader.0 + m7r8.P7_8;
            P7_8 = 'm6r8.P7_8 + m7r7.leader.0 + m7r1.P7_8 + m7r2.P7_8 + m7r3.P7_8 + m7r4.P7_8 + m7r5.P7_8 + m7r6.P7_8 + m7r8.leader.0;

            P8 = 'm7r8.P8 + m8r1.P8 + m8r2.P8 + m8r3.P8 + m8r4.P8 + m8r5.P8 + m8r6.P8 + m8r7.P8 + m8r8.leader.0;

            Ring = (P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8)
                \ {m1r1, m1r2, m1r3, m1r4, m1r5, m1r6, m1r7, m1r8, m2r1, m2r2, m2r3, m2r4, m2r5, m2r6, m2r7, m2r8, m3r1, m3r2, m3r3, m3r4, m3r5, m3r6, m3r7, m3r8, m4r1, m4r2, m4r3, m4r4, m4r5, m4r6, m4r7, m4r8, m5r1, m5r2, m5r3, m5r4, m5r5, m5r6, m5r7, m5r8, m6r1, m6r2, m6r3, m6r4, m6r5, m6r6, m6r7, m6r8, m7r1, m7r2, m7r3, m7r4, m7r5, m7r6, m7r7, m7r8, m8r1, m8r2, m8r3, m8r4, m8r5, m8r6, m8r7, m8r8};

            Spec = leader.0;
        ";
    };
}
