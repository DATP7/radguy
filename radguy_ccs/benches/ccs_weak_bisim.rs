use criterion::{Criterion, criterion_group, criterion_main};
use radguy::{
    kleene_local,
    oracle::LocalMaxR,
    ordered::{
        self,
        oracle::{CountOracle, StrategicLocalOracle, ToConstant},
        strategy::StrategyWeight,
    },
};
use radguy_ccs::systems::ccs::{
    bisimulation_system::BisimulationSystem, grammar::ProgramParser,
    transition_system::TransitionSystem, weak_transition_system::WeakTransitionSystem,
};
use slotmap::DefaultKey;

macro_rules! bisim_bench_suite {
    ($($name:ident: $left:expr, $right:expr => $eq:literal in $ccs:expr;)*) => {
        $(
        fn $name(c: &mut Criterion) {
            let parser = ProgramParser::new();
            let ast = parser
                .parse($ccs)
                .expect("Program should parse");
            let mut group = c.benchmark_group(stringify!($name));
            group.bench_function("unordered", |b| {
                b.iter_batched(
                    || {
                        let mut lts = WeakTransitionSystem::<DefaultKey>::default();
                        lts.load_ast(ast.clone());
                        BisimulationSystem::<DefaultKey, DefaultKey, DefaultKey, _>::new(lts)
                    },
                    |mut sys| {
                        let target = sys.specify_comparison($left, $right);
                        let result = !kleene_local(&sys, target, &LocalMaxR::default());
                        assert_eq!($eq, result, "{} and {} should{} be bisimilar in{}", $left, $right, if !$eq { " not" } else {""}, $ccs)
                    },
                    criterion::BatchSize::SmallInput,
                );
            });
            group.bench_function("ordered", |b|{
                    b.iter_batched(
                        || {
                            let mut lts = WeakTransitionSystem::<DefaultKey>::default();
                            lts.load_ast(ast.clone());
                            BisimulationSystem::<DefaultKey, DefaultKey, DefaultKey, _>::new(lts)
                        },
                        |mut sys| {
                            let target = sys.specify_comparison($left, $right);
                            let result = !ordered::kleene_local(&sys, target, &LocalMaxR::default().constant(StrategyWeight::Infinity).and_by(CountOracle, std::cmp::min));
                            assert_eq!($eq, result, "{} and {} should{} be bisimilar in{}", $left, $right, if !$eq { " not" } else {""}, $ccs)
                        },
                        criterion::BatchSize::SmallInput,
                    );
            });
        }
        )*
    };
}

bisim_bench_suite! {
    abp_ok: "SPEC", "ABP" => true in include_str!("../systems/ccs/abp_ok.ccs");
    abpl_ok: "SPEC", "ABPl" => true in include_str!("../systems/ccs/abp_ok.ccs");
    abpl_ok_2: "SPEC", "ABPl_2" => true in include_str!("../systems/ccs/abp_ok.ccs");
    abpl_bad_2: "SPEC", "ABPl_2" => false in include_str!("../systems/ccs/abp_bad.ccs");
    abpl_bad_3: "SPEC", "ABPl_3" => false in include_str!("../systems/ccs/abp_bad.ccs");
}

// TODO: Parameterize on size of leader election?
bisim_bench_suite! {
    leader_election_bad_6: "Spec", "Ring" => false in r"
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

        leader_election_ok_6: "Spec", "Ring" => true in r"
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
        dekker_mutual_exclusion: "Dekker-2", "Spec" => true in r"
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
}

criterion_group!(
    benches,
    abp_ok,
    abpl_ok,
    abpl_ok_2,
    abpl_bad_2,
    abpl_bad_3,
    leader_election_bad_6,
    leader_election_ok_6,
    dekker_mutual_exclusion
);
criterion_main!(benches);
