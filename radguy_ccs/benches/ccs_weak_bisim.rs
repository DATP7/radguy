use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use orx_priority_queue::DaryHeapWithMap;
use radguy::{
    extension::LocalExtension,
    kleene_local,
    oracle::{ArgumentsOracle, LocalMaxR, LocalOracle, SMax},
    ordered::{
        self,
        oracle::{
            CountOracle, InverseCountOracle, SiblingsOracle, StrategicArgumentsOracle,
            StrategicHeightOracle, StrategicLocalOracle, ToConstant,
        },
        strategy::{BinaryHeapStrategy, HashMapStrategy, LazyHeap, OrxStrategy, StrategyWeight},
    },
};
use radguy_ccs::systems::bool::extension::BoolExtension;
use radguy_ccs::systems::ccs::{
    bisimulation_system::BisimulationSystem, grammar::ProgramParser,
    transition_system::TransitionSystem, weak_transition_system::WeakTransitionSystem,
};
use slotmap::DefaultKey;

macro_rules! bisim_bench_oracles_ordered {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $left:expr, $right:expr => $eq:literal in $ccs:expr, with $($oracle:expr,)*) => {{
        let parser = ProgramParser::new();
        let ast = parser.parse($ccs).expect("Program should parse");
        let mut group = $c.benchmark_group(stringify!($name));
        $(
        {
            let oracle = $oracle;
            group.bench_with_input(BenchmarkId::new("ordered", format!("{}/{}", $sname, &oracle)), &oracle, |b, o| {
                b.iter_batched(
                    || {
                        let mut lts = WeakTransitionSystem::<DefaultKey>::default();
                        lts.load_ast(ast.clone());
                        (BisimulationSystem::<DefaultKey, DefaultKey, DefaultKey, _>::new(lts), (*o).clone())
                    },
                    |(mut sys, o)| {
                        let target = sys.specify_comparison($left, $right);
                        let result = !ordered::kleene_local::<_, _, $s, $s, _>(&mut sys, target, &o);
                        assert_eq!(
                            $eq,
                            result,
                            "{} and {} should{} be bisimilar in{}",
                            $left,
                            $right,
                            if !$eq { " not" } else { "" },
                            $ccs
                        )
                    },
                    criterion::BatchSize::SmallInput,
                );
            });
        }
        )*
    }};
    ($name:ident: using $c:expr, strategies $($s:ty),+; bench $left:expr, $right:expr => $eq:literal in $ccs:expr, with $($oracle:expr,)*) => {
        $(
            bisim_bench_oracles_ordered(using $c, strategy $s; bench $left, $right => $eq in $css, with $($oracle,)*);
        )+
    }
}

macro_rules! bisim_bench_oracles_unordered {
    ($name:ident: using $c:expr, bench $left:expr, $right:expr => $eq:literal in $ccs:expr, with $($oracle:expr,)*) => {{
        let parser = ProgramParser::new();
        let ast = parser.parse($ccs).expect("Program should parse");
        let mut group = $c.benchmark_group(stringify!($name));
        $(
        {
            let oracle = $oracle;
            group.bench_with_input(BenchmarkId::new("unordered", &oracle), &oracle, |b, o| {
                b.iter_batched(
                    || {
                        let mut lts = WeakTransitionSystem::<DefaultKey>::default();
                        lts.load_ast(ast.clone());
                        (BisimulationSystem::<DefaultKey, DefaultKey, DefaultKey, _>::new(lts), (*o).clone())
                    },
                    |(mut sys, o)| {
                        let target = sys.specify_comparison($left, $right);
                        let result = !kleene_local(&mut sys, target, &o);
                        assert_eq!(
                            $eq,
                            result,
                            "{} and {} should{} be bisimilar in{}",
                            $left,
                            $right,
                            if !$eq { " not" } else { "" },
                            $ccs
                        )
                    },
                    criterion::BatchSize::SmallInput,
                );
            });
        }
        )*
    }};
}
macro_rules! bisim_bench_problem_ordered {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; $left:expr, $right:expr => $eq:literal in $ccs:expr) => {
        let ccs = $ccs;

        bisim_bench_oracles_ordered! {
            $name: using $c, strategy $s; $sname; bench $left, $right => $eq in ccs, with
            SMax::default().constant(StrategyWeight::Infinity),
            SMax::default().constant(StrategyWeight::Num(1)).then(SiblingsOracle::default()),
            LocalMaxR::default().constant(StrategyWeight::Infinity),
            LocalMaxR::default().constant(StrategyWeight::Infinity).then(CountOracle::default()),
            LocalMaxR::default().constant(StrategyWeight::Infinity).then(InverseCountOracle::default()),
            BoolExtension::oracle().constant(StrategyWeight::Infinity),
            BoolExtension::oracle().constant(StrategyWeight::Infinity).and_by(InverseCountOracle::default(), std::cmp::min),
            BoolExtension::oracle().constant(StrategyWeight::Infinity).and_by(CountOracle::default(), std::cmp::min),
            BoolExtension::oracle().constant(StrategyWeight::Num(1)).then(SiblingsOracle::default()),
            StrategicArgumentsOracle::default(),
            StrategicArgumentsOracle::default().and_by(CountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().and_by(InverseCountOracle::default(), std::cmp::min),
            CountOracle::default().then(StrategicArgumentsOracle::default()),
            InverseCountOracle::default().then(StrategicArgumentsOracle::default()),
            StrategicArgumentsOracle::default().then(CountOracle::default()),
            StrategicArgumentsOracle::default().then(InverseCountOracle::default()),
            StrategicArgumentsOracle::default().and_by(SMax::default().constant(StrategyWeight::Infinity), std::cmp::min).then(CountOracle::default()),
            StrategicArgumentsOracle::default().and_by(SMax::default().constant(StrategyWeight::Infinity), std::cmp::min).then(InverseCountOracle::default()),
            StrategicArgumentsOracle::default().then(StrategicHeightOracle::simple()),
            StrategicArgumentsOracle::default().then(StrategicHeightOracle::transitive()),
            LocalMaxR::default().constant(StrategyWeight::Infinity).then(InverseCountOracle::default()).then(StrategicHeightOracle::simple()),
            LocalMaxR::default().constant(StrategyWeight::Infinity).then(InverseCountOracle::default()).then(StrategicHeightOracle::transitive()),
        };
    };
}

macro_rules! bisim_bench_problem {
    ($name:ident: using $c:expr, $left:expr, $right:expr => $eq:literal in $ccs:expr) => {
        let ccs = $ccs;
        bisim_bench_oracles_unordered! { $name: using $c, bench $left, $right => $eq in ccs, with
            SMax::default(),
            LocalMaxR::default(),
            ArgumentsOracle::default(),
            ArgumentsOracle::default().then(SMax::default()),
            ArgumentsOracle::default().then(LocalMaxR::default()),
            ArgumentsOracle::default().and(SMax::default()),
            ArgumentsOracle::default().and(LocalMaxR::default()),
            BoolExtension::oracle(),
            SMax::default().then(BoolExtension::oracle()),
            LocalMaxR::default().then(BoolExtension::oracle()),
        };
        bisim_bench_problem_ordered!($name: using $c, strategy BinaryHeapStrategy<_>; "std_binary"; $left, $right => $eq in $ccs);
        bisim_bench_problem_ordered!($name: using $c, strategy HashMapStrategy<_>; "hashmap"; $left, $right => $eq in $ccs);
        bisim_bench_problem_ordered!($name: using $c, strategy OrxStrategy<_, DaryHeapWithMap<_, _, 4>>; "orx_quad"; $left, $right => $eq in $ccs);
        bisim_bench_problem_ordered!($name: using $c, strategy LazyHeap<_, BinaryHeapStrategy<_>>; "std_binary_lazy"; $left, $right => $eq in $ccs);
        bisim_bench_problem_ordered!($name: using $c, strategy LazyHeap<_, OrxStrategy<_, DaryHeapWithMap<_, _, 4>>>; "orx_quad_lazy"; $left, $right => $eq in $ccs);
    };
}

macro_rules! bisim_bench_suite {
    ($($name:ident: $left:expr, $right:expr => $eq:literal in $ccs:expr;)*) => {
        $(
        fn $name(c: &mut Criterion) {
            bisim_bench_problem!($name: using c, $left, $right => $eq in $ccs);
        }
        )*
        criterion_group!(
            name = benches;
            config = Criterion::default(); //.sample_size(20);
            targets = $($name),*
        );
    };
}

bisim_bench_suite! {
    abp_ok: "SPEC", "ABP" => true in include_str!("../systems/ccs/abp_ok.ccs");
    abpl_ok: "SPEC", "ABPl" => true in include_str!("../systems/ccs/abp_ok.ccs");
    abpl_ok_2: "SPEC", "ABPl_2" => true in include_str!("../systems/ccs/abp_ok.ccs");
    abpl_bad_2: "SPEC", "ABPl_2" => false in include_str!("../systems/ccs/abp_bad.ccs");
    // abpl_ok_3: "SPEC", "ABPl_3" => true in include_str!("../systems/ccs/abp_ok.ccs");
    // abpl_bad_3: "SPEC", "ABPl_3" => false in include_str!("../systems/ccs/abp_bad.ccs");
    // NOTE: these two actually *are* weakly bisimilar, so should not be used
    // abp_bad: "SPEC", "ABP" => false in include_str!("../systems/ccs/abp_bad.ccs");
    // abpl_bad: "SPEC", "ABPl" => false in include_str!("../systems/ccs/abp_bad.ccs");

    // TODO: Parameterize on size of leader election?
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

criterion_main!(benches);
