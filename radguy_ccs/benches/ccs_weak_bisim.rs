use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use orx_priority_queue::DaryHeapWithMap;
use radguy::{
    kleene_local,
    oracle::{ArgumentsOracle, IdentityOracle, LocalMaxR, LocalOracle, SMax, TrivialOracle},
    ordered::{
        self,
        oracle::{
            ArgumentsStrategy, DependencyCountOracle, InverseDependencyCountOracle, SiblingsOracle,
            SiblingsOracleInv, StrategicArgumentsOracle, StrategicLocalOracle,
            StrategicNonStuckOracle, ToConstant, ToOrdered,
        },
        strategy::{BinaryHeapStrategy, LazyHeap, OrxStrategy, StrategyWeight},
    },
};
use radguy_ccs::systems::{
    bool::{extension::BoolExtension, strategic_extension::StrategicBoolExtension},
    ccs::{
        bisimulation_system::BisimulationSystem, grammar::ProgramParser,
        transition_system::TransitionSystem, weak_transition_system::WeakTransitionSystem,
    },
};
use std::{fs::OpenOptions, io::Write, path::Path};

const SKIPPED_PATH: &str = "bisim_skipped_benches.txt";

fn append_skipped(record: &str) {
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(Path::new(SKIPPED_PATH))
        .expect("File should be created before this function call");

    if let Err(e) = writeln!(file, "{record}") {
        panic!("Couldn't write to file: {e}");
    }
}

macro_rules! weak_bisim_system_ordered_composed_unordered {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $left:expr, $right:expr => $eq:literal in $ccs:expr, [$($strategic_oracle:expr),*]) => {
        $(
            bisim_bench_oracles_ordered! {
            $name: using $c, strategy $s; $sname; bench $left, $right => $eq in $ccs, with
                BoolExtension::bitset().as_oracle().ordered().then($strategic_oracle.clone()),
                SMax::bitset().then(BoolExtension::bitset().as_oracle()).ordered().then($strategic_oracle.clone()),
                LocalMaxR::bitset().then(BoolExtension::bitset().as_oracle()).ordered().then($strategic_oracle.clone()),
                ArgumentsOracle::bitset().and(SMax::bitset()).ordered().then($strategic_oracle.clone()),
                ArgumentsOracle::bitset().and(LocalMaxR::bitset()).ordered().then($strategic_oracle.clone()),
                SMax::bitset().ordered().then($strategic_oracle.clone()),
                LocalMaxR::bitset().ordered().then($strategic_oracle.clone()),
                ArgumentsOracle::bitset().ordered().then($strategic_oracle.clone()),
                ArgumentsOracle::bitset().then(SMax::bitset()).ordered().then($strategic_oracle.clone()),
                ArgumentsOracle::bitset().then(LocalMaxR::bitset()).ordered().then($strategic_oracle.clone()),
            }
        )*
    }
}

macro_rules! weak_bisim_system_ordered_composed_unordered_const_1 {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $left:expr, $right:expr => $eq:literal in $ccs:expr, [$($strategic_oracle:expr),*]) => {
        $(
            bisim_bench_oracles_ordered! {
            $name: using $c, strategy $s; $sname; bench $left, $right => $eq in $ccs, with
                // BoolExtension::bitset().as_oracle().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                // SMax::bitset().then(BoolExtension::bitset().as_oracle()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                // LocalMaxR::bitset().then(BoolExtension::bitset().as_oracle()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                // ArgumentsOracle::bitset().and(SMax::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                // ArgumentsOracle::bitset().and(LocalMaxR::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                SMax::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                LocalMaxR::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                // ArgumentsOracle::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                // ArgumentsOracle::bitset().then(SMax::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                // ArgumentsOracle::bitset().then(LocalMaxR::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
            }
        )*
    }
}

macro_rules! bisim_bench_oracles_ordered {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $left:expr, $right:expr => $eq:literal in $ccs:expr, with $($oracle:expr,)*) => {{
        let parser = ProgramParser::new();
        let ast = parser.parse($ccs).expect("Program should parse");
        let mut group = $c.benchmark_group(stringify!($name));
        $(
        {
            let oracle = $oracle;
            let mut skipped = false;
            group.bench_with_input(BenchmarkId::new("ordered", format!("{}/{}", $sname, &oracle)), &oracle, |b, o| {
                b.iter_batched(
                    || {
                        let mut lts = WeakTransitionSystem::<usize>::default();
                        lts.load_ast(ast.clone());
                        (BisimulationSystem::<usize, usize, usize, _>::new(lts), (*o).clone())
                    },
                    |(mut sys, o)| {
                        if skipped {
                            return;
                        }
                        let target = sys.specify_comparison($left, $right);
                        let Some((result, _)) = ordered::kleene_local::<_, _, $s, $s, _>(&mut sys, target, &o) else {
                            skipped = true;
                            append_skipped(&format!("{}/ordered/{}/{}", stringify!($name), $sname, &o));
                            return;
                        };
                        assert_eq!(
                            $eq,
                            !result,
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
        let name = stringify!($name);
        let mut group = $c.benchmark_group(name);
        $(
        {
            let mut skipped = false;
            let oracle = $oracle;
            group.bench_with_input(BenchmarkId::new("unordered", &oracle), &oracle, |b, o| {
                b.iter_batched(
                    || {
                        let mut lts = WeakTransitionSystem::<usize>::default();
                        lts.load_ast(ast.clone());
                        (BisimulationSystem::<usize, usize, usize, _>::new(lts), (*o).clone())
                    },
                    |(mut sys, o)| {
                        if skipped {
                            return;
                        }
                        let target = sys.specify_comparison($left, $right);
                        let Some((result, _)) = kleene_local(&mut sys, target, &o) else {
                            skipped = true;
                            append_skipped(&format!("{}/unordered/{}", stringify!($name), &o));
                            return;
                        };
                        assert_eq!(
                            $eq,
                            !result,
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
                IdentityOracle::bitset().ordered(),
                // TrivialOracle::bitset().ordered(),

                SMax::bitset().ordered(),
                // SMax::bitset().constant(StrategyWeight::Infinity),
                // StrategicArgumentsOracle::default(),
                // StrategicArgumentsOracle::default().and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
                // StrategicArgumentsOracle::default().and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
                // StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min),
                StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
                StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(SMax::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
                // StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
                // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()),
                // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
                // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
                // StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()),
                // StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
                // StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
                StrategicArgumentsOracle::default().then(BoolExtension::bitset().as_oracle().ordered()),
                // StrategicArgumentsOracle::default().then(BoolExtension::bitset().as_oracle().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
                // StrategicArgumentsOracle::default().then(BoolExtension::bitset().as_oracle().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
                // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min),
                // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min),
                // ArgumentsOracle::bitset().ordered().then(DependencyCountOracle::default()),
                // ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()),
                // DependencyCountOracle::default().and_by(BoolExtension::bitset().as_oracle().ordered(), std::cmp::min),
                // InverseDependencyCountOracle::default().and_by(BoolExtension::bitset().as_oracle().ordered(), std::cmp::min),
                // StrategicArgumentsOracle::default().then(StrategicBoolExtension::bitset().as_oracle()),
        };
        weak_bisim_system_ordered_composed_unordered!(
            $name: using $c, strategy $s; $sname; bench $left, $right => $eq in $ccs,
            [
                // DependencyCountOracle::default(),
                // InverseDependencyCountOracle::default(),
                // StrategicNonStuckOracle::bitset(),
                // StrategicArgumentsOracle::default().then(StrategicBoolExtension::bitset().as_oracle()),
                // DependencyCountOracle::default().then(StrategicBoolExtension::bitset().as_oracle())
            ]
        );
        weak_bisim_system_ordered_composed_unordered_const_1!(
            $name: using $c, strategy $s; $sname; bench $left, $right => $eq in $ccs,
            [
                // SiblingsOracle,
                // SiblingsOracleInv,
                // StrategicBoolExtension::bitset().as_oracle()
            ]
        );
    };
}

macro_rules! bisim_bench_suite {
    ($($name:ident: $left:expr, $right:expr => $eq:literal in $ccs:expr;)*) => {
        $(
        fn $name(c: &mut Criterion) {
            // bisim_bench_oracles_unordered! {
            //     $name: using c, bench $left, $right => $eq in $ccs, with
            //     IdentityOracle::bitset(),
            //     // TrivialOracle::bitset(),
            //     // BoolExtension::bitset().as_oracle(),
            //     SMax::bitset().then(BoolExtension::bitset().as_oracle()),
            //     LocalMaxR::bitset().then(BoolExtension::bitset().as_oracle()),
            //     // ArgumentsOracle::bitset().and(SMax::bitset()),
            //     // ArgumentsOracle::bitset().and(LocalMaxR::bitset()),
            //     SMax::bitset(),
            //     LocalMaxR::bitset(),
            //     // ArgumentsOracle::bitset(),
            //     // ArgumentsOracle::bitset().then(SMax::bitset()),
            //     // ArgumentsOracle::bitset().then(LocalMaxR::bitset()),
            // }
            bisim_bench_problem_ordered!($name: using c, strategy BinaryHeapStrategy<_>; "std_binary"; $left, $right => $eq in $ccs);
            // bisim_bench_problem_ordered!($name: using c, strategy OrxStrategy<_, DaryHeapWithMap<_, _, 4>>; "orx_quad"; $left, $right => $eq in $ccs);
            // bisim_bench_problem_ordered!($name: using c, strategy LazyHeap<_, BinaryHeapStrategy<_>>; "std_binary_lazy"; $left, $right => $eq in $ccs);
            // bisim_bench_problem_ordered!($name: using c, strategy LazyHeap<_, OrxStrategy<_, DaryHeapWithMap<_, _, 4>>>; "orx_quad_lazy"; $left, $right => $eq in $ccs);
        }
        )*
        criterion_group!(
            name = benches;
            config = Criterion::default().sample_size(20).measurement_time(std::time::Duration::from_secs(10));
            targets = $($name),*
        );
    };
}

bisim_bench_suite! {
    // NOTE: these two actually *are* weakly bisimilar, so should not be used
    // abp_bad: "SPEC", "ABP" => false in include_str!("../systems/ccs/abp_bad.ccs");
    // abpl_bad: "SPEC", "ABPl" => false in include_str!("../systems/ccs/abp_bad.ccs");
    // abp_ok: "SPEC", "ABP" => true in include_str!("../systems/ccs/abp_ok.ccs");
    // abpl_ok: "SPEC", "ABPl" => true in include_str!("../systems/ccs/abp_ok.ccs");
    // abpl_ok_2: "SPEC", "ABPl_2" => true in include_str!("../systems/ccs/abp_ok.ccs");
    // abpl_bad_2: "SPEC", "ABPl_2" => false in include_str!("../systems/ccs/abp_bad.ccs");
    // abpl_ok_3: "SPEC", "ABPl_3" => true in include_str!("../systems/ccs/abp_ok.ccs");
    abpl_bad_3: "SPEC", "ABPl_3" => false in include_str!("../systems/ccs/abp_bad.ccs");
    leader_election_bad_6: "Spec", "Ring" => false in include_str!("../systems/ccs/leader_election_bad_6.ccs");
    leader_election_ok_6: "Spec", "Ring" => true in include_str!("../systems/ccs/leader_election_ok_6.ccs");
    leader_election_bad_7: "Spec", "Ring" => false in include_str!("../systems/ccs/leader_election_bad_7.ccs");
    leader_election_ok_7: "Spec", "Ring" => true in include_str!("../systems/ccs/leader_election_ok_7.ccs");
    leader_election_bad_8: "Spec", "Ring" => false in include_str!("../systems/ccs/leader_election_bad_8.ccs");
    leader_election_ok_8: "Spec", "Ring" => true in include_str!("../systems/ccs/leader_election_ok_8.ccs");

    dekker_mutual_exclusion: "Dekker-2", "Spec" => true in include_str!("../systems/ccs/dekkers_mutual_exclusion.ccs");
}

criterion_main!(benches);
